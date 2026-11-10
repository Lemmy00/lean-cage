(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: Fresh endpoint creation starts at the actual native pair call. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewaySpawnABI GatewayReadonly GatewayCallPath
  GatewayContexts GatewayOperations GatewayFrames GatewayReturns.
Import ListNotations.
Open Scope Z_scope.

Definition pair_parameters pointer:=PTree.set _pair pointer(create_undef_temps(fn_temps f_host_private_pair)).
Definition pair_first:=match fn_body f_host_private_pair with Ssequence first _=>first|_=>Sskip end.
Definition pair_after_first:=match fn_body f_host_private_pair with Ssequence _ after=>after|_=>Sskip end.
Definition pair_socket_call:=match pair_first with Ssequence call _=>call|_=>Sskip end.
Definition pair_socket_guard:=match pair_first with Ssequence _ guard=>guard|_=>Sskip end.
Definition pair_socket_cont pointer:=Kcall(Some _t'1)f_host_private_pair empty_env(pair_parameters pointer)
  (Kseq pair_socket_guard(Kseq pair_after_first Kstop)).
Definition pair_socket_arguments object offset:=
  [Vint Int.one;Vint(Int.repr 526337);Vint Int.zero;Vptr object offset].

Lemma pair_function_entry ge pointer memory:
  function_entry2 ge f_host_private_pair[pointer]memory empty_env(pair_parameters pointer)memory.
Proof.
  constructor;[constructor|repeat constructor;cbn;intuition discriminate| |constructor|reflexivity].
  unfold list_disjoint,var_names;cbn;intros first second LEFT RIGHT;
    repeat destruct LEFT as[LEFT|LEFT];try contradiction;subst first;
    repeat destruct RIGHT as[RIGHT|RIGHT];try contradiction;subst second;discriminate.
Qed.

Lemma pair_socket_failed_path ge object offset memory:
  gateway_constant_path ge(Vint(Int.neg Int.one))
    (Returnstate(Vint(Int.neg Int.one))(pair_socket_cont(Vptr object offset))memory).
Proof.
  eapply gateway_constant_next with(next:=State f_host_private_pair Sskip
    (Kseq pair_socket_guard(Kseq pair_after_first Kstop))empty_env
    (PTree.set _t'1(Vint(Int.neg Int.one))(pair_parameters(Vptr object offset)))memory);
    [cbn;tauto|intro available;apply unchanged_store_edge,edge_returnstate|].
  eapply gateway_constant_next with(next:=State f_host_private_pair pair_socket_guard(Kseq pair_after_first Kstop)
    empty_env(PTree.set _t'1(Vint(Int.neg Int.one))(pair_parameters(Vptr object offset)))memory);
    [cbn;tauto|intro available;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_constant_next with(next:=State f_host_private_pair
    (Sreturn(Some(Eunop Oneg(Econst_int Int.one tint)tint)))(Kseq pair_after_first Kstop)
    empty_env(PTree.set _t'1(Vint(Int.neg Int.one))(pair_parameters(Vptr object offset)))memory).
  - cbn;tauto.
  - intro available;apply certified_if_edge with(v:=Vint(Int.neg Int.one))(b:=true);
      [apply old_expression_value,value_temp;apply PTree.gss|reflexivity].
  - eapply gateway_constant_at_return with(value:=Vint(Int.neg Int.one)).
    + reflexivity.
    + intro available;apply old_expression_value;eapply value_unary;[constructor|reflexivity].
    + intro available;reflexivity.
Qed.

Theorem actual_pair_socket_failed {World Event}(backend:gateway_backend World Event)ge object offset before world
    events returned after next:
  gateway_steps backend ge
    (gateway_live(Returnstate(Vint(Int.neg Int.one))(pair_socket_cont(Vptr object offset))before)world)events
    (gateway_live(Returnstate returned Kstop after)next)->returned=Vint(Int.neg Int.one).
Proof. intro RUN;eapply gateway_constant_path_actual;[apply pair_socket_failed_path|exact RUN]. Qed.

Lemma pair_socket_source_call(ge:Clight.genv)object offset memory symbol:
  Genv.find_symbol ge _socketpair=Some symbol->
  Genv.find_funct_ptr ge symbol=Some(gateway_spawn_signature gateway_socketpair_api)->
  store_edge ge
    (State f_host_private_pair pair_socket_call(Kseq pair_socket_guard(Kseq pair_after_first Kstop))empty_env
      (pair_parameters(Vptr object offset))memory)
    (Callstate(gateway_spawn_signature gateway_socketpair_api)(pair_socket_arguments object offset)
      (pair_socket_cont(Vptr object offset))memory).
Proof.
  intros SYMBOL FUNCTION;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
  - eapply cons_argument_values with(v:=Vint Int.one);[apply old_expression_value;constructor|reflexivity|].
    eapply cons_argument_values with(v:=Vint(Int.repr 526337)).
    + apply old_expression_value;eapply value_binary.
      * eapply value_binary;[constructor|constructor|reflexivity].
      * constructor.
      * reflexivity.
    + reflexivity.
    + eapply cons_argument_values with(v:=Vint Int.zero);[apply old_expression_value;constructor|reflexivity|].
      eapply cons_argument_values with(v:=Vptr object offset).
      * apply old_expression_value,value_temp;unfold pair_parameters;apply PTree.gss.
      * reflexivity.
      * apply no_argument_values.
  - cbn;exact FUNCTION.
  - reflexivity.
Qed.

Lemma pair_first_socket_path(ge:Clight.genv)object offset memory symbol:
  Genv.find_symbol ge _socketpair=Some symbol->
  Genv.find_funct_ptr ge symbol=Some(gateway_spawn_signature gateway_socketpair_api)->
  gateway_retained_call_path ge(gateway_spawn_signature gateway_socketpair_api)(pair_socket_arguments object offset)
    (pair_socket_cont(Vptr object offset))(Callstate(Internal f_host_private_pair)[Vptr object offset]Kstop memory).
Proof.
  intros SYMBOL FUNCTION.
  eapply gateway_retained_next with(next:=State f_host_private_pair(fn_body f_host_private_pair)Kstop
    empty_env(pair_parameters(Vptr object offset))memory);
    [cbn;tauto|intro available;apply function_entry_source_edge,pair_function_entry|].
  eapply gateway_retained_next with(next:=State f_host_private_pair pair_first(Kseq pair_after_first Kstop)
    empty_env(pair_parameters(Vptr object offset))memory);
    [cbn;tauto|intro available;apply unchanged_store_edge,edge_seq|].
  eapply gateway_retained_next with(next:=State f_host_private_pair pair_socket_call
    (Kseq pair_socket_guard(Kseq pair_after_first Kstop))empty_env(pair_parameters(Vptr object offset))memory);
    [cbn;tauto|intro available;apply unchanged_store_edge,edge_seq|].
  eapply gateway_retained_next with(next:=Callstate(gateway_spawn_signature gateway_socketpair_api)
    (pair_socket_arguments object offset)(pair_socket_cont(Vptr object offset))memory).
  - cbn;tauto.
  - intro available;eapply pair_socket_source_call;eassumption.
  - constructor.
Qed.

Theorem actual_pair_first_socket {World Event}(backend:gateway_backend World Event)
    (ready:mem->World->Prop)(ambient:gateway_runtime_discipline backend ready)
    object offset before world events returned after next:
  ready before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_private_pair)[Vptr object offset]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next)->
  exists prefix suffix called call_world,
    events=prefix++suffix /\Forall gateway_quiet_event prefix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(Internal f_host_private_pair)[Vptr object offset]Kstop before)world)prefix
      (gateway_live(Callstate(gateway_spawn_signature gateway_socketpair_api)(pair_socket_arguments object offset)
        (pair_socket_cont(Vptr object offset))called)call_world) /\ready called call_world /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(gateway_spawn_signature gateway_socketpair_api)(pair_socket_arguments object offset)
        (pair_socket_cont(Vptr object offset))called)call_world)suffix
      (gateway_live(Returnstate returned Kstop after)next).
Proof.
  intros READY RUN.
  destruct(actual_gateway_spawn_binding gateway_socketpair_api)as[symbol[SYMBOL FUNCTION]].
  exact(gateway_retained_call_ready_cut backend(Clight.globalenv prog)ready ambient
    (gateway_spawn_signature gateway_socketpair_api)(pair_socket_arguments object offset)(pair_socket_cont(Vptr object offset))
    (Callstate(Internal f_host_private_pair)[Vptr object offset]Kstop before)world events returned after next
    (pair_first_socket_path _ object offset before symbol SYMBOL FUNCTION)READY RUN).
Qed.
