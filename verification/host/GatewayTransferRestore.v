(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: The caller retains its saved thread token and captures errno
   before restoring. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs
  Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayCallPath GatewayRuntimeCuts GatewayInstructions
  GatewayTransferSource GatewayTransferChunk GatewayTransferReceive GatewayTransferErrno GatewayRuntimeABI
  GatewayOperations GatewayCalls GatewayReadonly.
Import ListNotations.

Definition transfer_errno_values temporaries amount saved descriptor count pointer:=
  PTree.set _t'8 pointer(transfer_count_values temporaries amount saved descriptor count).
Definition transfer_number_values temporaries amount saved descriptor count pointer number:=
  PTree.set _number number(transfer_errno_values temporaries amount saved descriptor count pointer).
Definition transfer_restore_cont temporaries amount saved descriptor count pointer number:=
  Kcall None f_host_transfer empty_env(transfer_number_values temporaries amount saved descriptor count pointer number)
    (Kseq transfer_after_restore transfer_iteration_cont).

Lemma actual_transfer_restore_call (ge:Clight.genv)temporaries amount saved descriptor count pointer number memory symbol :
  (exists block offset,saved=Vptr block offset) ->
  Genv.find_symbol ge _PyEval_RestoreThread=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some gateway_restore_thread_definition ->
  store_edge ge(State f_host_transfer transfer_restore_call(Kseq transfer_after_restore transfer_iteration_cont)empty_env
    (transfer_number_values temporaries amount saved descriptor count pointer number)memory)
    (Callstate gateway_restore_thread_definition[saved]
      (transfer_restore_cont temporaries amount saved descriptor count pointer number)memory).
Proof.
  intros[block[offset SAME]]SYMBOL FUNCTION;subst saved.
  eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
  - eapply cons_argument_values with(v:=Vptr block offset).
    + apply old_expression_value,value_temp.
      unfold transfer_number_values,transfer_errno_values,transfer_count_values,transfer_cast_count_values,
        transfer_received_values,transfer_receive_values,transfer_saved_values.
      rewrite !PTree.gso by discriminate;apply PTree.gss.
    + reflexivity.
    + apply no_argument_values.
  - cbn;exact FUNCTION.
  - reflexivity.
Qed.

Theorem actual_transfer_captures_errno {World Event}(backend:gateway_backend World Event)ge
    temporaries amount saved descriptor count pointer before world events returned after next
    (ready:mem->World->Prop)(discipline:gateway_runtime_discipline backend ready) :
  ready before world ->
  gateway_steps backend ge
    (gateway_live(Returnstate pointer(transfer_errno_cont temporaries amount saved descriptor count)before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->
  exists prefix suffix memory captured_world number,
    events=prefix++gateway_source E0::suffix /\Forall gateway_quiet_event prefix /\
    gateway_steps backend ge
      (gateway_live(Returnstate pointer(transfer_errno_cont temporaries amount saved descriptor count)before)world)prefix
      (gateway_live(State f_host_transfer transfer_errno_bind(Kseq transfer_after_errno transfer_iteration_cont)empty_env
        (transfer_errno_values temporaries amount saved descriptor count pointer)memory)captured_world) /\
    eval_expr ge empty_env(transfer_errno_values temporaries amount saved descriptor count pointer)memory
      (Ederef(Etempvar _t'8(tptr tint))tint)number /\ready memory captured_world /\
    gateway_steps backend ge
      (gateway_live(State f_host_transfer Sskip(Kseq transfer_after_errno transfer_iteration_cont)empty_env
        (transfer_number_values temporaries amount saved descriptor count pointer number)memory)captured_world)suffix
      (gateway_live(Returnstate returned Kstop after)next).
Proof.
  intros READY RUN.
  destruct(gateway_uniform_edge_side_cut backend ge ready discipline
    (Returnstate pointer(transfer_errno_cont temporaries amount saved descriptor count)before)
    (State f_host_transfer Sskip(Kseq transfer_errno_bind(Kseq transfer_after_errno transfer_iteration_cont))empty_env
      (transfer_errno_values temporaries amount saved descriptor count pointer)before)
    before world events returned after next ltac:(cbn;tauto)
    ltac:(intro memory;apply unchanged_store_edge,edge_returnstate)READY RUN)
    as[prefix1[suffix1[memory1[world1[EVENTS1[AMBIENT1[PREFIX1[READY1 REST1]]]]]]]].
  cbn[GatewayMachine.gateway_replace_memory]in PREFIX1,REST1.
  destruct(gateway_uniform_edge_side_cut backend ge ready discipline
    (State f_host_transfer Sskip(Kseq transfer_errno_bind(Kseq transfer_after_errno transfer_iteration_cont))empty_env
      (transfer_errno_values temporaries amount saved descriptor count pointer)memory1)
    (State f_host_transfer transfer_errno_bind(Kseq transfer_after_errno transfer_iteration_cont)empty_env
      (transfer_errno_values temporaries amount saved descriptor count pointer)memory1)
    memory1 world1 suffix1 returned after next ltac:(cbn;tauto)
    ltac:(intro memory;apply unchanged_store_edge,edge_skip_seq)READY1 REST1)
    as[prefix2[suffix2[memory2[world2[EVENTS2[AMBIENT2[PREFIX2[READY2 REST2]]]]]]]].
  cbn[GatewayMachine.gateway_replace_memory]in PREFIX2,REST2.
  destruct(gateway_set_result_cut backend ge f_host_transfer _number
    (Ederef(Etempvar _t'8(tptr tint))tint)(Kseq transfer_after_errno transfer_iteration_cont)empty_env
    (transfer_errno_values temporaries amount saved descriptor count pointer)memory2 world2 suffix2 returned after next REST2)
    as[prefix3[suffix3[memory3[world3[number[EVENTS3[AMBIENT3[PREFIX3[VALUE REST3]]]]]]]]].
  assert(READY3:ready memory3 world3).
  { eapply gateway_ambient_run_ready with(backend:=backend)(ge:=ge)(ready:=ready)
      (source:=State f_host_transfer transfer_errno_bind(Kseq transfer_after_errno transfer_iteration_cont)empty_env
        (transfer_errno_values temporaries amount saved descriptor count pointer)memory2)
      (before:=memory2)(world:=world2)(events:=prefix3)(after:=memory3)(next:=world3);
      [exact discipline|exact READY2|exact AMBIENT3|exact PREFIX3]. }
  exists(prefix1++gateway_source E0::prefix2++gateway_source E0::prefix3),suffix3,memory3,world3,number.
  split.
  - rewrite EVENTS1,EVENTS2,EVENTS3.
    repeat rewrite <-app_assoc;cbn[app];repeat rewrite <-app_assoc;cbn[app];reflexivity.
  - split.
    + apply Forall_app;split.
      * eapply Forall_impl;[|exact AMBIENT1];intros event SAME;right;exact SAME.
      * constructor;[left;reflexivity|]. apply Forall_app;split.
        -- eapply Forall_impl;[|exact AMBIENT2];intros event SAME;right;exact SAME.
        -- constructor;[left;reflexivity|].
           eapply Forall_impl;[|exact AMBIENT3];intros event SAME;right;exact SAME.
    + split.
      * eapply gateway_steps_append;[exact PREFIX1|].
        econstructor;[apply gateway_internal;[exact I|constructor]|].
        eapply gateway_steps_append;[exact PREFIX2|].
        econstructor;[apply gateway_internal;[exact I|constructor]|exact PREFIX3].
      * split;[exact VALUE|]. split;[exact READY3|exact REST3].
Qed.

Local Ltac restore_retain target:=
  eapply gateway_retained_next with(next:=target);[cbn;tauto|intro another|].

Lemma actual_captured_number_restore_path (ge:Clight.genv)temporaries amount saved descriptor count pointer number memory symbol :
  (exists block offset,saved=Vptr block offset) ->
  Genv.find_symbol ge _PyEval_RestoreThread=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some gateway_restore_thread_definition ->
  gateway_retained_call_path ge gateway_restore_thread_definition[saved]
    (transfer_restore_cont temporaries amount saved descriptor count pointer number)
    (State f_host_transfer Sskip(Kseq transfer_after_errno transfer_iteration_cont)empty_env
      (transfer_number_values temporaries amount saved descriptor count pointer number)memory).
Proof.
  intros SAVED SYMBOL FUNCTION.
  restore_retain(State f_host_transfer transfer_after_errno transfer_iteration_cont empty_env
    (transfer_number_values temporaries amount saved descriptor count pointer number)memory).
  { apply unchanged_store_edge,edge_skip_seq. }
  restore_retain(State f_host_transfer transfer_restore_call(Kseq transfer_after_restore transfer_iteration_cont)empty_env
    (transfer_number_values temporaries amount saved descriptor count pointer number)memory).
  { apply unchanged_store_edge,edge_seq. }
  restore_retain(Callstate gateway_restore_thread_definition[saved]
    (transfer_restore_cont temporaries amount saved descriptor count pointer number)memory).
  { apply actual_transfer_restore_call with(symbol:=symbol);assumption. }
  constructor.
Qed.
