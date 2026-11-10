(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Real flag-return guards determine this caller's next SDK operation. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewaySpawnABI GatewayContexts GatewayFramedRuntime
  GatewayLaunchPaths GatewayExchangeSetup GatewayExchangeErrors GatewayExchangeFlagSource GatewayExchangeLoads
  GatewayPairContext GatewayPairMemory.
Import ListNotations.
Open Scope Z_scope.

Definition exchange_flags_decision:=match exchange_flags_guard with Ssequence first _=>first|_=>Sskip end.
Definition exchange_flags_error:=match exchange_flags_guard with Ssequence _ error=>error|_=>Sskip end.
Definition exchange_set_flags_body:=match exchange_flags_decision with Sifthenelse _ _ body=>body|_=>Sskip end.
Definition exchange_set_flags_prefix:=match exchange_set_flags_body with Ssequence prefix _=>prefix|_=>Sskip end.
Definition exchange_set_flags_bind:=match exchange_set_flags_body with Ssequence _ bind=>bind|_=>Sskip end.
Definition exchange_set_flags_load:=match exchange_set_flags_prefix with Ssequence load _=>load|_=>Sskip end.
Definition exchange_set_flags_call:=match exchange_set_flags_prefix with Ssequence _ call=>call|_=>Sskip end.
Definition exchange_set_flags_cont environment temporaries:=
  Kcall(Some _t'13)f_host_exchange environment temporaries
    (Kseq exchange_set_flags_bind(Kseq exchange_flags_error(Kseq(exchange_setup_after 6)Kstop))).
Definition exchange_got_flags flags temporaries:=PTree.set _flags(Vint flags)(PTree.set _t'8(Vint flags)temporaries).
Definition exchange_set_flags_temps flags right temporaries:=PTree.set _t'98(Vint(Int.repr right))(exchange_got_flags flags temporaries).

Lemma actual_exchange_flags_comparison(ge:Clight.genv)environment temporaries memory flags:
  temporaries!_flags=Some(Vint flags)->
  expression_value ge environment temporaries memory
    (Ebinop Olt(Etempvar _flags tint)(Econst_int Int.zero tint)tint)
    (Vint(if zlt(Int.signed flags)0 then Int.one else Int.zero)).
Proof.
  intro FLAGS;apply old_expression_value;eapply value_binary;[apply value_temp;exact FLAGS|constructor|].
  change(Some(Val.of_bool(Int.lt flags Int.zero))=Some(Vint(if zlt(Int.signed flags)0 then Int.one else Int.zero))).
  unfold Int.lt;rewrite Int.signed_zero;destruct(zlt(Int.signed flags)0);reflexivity.
Qed.

Lemma actual_exchange_set_flags_call(ge:Clight.genv)environment temporaries memory flags right symbol:
  temporaries!_t'98=Some(Vint(Int.repr right))->temporaries!_flags=Some(Vint flags)->environment!_leancage_host_fcntl=None->
  Genv.find_symbol ge _leancage_host_fcntl=Some symbol->
  Genv.find_funct_ptr ge symbol=Some(gateway_spawn_signature gateway_fcntl_api)->
  store_edge ge(State f_host_exchange exchange_set_flags_call
    (Kseq exchange_set_flags_bind(Kseq exchange_flags_error(Kseq(exchange_setup_after 6)Kstop)))environment temporaries memory)
    (Callstate(gateway_spawn_signature gateway_fcntl_api)
      [Vint(Int.repr right);Vint(Int.repr 4);Vint(Int.and flags(Int.not(Int.repr 2048)))]
      (exchange_set_flags_cont environment temporaries)memory).
Proof.
  intros FD FLAGS UNSHADOWED SYMBOL FUNCTION;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value;eapply value_function;[exact UNSHADOWED|exact SYMBOL|reflexivity].
  - eapply cons_argument_values with(v:=Vint(Int.repr right));[apply old_expression_value,value_temp;exact FD|reflexivity|].
    eapply cons_argument_values with(v:=Vint(Int.repr 4));[apply old_expression_value;constructor|reflexivity|].
    eapply cons_argument_values with(v:=Vint(Int.and flags(Int.not(Int.repr 2048)))).
    + apply old_expression_value;eapply value_binary with(v:=Vint flags)(w:=Vint(Int.not(Int.repr 2048)));
        [apply value_temp;exact FLAGS| |reflexivity].
      eapply value_unary;[constructor|reflexivity].
    + reflexivity.
    + apply no_argument_values.
  - cbn;exact FUNCTION.
  - reflexivity.
Qed.

Section AfterGet.
Context {World Event}(backend:gateway_backend World Event)(target:Clight.state->World->Prop)(property:mem->World->Prop).
Hypothesis CLOSED:gateway_ambient_closed backend property.
Variables(allocation_before allocated:mem)(environment:env)(temporaries:temp_env)(memory:mem)(object:block)(left right:Z)(flags:int).
Hypotheses(ALLOC:alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated)
  (ARRAY:environment!_pair=Some(object,tarray tint 2))
  (CELLS:forall before world,property before world->gateway_pair_cells before object Ptrofs.zero left right).
Hypothesis SUCCESS:0<=Int.signed flags->gateway_launch_path backend target property
  (Callstate(gateway_spawn_signature gateway_fcntl_api)
    [Vint(Int.repr right);Vint(Int.repr 4);Vint(Int.and flags(Int.not(Int.repr 2048)))]
    (exchange_set_flags_cont environment(exchange_set_flags_temps flags right temporaries))memory).

Theorem actual_exchange_after_get_script:
  gateway_launch_path backend target property(Returnstate(Vint flags)(exchange_get_flags_cont environment temporaries)memory).
Proof.
  set(returned:=PTree.set _t'8(Vint flags)temporaries).
  set(got:=exchange_got_flags flags temporaries).
  eapply gateway_launch_same with(following:=State f_host_exchange Sskip
    (Kseq exchange_get_flags_bind(Kseq(exchange_setup_after 5)Kstop))environment returned memory);
    [exact CLOSED|cbn;tauto|exact I|intros;apply unchanged_store_edge,edge_returnstate|].
  eapply gateway_launch_same with(following:=State f_host_exchange exchange_get_flags_bind
    (Kseq(exchange_setup_after 5)Kstop)environment returned memory);
    [exact CLOSED|cbn;tauto|exact I|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_launch_same with(following:=State f_host_exchange Sskip(Kseq(exchange_setup_after 5)Kstop)environment got memory);
    [exact CLOSED|cbn;tauto|exact I|intros;apply certified_set_edge,old_expression_value,value_temp;apply PTree.gss|].
  eapply gateway_launch_same with(following:=State f_host_exchange(exchange_setup_after 5)Kstop environment got memory);
    [exact CLOSED|cbn;tauto|exact I|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_launch_same with(following:=State f_host_exchange exchange_flags_guard(Kseq(exchange_setup_after 6)Kstop)
    environment got memory);
    [exact CLOSED|cbn;tauto|exact I|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_launch_same with(following:=State f_host_exchange exchange_flags_decision
    (Kseq exchange_flags_error(Kseq(exchange_setup_after 6)Kstop))environment got memory);
    [exact CLOSED|cbn;tauto|exact I|intros;apply unchanged_store_edge,edge_seq|].
  destruct(zlt(Int.signed flags)0)as[NEGATIVE|NONNEGATIVE].
  - eapply gateway_launch_same with(following:=State f_host_exchange(Sset _t'12(Econst_int Int.one tint))
      (Kseq exchange_flags_error(Kseq(exchange_setup_after 6)Kstop))environment got memory);
      [exact CLOSED|cbn;tauto|exact I| |].
    { intros before world READY;apply certified_if_edge with(v:=Vint Int.one)(b:=true);[|reflexivity].
      pose proof(actual_exchange_flags_comparison(Clight.globalenv prog)environment got before flags(PTree.gss _ _ _))as VALUE.
      destruct(zlt(Int.signed flags)0);[exact VALUE|lia]. }
    set(failed:=PTree.set _t'12(Vint Int.one)got).
    eapply gateway_launch_same with(following:=State f_host_exchange Sskip
      (Kseq exchange_flags_error(Kseq(exchange_setup_after 6)Kstop))environment failed memory);
      [exact CLOSED|cbn;tauto|exact I|intros;apply certified_set_edge,old_expression_value;constructor|].
    eapply gateway_launch_same with(following:=State f_host_exchange exchange_flags_error
      (Kseq(exchange_setup_after 6)Kstop)environment failed memory);
      [exact CLOSED|cbn;tauto|exact I|intros;apply unchanged_store_edge,edge_skip_seq|].
    eapply gateway_launch_same with(following:=State f_host_exchange(exchange_guard_failure exchange_flags_guard)
      (Kseq(exchange_setup_after 6)Kstop)environment failed memory);
      [exact CLOSED|cbn;tauto|exact I| |].
    { intros before world READY;apply certified_if_edge with(v:=Vint Int.one)(b:=true);
        [apply old_expression_value,value_temp;apply PTree.gss|reflexivity]. }
    eapply gateway_launch_failure with(allowed:=exchange_error_allowed).
    + exact(actual_exchange_error_bindings allocation_before environment allocated ALLOC).
    + apply((proj1(Forall_forall _ _))actual_exchange_errors_return).
      change(In(exchange_guard_failure exchange_flags_guard)exchange_early_errors).
      unfold exchange_early_errors;apply in_map;cbn;auto.
    + reflexivity.
  - eapply gateway_launch_same with(following:=State f_host_exchange exchange_set_flags_body
      (Kseq exchange_flags_error(Kseq(exchange_setup_after 6)Kstop))environment got memory);
      [exact CLOSED|cbn;tauto|exact I| |].
    { intros before world READY;apply certified_if_edge with(v:=Vint Int.zero)(b:=false);[|reflexivity].
      pose proof(actual_exchange_flags_comparison(Clight.globalenv prog)environment got before flags(PTree.gss _ _ _))as VALUE.
      destruct(zlt(Int.signed flags)0);[lia|exact VALUE]. }
    eapply gateway_launch_same with(following:=State f_host_exchange exchange_set_flags_prefix
      (Kseq exchange_set_flags_bind(Kseq exchange_flags_error(Kseq(exchange_setup_after 6)Kstop)))environment got memory);
      [exact CLOSED|cbn;tauto|exact I|intros;apply unchanged_store_edge,edge_seq|].
    eapply gateway_launch_same with(following:=State f_host_exchange exchange_set_flags_load
      (Kseq exchange_set_flags_call(Kseq exchange_set_flags_bind(Kseq exchange_flags_error(Kseq(exchange_setup_after 6)Kstop))))
      environment got memory);
      [exact CLOSED|cbn;tauto|exact I|intros;apply unchanged_store_edge,edge_seq|].
    set(loaded:=exchange_set_flags_temps flags right temporaries).
    eapply gateway_launch_same with(following:=State f_host_exchange Sskip
      (Kseq exchange_set_flags_call(Kseq exchange_set_flags_bind(Kseq exchange_flags_error(Kseq(exchange_setup_after 6)Kstop))))
      environment loaded memory);
      [exact CLOSED|cbn;tauto|exact I| |].
    { intros before world READY;apply certified_set_edge.
      change(expression_value(Clight.globalenv prog)environment got before
        (Ederef(exchange_endpoint_element _pair 1)tint)(Vint(Int.repr right))).
      exact(actual_exchange_endpoint_load _ environment got before _pair object left right 1 ARRAY(CELLS before world READY)ltac:(lia)). }
    eapply gateway_launch_same with(following:=State f_host_exchange exchange_set_flags_call
      (Kseq exchange_set_flags_bind(Kseq exchange_flags_error(Kseq(exchange_setup_after 6)Kstop)))environment loaded memory);
      [exact CLOSED|cbn;tauto|exact I|intros;apply unchanged_store_edge,edge_skip_seq|].
    eapply gateway_launch_same with(following:=Callstate(gateway_spawn_signature gateway_fcntl_api)
      [Vint(Int.repr right);Vint(Int.repr 4);Vint(Int.and flags(Int.not(Int.repr 2048)))]
      (exchange_set_flags_cont environment loaded)memory);
      [exact CLOSED|cbn;tauto|exact I| |apply SUCCESS;lia].
    intros before world READY;destruct(actual_gateway_spawn_binding gateway_fcntl_api)as[symbol[SYMBOL FUNCTION]].
    eapply actual_exchange_set_flags_call;[apply PTree.gss| | |exact SYMBOL|exact FUNCTION].
    + unfold loaded,exchange_set_flags_temps;rewrite PTree.gso by discriminate;apply PTree.gss.
    + eapply actual_exchange_setup_unshadowed;[exact ALLOC|cbn;intuition discriminate].
Qed.
End AfterGet.

Definition exchange_set_flags_return(status:int)(temporaries:temp_env):=
  PTree.set _t'12(Val.of_bool(negb(Int.eq status Int.zero)))(PTree.set _t'13(Vint status)temporaries).

Theorem actual_exchange_after_set_script {World Event}(backend:gateway_backend World Event)
    target property(CLOSED:gateway_ambient_closed backend property)allocation_before allocated environment temporaries memory status:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  (status=Int.zero\/status=Int.neg Int.one)->
  (status=Int.zero->gateway_launch_path backend target property
    (State f_host_exchange(exchange_setup_after 6)Kstop environment(exchange_set_flags_return status temporaries)memory))->
  gateway_launch_path backend target property(Returnstate(Vint status)(exchange_set_flags_cont environment temporaries)memory).
Proof.
  intros ALLOC STATUS SUCCESS.
  set(returned:=PTree.set _t'13(Vint status)temporaries).
  set(marked:=exchange_set_flags_return status temporaries).
  eapply gateway_launch_same with(following:=State f_host_exchange Sskip
    (Kseq exchange_set_flags_bind(Kseq exchange_flags_error(Kseq(exchange_setup_after 6)Kstop)))environment returned memory);
    [exact CLOSED|cbn;tauto|exact I|intros;apply unchanged_store_edge,edge_returnstate|].
  eapply gateway_launch_same with(following:=State f_host_exchange exchange_set_flags_bind
    (Kseq exchange_flags_error(Kseq(exchange_setup_after 6)Kstop))environment returned memory);
    [exact CLOSED|cbn;tauto|exact I|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_launch_same with(following:=State f_host_exchange Sskip
    (Kseq exchange_flags_error(Kseq(exchange_setup_after 6)Kstop))environment marked memory);
    [exact CLOSED|cbn;tauto|exact I| |].
  { intros before world READY;apply certified_set_edge,old_expression_value;eapply value_cast with(v:=Vint status).
    - apply value_temp;apply PTree.gss.
    - change(Some(Vint(if Int.eq status Int.zero then Int.zero else Int.one))=
        Some(Val.of_bool(negb(Int.eq status Int.zero))));destruct(Int.eq status Int.zero);reflexivity. }
  eapply gateway_launch_same with(following:=State f_host_exchange exchange_flags_error
    (Kseq(exchange_setup_after 6)Kstop)environment marked memory);
    [exact CLOSED|cbn;tauto|exact I|intros;apply unchanged_store_edge,edge_skip_seq|].
  destruct STATUS as[ZERO|FAILED];subst status.
  - eapply gateway_launch_same with(following:=State f_host_exchange Sskip(Kseq(exchange_setup_after 6)Kstop)
      environment marked memory);
      [exact CLOSED|cbn;tauto|exact I| |].
    { intros before world READY;apply certified_if_edge with(v:=Vint Int.zero)(b:=false);
        [apply old_expression_value,value_temp;apply PTree.gss|reflexivity]. }
    eapply gateway_launch_same with(following:=State f_host_exchange(exchange_setup_after 6)Kstop environment marked memory);
      [exact CLOSED|cbn;tauto|exact I|intros;apply unchanged_store_edge,edge_skip_seq|apply SUCCESS;reflexivity].
  - eapply gateway_launch_same with(following:=State f_host_exchange(exchange_guard_failure exchange_flags_guard)
      (Kseq(exchange_setup_after 6)Kstop)environment marked memory);
      [exact CLOSED|cbn;tauto|exact I| |].
    { intros before world READY;apply certified_if_edge with(v:=Vint Int.one)(b:=true);
        [apply old_expression_value,value_temp;apply PTree.gss|reflexivity]. }
    eapply gateway_launch_failure with(allowed:=exchange_error_allowed).
    + exact(actual_exchange_error_bindings allocation_before environment allocated ALLOC).
    + apply((proj1(Forall_forall _ _))actual_exchange_errors_return).
      change(In(exchange_guard_failure exchange_flags_guard)exchange_early_errors).
      unfold exchange_early_errors;apply in_map;cbn;auto.
    + reflexivity.
Qed.
