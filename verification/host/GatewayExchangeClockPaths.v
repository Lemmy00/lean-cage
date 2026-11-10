(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual clock guard precedes this exchange's first private pair. *)
From Stdlib Require Import ZArith List Bool.
From compcert Require Import Coqlib Maps Integers Floats AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayBindings GatewayExchangeSetup
  GatewayExchangeErrors GatewayLaunchQuiet GatewayLaunchPaths GatewayFramedRuntime GatewayPure GatewaySpawnABI.
Import ListNotations.

Definition exchange_clock_call:=match exchange_clock_prefix with Ssequence call _=>call|_=>Sskip end.
Definition exchange_clock_bind:=match exchange_clock_prefix with Ssequence _ bind=>bind|_=>Sskip end.
Definition exchange_clock_cont environment temporaries:=
  Kcall(Some _t'1)f_host_exchange environment temporaries
    (Kseq exchange_clock_bind(Kseq(exchange_setup_after 1)Kstop)).
Definition exchange_clock_temps(value:val)(temporaries:temp_env):=
  PTree.set _began value(PTree.set _t'1 value temporaries).
Definition exchange_first_pair_cont environment temporaries:=
  Kcall(Some _t'3)f_host_exchange environment temporaries
    (Kseq exchange_data_pair_guard(Kseq(exchange_setup_after 3)Kstop)).

Definition exchange_clock_truth(value:val):option bool:=
  match value with Vfloat number=>Some(negb(Float.cmp Ceq number Float.zero))|_=>None end.

Lemma exchange_clock_truth_actual value memory:
  bool_val value tdouble memory=exchange_clock_truth value.
Proof. destruct value;reflexivity. Qed.

Lemma exchange_clock_negation(ge:Clight.genv)environment temporaries memory value truth:
  temporaries!_began=Some value->exchange_clock_truth value=Some truth->
  expression_value ge environment temporaries memory(Eunop Onotbool(Etempvar _began tdouble)tint)
    (Val.of_bool(negb truth)).
Proof.
  intros TEMP TRUTH;apply old_expression_value;eapply value_unary with(v:=value);[apply value_temp;exact TEMP|].
  change(option_map(fun flag=>Val.of_bool(negb flag))(bool_val value tdouble memory)=Some(Val.of_bool(negb truth))).
  rewrite exchange_clock_truth_actual,TRUTH;reflexivity.
Qed.

Lemma exchange_clock_guard_undefined(ge:Clight.genv)environment temporaries memory value continuation trace target:
  temporaries!_began=Some value->exchange_clock_truth value=None->
  ~step2 ge(State f_host_exchange exchange_clock_guard continuation environment temporaries memory)trace target.
Proof.
  intros TEMP UNDEFINED STEP;inversion STEP;subst;
    try match goal with BAD:_=_\/_=_|-_=>destruct BAD;discriminate end.
  match goal with VALUE:eval_expr _ _ _ _ (Eunop Onotbool(Etempvar _began tdouble)tint) _|-_=>
    inversion VALUE;subst end.
  all:try match goal with LOCATION:eval_lvalue _ _ _ _ (Eunop _ _ _) _ _ _|-_=>inversion LOCATION end.
  match goal with VALUE:eval_expr _ _ _ _ (Etempvar _began tdouble) ?actual|-_=>
    assert(EXPRESSION:expression_value ge environment temporaries memory(Etempvar _began tdouble)value)
      by(apply old_expression_value,value_temp;exact TEMP);
    pose proof((proj2 EXPRESSION)actual VALUE)as SAME;subst actual end.
  match goal with OPERATION:sem_unary_operation Onotbool value _ memory=Some ?result|-_=>
    change(option_map(fun flag=>Val.of_bool(negb flag))(bool_val value tdouble memory)=Some result)in OPERATION;
    rewrite exchange_clock_truth_actual,UNDEFINED in OPERATION;discriminate end.
Qed.

Definition exchange_clock_point {World}(property:mem->World->Prop)environment temporaries source world:Prop:=
  exists memory,source=Callstate(Internal f_host_now)[](exchange_clock_cont environment temporaries)memory /\
    property memory world.

Definition exchange_first_pair_point {World}(property:mem->World->Prop)environment temporaries data value source world:Prop:=
  exists memory,source=Callstate(Internal f_host_private_pair)[Vptr data Ptrofs.zero]
    (exchange_first_pair_cont environment(exchange_clock_temps value temporaries))memory /\
    exchange_clock_truth value=Some true /\property memory world.

Section ClockPaths.
Context {World Event}(backend:gateway_backend World Event)(property:mem->World->Prop).
Hypothesis CLOSED:gateway_ambient_closed backend property.
Variables(environment:env)(temporaries:temp_env)(memory:mem).

Theorem actual_exchange_clock_call_script symbol:
  environment!_host_now=None->
  Genv.find_symbol(Clight.globalenv prog)_host_now=Some symbol->
  Genv.find_funct_ptr(Clight.globalenv prog)symbol=Some(Internal f_host_now)->
  gateway_quiet_launch_path backend(exchange_clock_point property environment temporaries)property
    (State f_host_exchange(exchange_setup_after 0)Kstop environment temporaries memory).
Proof.
  intros UNSHADOWED SYMBOL FUNCTION.
  eapply gateway_quiet_launch_same with(following:=State f_host_exchange exchange_clock_prefix
    (Kseq(exchange_setup_after 1)Kstop)environment temporaries memory);
    [exact CLOSED|cbn;tauto|exact I|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_quiet_launch_same with(following:=State f_host_exchange exchange_clock_call
    (Kseq exchange_clock_bind(Kseq(exchange_setup_after 1)Kstop))environment temporaries memory);
    [exact CLOSED|cbn;tauto|exact I|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_quiet_launch_same with(following:=Callstate(Internal f_host_now)[]
    (exchange_clock_cont environment temporaries)memory);
    [exact CLOSED|cbn;tauto|exact I| |].
  - intros available world READY;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
    + reflexivity.
    + apply old_expression_value;eapply value_function;[exact UNSHADOWED|exact SYMBOL|reflexivity].
    + apply no_argument_values.
    + unfold Genv.find_funct;destruct(Ptrofs.eq_dec Ptrofs.zero Ptrofs.zero);
        [exact FUNCTION|contradiction].
    + reflexivity.
  - apply gateway_quiet_launch_reached;intros available world READY;exists available;split;[reflexivity|exact READY].
Qed.

Theorem actual_exchange_clock_return_script allocation_before allocated data value:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  environment!_pair=Some(data,tarray tint 2)->
  gateway_quiet_launch_path backend(exchange_first_pair_point property environment temporaries data value)property
    (Returnstate value(exchange_clock_cont environment temporaries)memory).
Proof.
  intros ALLOC ARRAY.
  set(after_call:=PTree.set _t'1 value temporaries).
  set(after_clock:=exchange_clock_temps value temporaries).
  eapply gateway_quiet_launch_same with(following:=State f_host_exchange Sskip
    (Kseq exchange_clock_bind(Kseq(exchange_setup_after 1)Kstop))environment after_call memory);
    [exact CLOSED|cbn;tauto|exact I|intros;apply unchanged_store_edge,edge_returnstate|].
  eapply gateway_quiet_launch_same with(following:=State f_host_exchange exchange_clock_bind
    (Kseq(exchange_setup_after 1)Kstop)environment after_call memory);
    [exact CLOSED|cbn;tauto|exact I|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_quiet_launch_same with(following:=State f_host_exchange Sskip
    (Kseq(exchange_setup_after 1)Kstop)environment after_clock memory);
    [exact CLOSED|cbn;tauto|exact I| |].
  { intros available world READY;apply certified_set_edge,old_expression_value,value_temp;apply PTree.gss. }
  eapply gateway_quiet_launch_same with(following:=State f_host_exchange(exchange_setup_after 1)Kstop
    environment after_clock memory);
    [exact CLOSED|cbn;tauto|exact I|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_quiet_launch_same with(following:=State f_host_exchange exchange_clock_guard
    (Kseq(exchange_setup_after 2)Kstop)environment after_clock memory);
    [exact CLOSED|cbn;tauto|exact I|intros;apply unchanged_store_edge,edge_seq|].
  destruct(exchange_clock_truth value)as[truth|]eqn:TRUTH.
  - destruct truth.
    + eapply gateway_quiet_launch_same with(following:=State f_host_exchange Sskip
      (Kseq(exchange_setup_after 2)Kstop)environment after_clock memory);
      [exact CLOSED|cbn;tauto|exact I| |].
      { intros available world READY;apply certified_if_edge with(v:=Vint Int.zero)(b:=false).
        - exact(exchange_clock_negation _ environment after_clock available value true(PTree.gss _ _ _)TRUTH).
        - reflexivity. }
      eapply gateway_quiet_launch_same with(following:=State f_host_exchange(exchange_setup_after 2)Kstop
        environment after_clock memory);
        [exact CLOSED|cbn;tauto|exact I|intros;apply unchanged_store_edge,edge_skip_seq|].
      eapply gateway_quiet_launch_same with(following:=State f_host_exchange exchange_data_pair
        (Kseq(exchange_setup_after 3)Kstop)environment after_clock memory);
        [exact CLOSED|cbn;tauto|exact I|intros;apply unchanged_store_edge,edge_seq|].
      eapply gateway_quiet_launch_same with(following:=State f_host_exchange exchange_data_pair_call
        (Kseq exchange_data_pair_guard(Kseq(exchange_setup_after 3)Kstop))environment after_clock memory);
        [exact CLOSED|cbn;tauto|exact I|intros;apply unchanged_store_edge,edge_seq|].
      eapply gateway_quiet_launch_same with(following:=Callstate(Internal f_host_private_pair)[Vptr data Ptrofs.zero]
        (exchange_first_pair_cont environment after_clock)memory);
        [exact CLOSED|cbn;tauto|exact I| |].
      { intros available world READY.
        destruct(gateway_actual_function_binding _host_private_pair(Internal f_host_private_pair)
          ltac:(vm_compute;reflexivity))as[symbol[SYMBOL FUNCTION]].
        eapply actual_exchange_data_pair_call;[exact ARRAY| |exact SYMBOL|exact FUNCTION].
        eapply actual_exchange_setup_unshadowed;[exact ALLOC|cbn;intuition discriminate]. }
      apply gateway_quiet_launch_reached;intros available world READY;exists available.
      split;[reflexivity|]. split;[exact TRUTH|exact READY].
    + eapply gateway_quiet_launch_same with(following:=State f_host_exchange
      (exchange_guard_failure exchange_clock_guard)(Kseq(exchange_setup_after 2)Kstop)environment after_clock memory);
      [exact CLOSED|cbn;tauto|exact I| |].
      { intros available world READY;apply certified_if_edge with(v:=Vint Int.one)(b:=true).
        - exact(exchange_clock_negation _ environment after_clock available value false(PTree.gss _ _ _)TRUTH).
        - reflexivity. }
      eapply gateway_quiet_launch_failure with(allowed:=exchange_error_allowed).
      * exact(actual_exchange_error_bindings allocation_before environment allocated ALLOC).
      * apply((proj1(Forall_forall _ _))actual_exchange_errors_return).
        change(In(exchange_guard_failure exchange_clock_guard)exchange_early_errors).
        unfold exchange_early_errors;apply in_map;cbn;auto.
      * reflexivity.
  - eapply gateway_quiet_launch_stuck;[exact CLOSED|cbn;tauto|exact I|].
    intros available world trace target READY;cbn[gateway_replace_memory].
    eapply exchange_clock_guard_undefined;[apply PTree.gss|exact TRUTH].
Qed.
End ClockPaths.
