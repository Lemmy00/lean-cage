(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Either real pair guard rejects, or this same exchange advances with zero. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayBindings GatewayExchangeSetup
  GatewayExchangeErrors GatewayLaunchQuiet GatewayLaunchPaths GatewayFramedRuntime GatewayPure GatewaySpawnABI GatewayReturnTypes.
Import ListNotations.

Inductive exchange_pair_stage:=exchange_data_stage|exchange_control_stage.
Definition exchange_pair_destination stage:=match stage with exchange_data_stage=>_t'3|exchange_control_stage=>_t'7 end.
Definition exchange_pair_guard stage:=match stage with
  exchange_data_stage=>exchange_data_pair_guard|exchange_control_stage=>exchange_control_pair_guard end.
Definition exchange_pair_after stage:=exchange_setup_after(match stage with
  exchange_data_stage=>3|exchange_control_stage=>4 end).
Definition exchange_pair_cont stage environment temporaries:=
  Kcall(Some(exchange_pair_destination stage))f_host_exchange environment temporaries
    (Kseq(exchange_pair_guard stage)(Kseq(exchange_pair_after stage)Kstop)).
Definition exchange_pair_failed stage:=match exchange_pair_guard stage with Sifthenelse _ failed _=>failed|_=>Sskip end.

Lemma actual_exchange_pair_return_profile:gateway_int_return_function f_host_private_pair.
Proof. split;[reflexivity|]. cbn;unfold gateway_int_return_expression;intuition. Qed.

Lemma gateway_temp_guard_undefined(ge:Clight.genv)function identifier ty environment temporaries memory value
    yes no continuation trace target:
  temporaries!identifier=Some value->bool_val value ty memory=None->
  ~step2 ge(State function(Sifthenelse(Etempvar identifier ty)yes no)continuation environment temporaries memory)trace target.
Proof.
  intros TEMP UNDEFINED STEP;inversion STEP;subst;
    try match goal with BAD:_=_\/_=_|-_=>destruct BAD;discriminate end.
  assert(EXPRESSION:expression_value ge environment temporaries memory(Etempvar identifier ty)value)
    by(apply old_expression_value,value_temp;exact TEMP).
  match goal with VALUE:eval_expr _ _ _ _ (Etempvar identifier ty) ?actual|-_=>
    pose proof((proj2 EXPRESSION)actual VALUE)as SAME;subst actual end.
  cbn[typeof]in *;congruence.
Qed.

Section PairGuard.
Context {World Event}(backend:gateway_backend World Event)(property:mem->World->Prop)
  (target:Clight.state->World->Prop).
Hypothesis CLOSED:gateway_ambient_closed backend property.
Variables(stage:exchange_pair_stage)(environment:env)(temporaries:temp_env)(memory:mem)(returned:val).

Theorem actual_exchange_pair_return_script allocation_before allocated:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  gateway_int_return_value returned->
  (returned=Vint Int.zero->gateway_quiet_launch_path backend target property
    (State f_host_exchange(exchange_pair_after stage)Kstop environment
      (PTree.set(exchange_pair_destination stage)returned temporaries)memory))->
  gateway_quiet_launch_path backend target property(Returnstate returned(exchange_pair_cont stage environment temporaries)memory).
Proof.
  intros ALLOC TYPE CONTINUE.
  set(changed:=PTree.set(exchange_pair_destination stage)returned temporaries).
  eapply gateway_quiet_launch_same with(following:=State f_host_exchange Sskip
    (Kseq(exchange_pair_guard stage)(Kseq(exchange_pair_after stage)Kstop))environment changed memory);
    [exact CLOSED|cbn;tauto|exact I|intros;apply unchanged_store_edge,edge_returnstate|].
  eapply gateway_quiet_launch_same with(following:=State f_host_exchange(exchange_pair_guard stage)
    (Kseq(exchange_pair_after stage)Kstop)environment changed memory);
    [exact CLOSED|cbn;tauto|exact I|intros;apply unchanged_store_edge,edge_skip_seq|].
  destruct TYPE as[UNDEFINED|[ZERO|FAILED]];subst returned.
  - eapply gateway_quiet_launch_stuck;[exact CLOSED|cbn;destruct stage;tauto|exact I|].
    intros available world trace following READY;cbn[gateway_replace_memory].
    destruct stage;unfold exchange_pair_guard,exchange_data_pair_guard,exchange_control_pair_guard.
    all:eapply gateway_temp_guard_undefined;[apply PTree.gss|reflexivity].
  - eapply gateway_quiet_launch_same with(following:=State f_host_exchange Sskip
      (Kseq(exchange_pair_after stage)Kstop)environment changed memory);
      [exact CLOSED|cbn;destruct stage;tauto|exact I| |].
    { intros available world READY;destruct stage;
        (apply certified_if_edge with(v:=Vint Int.zero)(b:=false);
         [apply old_expression_value,value_temp;apply PTree.gss|reflexivity]). }
    eapply gateway_quiet_launch_same with(following:=State f_host_exchange(exchange_pair_after stage)Kstop
      environment changed memory);
      [exact CLOSED|cbn;tauto|exact I|intros;apply unchanged_store_edge,edge_skip_seq|].
    apply CONTINUE;reflexivity.
  - eapply gateway_quiet_launch_same with(following:=State f_host_exchange(exchange_pair_failed stage)
      (Kseq(exchange_pair_after stage)Kstop)environment changed memory);
      [exact CLOSED|cbn;destruct stage;tauto|exact I| |].
    { intros available world READY;destruct stage;
        (apply certified_if_edge with(v:=Vint(Int.neg Int.one))(b:=true);
         [apply old_expression_value,value_temp;apply PTree.gss|reflexivity]). }
    eapply gateway_quiet_launch_failure with(allowed:=exchange_error_allowed).
    + exact(actual_exchange_error_bindings allocation_before environment allocated ALLOC).
    + apply((proj1(Forall_forall _ _))actual_exchange_errors_return).
      destruct stage.
      * change(In(exchange_guard_failure exchange_data_pair)exchange_early_errors).
        unfold exchange_early_errors;apply in_map;cbn;auto.
      * change(In(exchange_guard_failure exchange_control_pair)exchange_early_errors).
        unfold exchange_early_errors;apply in_map;cbn;auto.
    + reflexivity.
Qed.
End PairGuard.
