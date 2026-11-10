(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: A selected integer failure remains failure through its actual callbacks and stores. *)
From Stdlib Require Import List Bool.
From compcert Require Import Coqlib AST Values Memory Events Integers Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps LocalAccess StoreSteps.
From HostGateway Require Import GatewayMachine GatewayRuntimeCuts GatewayFrames GatewayPure GatewayOperations GatewayFailurePaths.
Import ListNotations.

Definition gateway_integer_failure_expression := Eunop Oneg (Econst_int Int.one tint) tint.
Fixpoint gateway_must_integer_failure(statement:statement):Prop:=
  match statement with
  |Sreturn(Some expression)=>expression=gateway_integer_failure_expression
  |Ssequence first second=>gateway_must_integer_failure first \/
    (gateway_no_return first=true /\gateway_must_integer_failure second)
  |Sifthenelse _ first second=>gateway_must_integer_failure first /\gateway_must_integer_failure second
  |_=>False end.
Fixpoint gateway_integer_failure_barrier(continuation:cont):Prop:=
  match continuation with
  |Kseq statement rest=>
    (gateway_must_integer_failure statement /\call_cont rest=Kstop) \/
    (gateway_no_return statement=true /\gateway_integer_failure_barrier rest)
  |_=>False end.
Definition gateway_integer_failure_type function : Prop := fn_return function = tint.
Fixpoint gateway_nested_integer_failure(continuation:cont):Prop:=
  match continuation with
  |Kstop=>False
  |Kseq _ rest|Kloop1 _ _ rest|Kloop2 _ _ rest|Kswitch rest=>gateway_nested_integer_failure rest
  |Kcall _ function _ _ rest=>(gateway_integer_failure_type function /\gateway_integer_failure_barrier rest) \/gateway_nested_integer_failure rest
  end.
Definition gateway_integer_failure_source(source:Clight.state):Prop:=
  match source with
  |State function statement continuation _ _ _=>
    (gateway_integer_failure_type function /\call_cont continuation=Kstop /\
      (gateway_must_integer_failure statement \/(gateway_no_return statement=true /\gateway_integer_failure_barrier continuation))) \/
      gateway_nested_integer_failure continuation
  |Callstate _ _ continuation _=>gateway_nested_integer_failure continuation
  |Returnstate value continuation _=>gateway_nested_integer_failure continuation \/(continuation=Kstop /\value=(Vint (Int.neg Int.one)))
  end.

Lemma gateway_integer_failure_barrier_call_cont continuation :gateway_integer_failure_barrier continuation ->call_cont continuation=Kstop.
Proof. induction continuation;cbn;intuition. Qed.
Lemma gateway_nested_integer_failure_call_cont continuation :
  gateway_nested_integer_failure(call_cont continuation)<->gateway_nested_integer_failure continuation.
Proof. induction continuation;cbn;tauto. Qed.

Lemma gateway_integer_failure_find_label label body continuation found rest :
  find_label label body continuation=Some(found,rest) ->
  gateway_nested_integer_failure continuation ->gateway_nested_integer_failure rest
with gateway_integer_failure_find_label_branches label branches continuation found rest :
  find_label_ls label branches continuation=Some(found,rest) ->
  gateway_nested_integer_failure continuation ->gateway_nested_integer_failure rest.
Proof.
  - destruct body;cbn;intros FOUND NESTED;try discriminate.
    + destruct(find_label label body1(Kseq body2 continuation))as[[statement next]|]eqn:FIRST.
      * inversion FOUND;subst;eapply gateway_integer_failure_find_label;[exact FIRST|exact NESTED].
      * eapply gateway_integer_failure_find_label;[exact FOUND|exact NESTED].
    + destruct(find_label label body1 continuation)as[[statement next]|]eqn:FIRST.
      * inversion FOUND;subst;eapply gateway_integer_failure_find_label;[exact FIRST|exact NESTED].
      * eapply gateway_integer_failure_find_label;[exact FOUND|exact NESTED].
    + destruct(find_label label body1(Kloop1 body1 body2 continuation))as[[statement next]|]eqn:FIRST.
      * inversion FOUND;subst;eapply gateway_integer_failure_find_label;[exact FIRST|exact NESTED].
      * eapply gateway_integer_failure_find_label;[exact FOUND|exact NESTED].
    + eapply gateway_integer_failure_find_label_branches;[exact FOUND|exact NESTED].
    + destruct(ident_eq label l).
      * inversion FOUND;subst;exact NESTED.
      * eapply gateway_integer_failure_find_label;[exact FOUND|exact NESTED].
  - destruct branches;cbn;intros FOUND NESTED;try discriminate.
    destruct(find_label label s(Kseq(seq_of_labeled_statement branches)continuation))as[[statement next]|]eqn:FIRST.
    + inversion FOUND;subst;eapply gateway_integer_failure_find_label;[exact FIRST|exact NESTED].
    + eapply gateway_integer_failure_find_label_branches;[exact FOUND|exact NESTED].
Qed.

Lemma gateway_integer_failure_literal ge environment temporaries memory expression value target converted :
  expression=gateway_integer_failure_expression ->gateway_integer_failure_type target ->
  eval_expr ge environment temporaries memory expression value ->
  sem_cast value(typeof expression)(fn_return target)memory=Some converted ->converted=(Vint (Int.neg Int.one)).
Proof.
  intros EXPRESSION TYPE EVALUATION CAST; subst expression.
  assert (VALUE : expression_value ge environment temporaries memory gateway_integer_failure_expression
    (Vint (Int.neg Int.one))).
  { apply old_expression_value; eapply value_unary; [constructor | reflexivity]. }
  destruct VALUE as [VALUE UNIQUE]; pose proof (UNIQUE _ EVALUATION) as SAME; subst value.
  rewrite TYPE in CAST; cbn in CAST; inversion CAST; reflexivity.
Qed.

Lemma gateway_integer_failure_source_internal ge source trace after :
  gateway_integer_failure_source source ->step2 ge source trace after ->gateway_integer_failure_source after.
Proof.
  intros GOOD STEP;inversion STEP;subst;
    cbn[gateway_integer_failure_source gateway_no_return gateway_must_integer_failure gateway_integer_failure_barrier gateway_nested_integer_failure call_cont]in *.
  all:repeat rewrite andb_true_iff in *.
  all:try solve[intuition discriminate].
  - destruct b;tauto.
  - destruct H as[SAME|SAME];subst x;cbn[gateway_must_integer_failure gateway_no_return]in GOOD;intuition discriminate.
  - destruct GOOD as[[TYPE[STOP[IMPOSSIBLE|[NO_RETURN BARRIER]]]]|NESTED];[contradiction|discriminate|].
    left;apply gateway_nested_integer_failure_call_cont;exact NESTED.
  - destruct GOOD as[[TYPE[STOP[MUST|[IMPOSSIBLE BARRIER]]]]|NESTED];[|discriminate|].
    + right;split;[exact STOP|eapply gateway_integer_failure_literal;eassumption].
    + left;apply gateway_nested_integer_failure_call_cont;exact NESTED.
  - destruct GOOD as[[TYPE[STOP[IMPOSSIBLE|[NO_RETURN BARRIER]]]]|NESTED];[contradiction| |exact(or_introl NESTED)].
    destruct k;cbn in *;contradiction.
  - destruct H as[SAME|SAME];subst x;cbn[gateway_must_integer_failure gateway_no_return]in GOOD;intuition discriminate.
  - right;eapply gateway_integer_failure_find_label;[eassumption|].
    apply gateway_nested_integer_failure_call_cont;intuition discriminate.
  - destruct GOOD as[NESTED|[STOP VALUE]];[|discriminate].
    destruct NESTED as[[TYPE BARRIER]|NESTED].
    + left;split;[exact TYPE|]. split;[apply gateway_integer_failure_barrier_call_cont;exact BARRIER|].
      right;split;[reflexivity|exact BARRIER].
    + right;exact NESTED.
Qed.

Definition gateway_integer_failure_state {World}(state:gateway_state World):Prop:=
  match state with gateway_live source _=>gateway_integer_failure_source source|gateway_dead _ _=>True end.
Lemma gateway_integer_failure_step {World Event}(backend:gateway_backend World Event)ge before event after :
  gateway_integer_failure_state before ->gateway_step backend ge before event after ->gateway_integer_failure_state after.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn in *;try exact I.
  - eapply gateway_integer_failure_source_internal;eassumption.
  - left;exact GOOD.
  - destruct GOOD as[[TYPE[STOP[MUST|[NO_RETURN BARRIER]]]]|NESTED];[contradiction| |tauto].
    left;split;[exact TYPE|]. split;[exact STOP|]. right;split;[reflexivity|exact BARRIER].
  - destruct source;exact GOOD.
  - exact GOOD.
Qed.

Theorem gateway_actual_selected_integer_failure {World Event}(backend:gateway_backend World Event)ge
    function statement continuation environment temporaries before world events value after next :
  gateway_integer_failure_type function ->gateway_must_integer_failure statement ->call_cont continuation=Kstop ->
  gateway_steps backend ge
    (gateway_live(State function statement continuation environment temporaries before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value=(Vint (Int.neg Int.one)).
Proof.
  intros TYPE MUST STOP RUN.
  assert(INITIAL:gateway_integer_failure_state(gateway_live(State function statement continuation environment temporaries before)world)).
  { left;split;[exact TYPE|]. split;[exact STOP|left;exact MUST]. }
  assert(FINAL:gateway_integer_failure_state(gateway_live(Returnstate value Kstop after)next)).
  { revert INITIAL;induction RUN;intros GOOD;[exact GOOD|apply IHRUN;eapply gateway_integer_failure_step;eassumption]. }
  cbn in FINAL;tauto.
Qed.
