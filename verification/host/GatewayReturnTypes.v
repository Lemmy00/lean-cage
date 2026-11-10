(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Native helper results follow real source returns, not external
   ABI guesses. *)
From Stdlib Require Import List ZArith.
From compcert Require Import AST Values Memory Events Integers Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps LocalAccess.
From HostGateway Require Import GatewaySource GatewayMachine.
Import ListNotations.

Definition gateway_int_return_expression expression :Prop:=
  expression=Econst_int Int.zero tint \/
  expression=Eunop Oneg(Econst_int Int.one tint)tint.

Fixpoint gateway_int_return_statement(statement:statement):Prop:=
  match statement with
  |Ssequence first second|Sifthenelse _ first second|Sloop first second=>
    gateway_int_return_statement first /\gateway_int_return_statement second
  |Sreturn(Some expression)=>gateway_int_return_expression expression
  |Sswitch _ _|Slabel _ _|Sgoto _=>False
  |_=>True
  end.

Definition gateway_int_return_function function :Prop:=
  fn_return function=tint /\gateway_int_return_statement(fn_body function).

Fixpoint gateway_int_return_cont(continuation:cont):Prop:=
  match continuation with
  |Kstop=>True
  |Kseq statement rest=>gateway_int_return_statement statement /\gateway_int_return_cont rest
  |Kloop1 first second rest|Kloop2 first second rest=>
    gateway_int_return_statement first /\gateway_int_return_statement second /\gateway_int_return_cont rest
  |Kswitch rest=>gateway_int_return_cont rest
  |Kcall _ _ _ _ _=>False
  end.

Fixpoint gateway_nested_int_return_cont(continuation:cont):Prop:=
  match continuation with
  |Kstop=>False
  |Kseq _ rest|Kloop1 _ _ rest|Kloop2 _ _ rest|Kswitch rest=>gateway_nested_int_return_cont rest
  |Kcall _ function _ _ rest=>
    (gateway_int_return_function function /\gateway_int_return_cont rest) \/
      gateway_nested_int_return_cont rest
  end.

Definition gateway_int_return_value value :Prop:=
  value=Vundef \/value=Vint Int.zero \/value=Vint(Int.neg Int.one).

Definition gateway_int_return_source(source:Clight.state):Prop:=
  match source with
  |State function statement continuation _ _ _=>
    (gateway_int_return_function function /\gateway_int_return_statement statement /\
      gateway_int_return_cont continuation) \/gateway_nested_int_return_cont continuation
  |Callstate definition _ continuation _=>gateway_nested_int_return_cont continuation \/
    exists function,definition=Internal function /\continuation=Kstop /\gateway_int_return_function function
  |Returnstate value continuation _=>gateway_nested_int_return_cont continuation \/
    continuation=Kstop /\gateway_int_return_value value
  end.

Lemma gateway_int_cont_is_stop continuation :
  gateway_int_return_cont continuation ->is_call_cont continuation ->continuation=Kstop.
Proof. destruct continuation;cbn;intuition congruence. Qed.

Lemma gateway_int_cont_call_cont continuation :
  gateway_int_return_cont continuation ->call_cont continuation=Kstop.
Proof. induction continuation;cbn;intuition. Qed.

Lemma gateway_nested_cont_call_cont continuation :
  gateway_nested_int_return_cont(call_cont continuation)<->gateway_nested_int_return_cont continuation.
Proof. induction continuation;cbn;tauto. Qed.

Lemma gateway_nested_find_label label body k found rest:
  find_label label body k=Some(found,rest) ->gateway_nested_int_return_cont k ->gateway_nested_int_return_cont rest
with gateway_nested_find_label_branches label branches k found rest:
  find_label_ls label branches k=Some(found,rest) ->gateway_nested_int_return_cont k ->gateway_nested_int_return_cont rest.
Proof.
  - destruct body;cbn;intros FOUND CONT;try discriminate.
    + destruct(find_label label body1(Kseq body2 k))as[[statement next]|]eqn:FIRST.
      * inversion FOUND;subst;eapply gateway_nested_find_label;[exact FIRST|exact CONT].
      * eapply gateway_nested_find_label;[exact FOUND|exact CONT].
    + destruct(find_label label body1 k)as[[statement next]|]eqn:FIRST.
      * inversion FOUND;subst;eapply gateway_nested_find_label;[exact FIRST|exact CONT].
      * eapply gateway_nested_find_label;[exact FOUND|exact CONT].
    + destruct(find_label label body1(Kloop1 body1 body2 k))as[[statement next]|]eqn:FIRST.
      * inversion FOUND;subst;eapply gateway_nested_find_label;[exact FIRST|exact CONT].
      * eapply gateway_nested_find_label;[exact FOUND|exact CONT].
    + eapply gateway_nested_find_label_branches;[exact FOUND|exact CONT].
    + destruct(ident_eq label l).
      * inversion FOUND;subst;exact CONT.
      * eapply gateway_nested_find_label;[exact FOUND|exact CONT].
  - destruct branches;cbn;intros FOUND CONT;try discriminate.
    destruct(find_label label s(Kseq(seq_of_labeled_statement branches)k))as[[statement next]|]eqn:FIRST.
    + inversion FOUND;subst;eapply gateway_nested_find_label;[exact FIRST|exact CONT].
    + eapply gateway_nested_find_label_branches;[exact FOUND|exact CONT].
Qed.

Lemma gateway_int_literal_value ge environment temporaries memory expression value converted :
  gateway_int_return_expression expression ->
  eval_expr ge environment temporaries memory expression value ->
  sem_cast value(typeof expression)tint memory=Some converted ->
  gateway_int_return_value converted.
Proof.
  intros[LITERAL|LITERAL] EVALUATION CAST;subst expression.
  - assert(VALUE:expression_value ge environment temporaries memory
      (Econst_int Int.zero tint)(Vint Int.zero)).
    { apply old_expression_value;constructor. }
    destruct VALUE as[VALUE UNIQUE];pose proof(UNIQUE _ EVALUATION)as SAME;subst value.
    cbn in CAST;inversion CAST;subst;right;left;reflexivity.
  - assert(VALUE:expression_value ge environment temporaries memory
      (Eunop Oneg(Econst_int Int.one tint)tint)(Vint(Int.neg Int.one))).
    { apply old_expression_value;eapply value_unary;[constructor|reflexivity]. }
    destruct VALUE as[VALUE UNIQUE];pose proof(UNIQUE _ EVALUATION)as SAME;subst value.
    cbn in CAST;inversion CAST;subst;right;right;reflexivity.
Qed.

Lemma gateway_int_return_internal ge source observed next :
  gateway_int_return_source source ->step2 ge source observed next ->gateway_int_return_source next.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn in *.
  all:try solve[tauto].
  - destruct b;tauto.
  - destruct GOOD as[[FUNCTION[STATEMENT CONT]]|NESTED].
    + right;split;[apply gateway_int_cont_call_cont;exact CONT|left;reflexivity].
    + left;apply gateway_nested_cont_call_cont;exact NESTED.
  - destruct GOOD as[[[TYPE FUNCTION][STATEMENT CONT]]|NESTED].
    + right;split;[apply gateway_int_cont_call_cont;exact CONT|].
      eapply gateway_int_literal_value;[exact STATEMENT|eassumption|].
      rewrite <-TYPE;eassumption.
    + left;apply gateway_nested_cont_call_cont;exact NESTED.
  - destruct GOOD as[[FUNCTION[STATEMENT CONT]]|NESTED].
    + right;split;[eapply gateway_int_cont_is_stop;eassumption|left;reflexivity].
    + left;exact NESTED.
  - right;eapply gateway_nested_find_label;[eassumption|].
    apply gateway_nested_cont_call_cont;tauto.
  - destruct GOOD as[NESTED|[function[DEFINITION[STOP FUNCTION]]]].
    + right;exact NESTED.
    + inversion DEFINITION;subst;left;split;[exact FUNCTION|split;[exact(proj2 FUNCTION)|exact I]].
  - destruct GOOD as[NESTED|[function[DEFINITION[STOP FUNCTION]]]].
    + left;exact NESTED.
    + discriminate.
  - destruct GOOD as[NESTED|[STOP VALUE]];[tauto|discriminate].
Qed.

Definition gateway_int_return_state {World}(state:gateway_state World):Prop:=
  match state with gateway_live source _=>gateway_int_return_source source|gateway_dead _ _=>True end.

Lemma gateway_int_return_step {World Event}(backend:gateway_backend World Event)ge before observed after :
  gateway_int_return_state before ->gateway_step backend ge before observed after ->
  gateway_int_return_state after.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn in *;try exact I.
  - eapply gateway_int_return_internal;eassumption.
  - destruct GOOD as[NESTED|[function[DEFINITION[STOP FUNCTION]]]];[left;exact NESTED|discriminate].
  - tauto.
  - destruct source;exact GOOD.
  - exact GOOD.
Qed.

Theorem gateway_actual_int_return {World Event}(backend:gateway_backend World Event)ge
    function arguments before world events returned after next :
  gateway_int_return_function function ->
  gateway_steps backend ge(gateway_live(Callstate(Internal function)arguments Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->gateway_int_return_value returned.
Proof.
  intros FUNCTION RUN.
  assert(GOOD:gateway_int_return_state
    (gateway_live(Callstate(Internal function)arguments Kstop before)world)).
  { right;exists function;auto. }
  assert(FINAL:gateway_int_return_state(gateway_live(Returnstate returned Kstop after)next)).
  { revert GOOD;induction RUN;intro GOOD;[exact GOOD|apply IHRUN;eapply gateway_int_return_step;eassumption]. }
  cbn in FINAL;tauto.
Qed.

Lemma actual_host_read_return_profile:gateway_int_return_function f_host_read.
Proof. unfold gateway_int_return_function;split;[reflexivity|].
  cbn;unfold gateway_int_return_expression;intuition. Qed.

Lemma actual_host_transfer_return_profile:gateway_int_return_function f_host_transfer.
Proof. unfold gateway_int_return_function;split;[reflexivity|].
  cbn;unfold gateway_int_return_expression;intuition. Qed.

Lemma actual_host_ready_return_profile:gateway_int_return_function f_host_ready.
Proof. unfold gateway_int_return_function;split;[reflexivity|].
  cbn;unfold gateway_int_return_expression;intuition. Qed.

Lemma actual_host_control_return_profile:gateway_int_return_function f_host_control.
Proof. unfold gateway_int_return_function;split;[reflexivity|].
  cbn;unfold gateway_int_return_expression;intuition. Qed.

Theorem actual_host_read_return_type {World Event}(backend:gateway_backend World Event)ge
    arguments before world events returned after next :
  gateway_steps backend ge(gateway_live(Callstate(Internal f_host_read)arguments Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->
  returned=Vundef \/returned=Vint Int.zero \/returned=Vint(Int.neg Int.one).
Proof. apply gateway_actual_int_return;exact actual_host_read_return_profile. Qed.
