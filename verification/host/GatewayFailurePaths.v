(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: A selected source failure cannot become a successful pointer. *)
From Stdlib Require Import List Bool.
From compcert Require Import Coqlib AST Values Memory Events Integers Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps LocalAccess StoreSteps.
From HostGateway Require Import GatewayMachine GatewayRuntimeCuts GatewayFrames GatewayPure GatewayOperations.
Import ListNotations.

Definition gateway_null_expression:=Ecast(Econst_int Int.zero tint)(tptr tvoid).
Fixpoint gateway_no_return(statement:statement):bool:=
  match statement with
  |Sskip|Sassign _ _|Sset _ _|Scall _ _ _|Sbuiltin _ _ _ _=>true
  |Ssequence first second|Sifthenelse _ first second=>gateway_no_return first&&gateway_no_return second
  |_=>false end.
Fixpoint gateway_must_null(statement:statement):Prop:=
  match statement with
  |Sreturn(Some expression)=>expression=gateway_null_expression
  |Ssequence first second=>gateway_must_null first \/
    (gateway_no_return first=true /\gateway_must_null second)
  |Sifthenelse _ first second=>gateway_must_null first /\gateway_must_null second
  |_=>False end.
Fixpoint gateway_null_barrier(continuation:cont):Prop:=
  match continuation with
  |Kseq statement rest=>
    (gateway_must_null statement /\call_cont rest=Kstop) \/
    (gateway_no_return statement=true /\gateway_null_barrier rest)
  |_=>False end.
Definition gateway_pointer_return function :Prop:=exists pointee attr,fn_return function=Tpointer pointee attr.
Fixpoint gateway_nested_null(continuation:cont):Prop:=
  match continuation with
  |Kstop=>False
  |Kseq _ rest|Kloop1 _ _ rest|Kloop2 _ _ rest|Kswitch rest=>gateway_nested_null rest
  |Kcall _ function _ _ rest=>(gateway_pointer_return function /\gateway_null_barrier rest) \/gateway_nested_null rest
  end.
Definition gateway_null_source(source:Clight.state):Prop:=
  match source with
  |State function statement continuation _ _ _=>
    (gateway_pointer_return function /\call_cont continuation=Kstop /\
      (gateway_must_null statement \/(gateway_no_return statement=true /\gateway_null_barrier continuation))) \/
      gateway_nested_null continuation
  |Callstate _ _ continuation _=>gateway_nested_null continuation
  |Returnstate value continuation _=>gateway_nested_null continuation \/(continuation=Kstop /\value=Vnullptr)
  end.

Lemma gateway_null_barrier_call_cont continuation :gateway_null_barrier continuation ->call_cont continuation=Kstop.
Proof. induction continuation;cbn;intuition. Qed.
Lemma gateway_nested_null_call_cont continuation :
  gateway_nested_null(call_cont continuation)<->gateway_nested_null continuation.
Proof. induction continuation;cbn;tauto. Qed.

Lemma gateway_null_find_label label body continuation found rest :
  find_label label body continuation=Some(found,rest) ->
  gateway_nested_null continuation ->gateway_nested_null rest
with gateway_null_find_label_branches label branches continuation found rest :
  find_label_ls label branches continuation=Some(found,rest) ->
  gateway_nested_null continuation ->gateway_nested_null rest.
Proof.
  - destruct body;cbn;intros FOUND NESTED;try discriminate.
    + destruct(find_label label body1(Kseq body2 continuation))as[[statement next]|]eqn:FIRST.
      * inversion FOUND;subst;eapply gateway_null_find_label;[exact FIRST|exact NESTED].
      * eapply gateway_null_find_label;[exact FOUND|exact NESTED].
    + destruct(find_label label body1 continuation)as[[statement next]|]eqn:FIRST.
      * inversion FOUND;subst;eapply gateway_null_find_label;[exact FIRST|exact NESTED].
      * eapply gateway_null_find_label;[exact FOUND|exact NESTED].
    + destruct(find_label label body1(Kloop1 body1 body2 continuation))as[[statement next]|]eqn:FIRST.
      * inversion FOUND;subst;eapply gateway_null_find_label;[exact FIRST|exact NESTED].
      * eapply gateway_null_find_label;[exact FOUND|exact NESTED].
    + eapply gateway_null_find_label_branches;[exact FOUND|exact NESTED].
    + destruct(ident_eq label l).
      * inversion FOUND;subst;exact NESTED.
      * eapply gateway_null_find_label;[exact FOUND|exact NESTED].
  - destruct branches;cbn;intros FOUND NESTED;try discriminate.
    destruct(find_label label s(Kseq(seq_of_labeled_statement branches)continuation))as[[statement next]|]eqn:FIRST.
    + inversion FOUND;subst;eapply gateway_null_find_label;[exact FIRST|exact NESTED].
    + eapply gateway_null_find_label_branches;[exact FOUND|exact NESTED].
Qed.

Lemma gateway_null_literal ge environment temporaries memory expression value target converted :
  expression=gateway_null_expression ->gateway_pointer_return target ->
  eval_expr ge environment temporaries memory expression value ->
  sem_cast value(typeof expression)(fn_return target)memory=Some converted ->converted=Vnullptr.
Proof.
  intros EXPRESSION[pointee[attr TYPE]]EVALUATION CAST;subst expression.
  assert(VALUE:expression_value ge environment temporaries memory gateway_null_expression Vnullptr).
  { apply old_expression_value;eapply value_cast;[constructor|reflexivity]. }
  destruct VALUE as[VALUE UNIQUE];pose proof(UNIQUE _ EVALUATION)as SAME;subst value.
  rewrite TYPE in CAST;cbn in CAST;inversion CAST;reflexivity.
Qed.

Lemma gateway_null_source_internal ge source trace after :
  gateway_null_source source ->step2 ge source trace after ->gateway_null_source after.
Proof.
  intros GOOD STEP;inversion STEP;subst;
    cbn[gateway_null_source gateway_no_return gateway_must_null gateway_null_barrier gateway_nested_null call_cont]in *.
  all:repeat rewrite andb_true_iff in *.
  all:try solve[intuition discriminate].
  - destruct b;tauto.
  - destruct H as[SAME|SAME];subst x;cbn[gateway_must_null gateway_no_return]in GOOD;intuition discriminate.
  - destruct GOOD as[[TYPE[STOP[IMPOSSIBLE|[NO_RETURN BARRIER]]]]|NESTED];[contradiction|discriminate|].
    left;apply gateway_nested_null_call_cont;exact NESTED.
  - destruct GOOD as[[TYPE[STOP[MUST|[IMPOSSIBLE BARRIER]]]]|NESTED];[|discriminate|].
    + right;split;[exact STOP|eapply gateway_null_literal;eassumption].
    + left;apply gateway_nested_null_call_cont;exact NESTED.
  - destruct GOOD as[[TYPE[STOP[IMPOSSIBLE|[NO_RETURN BARRIER]]]]|NESTED];[contradiction| |exact(or_introl NESTED)].
    destruct k;cbn in *;contradiction.
  - destruct H as[SAME|SAME];subst x;cbn[gateway_must_null gateway_no_return]in GOOD;intuition discriminate.
  - right;eapply gateway_null_find_label;[eassumption|].
    apply gateway_nested_null_call_cont;intuition discriminate.
  - destruct GOOD as[NESTED|[STOP VALUE]];[|discriminate].
    destruct NESTED as[[TYPE BARRIER]|NESTED].
    + left;split;[exact TYPE|]. split;[apply gateway_null_barrier_call_cont;exact BARRIER|].
      right;split;[reflexivity|exact BARRIER].
    + right;exact NESTED.
Qed.

Definition gateway_null_state {World}(state:gateway_state World):Prop:=
  match state with gateway_live source _=>gateway_null_source source|gateway_dead _ _=>True end.
Lemma gateway_null_step {World Event}(backend:gateway_backend World Event)ge before event after :
  gateway_null_state before ->gateway_step backend ge before event after ->gateway_null_state after.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn in *;try exact I.
  - eapply gateway_null_source_internal;eassumption.
  - left;exact GOOD.
  - destruct GOOD as[[TYPE[STOP[MUST|[NO_RETURN BARRIER]]]]|NESTED];[contradiction| |tauto].
    left;split;[exact TYPE|]. split;[exact STOP|]. right;split;[reflexivity|exact BARRIER].
  - destruct source;exact GOOD.
  - exact GOOD.
Qed.

Theorem gateway_actual_selected_failure {World Event}(backend:gateway_backend World Event)ge
    function statement continuation environment temporaries before world events value after next :
  gateway_pointer_return function ->gateway_must_null statement ->call_cont continuation=Kstop ->
  gateway_steps backend ge
    (gateway_live(State function statement continuation environment temporaries before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value=Vnullptr.
Proof.
  intros TYPE MUST STOP RUN.
  assert(INITIAL:gateway_null_state(gateway_live(State function statement continuation environment temporaries before)world)).
  { left;split;[exact TYPE|]. split;[exact STOP|left;exact MUST]. }
  assert(FINAL:gateway_null_state(gateway_live(Returnstate value Kstop after)next)).
  { revert INITIAL;induction RUN;intros GOOD;[exact GOOD|apply IHRUN;eapply gateway_null_step;eassumption]. }
  cbn in FINAL;tauto.
Qed.

Definition gateway_failure_result {World Event}(backend:gateway_backend World Event)ge source :Prop:=
  forall before world events value after next,
    gateway_steps backend ge(gateway_live(gateway_replace_memory source before)world)events
      (gateway_live(Returnstate value Kstop after)next) ->value=Vnullptr.

Theorem gateway_failure_selected {World Event}(backend:gateway_backend World Event)ge
    function statement continuation environment temporaries memory :
  gateway_pointer_return function ->gateway_must_null statement ->call_cont continuation=Kstop ->
  gateway_failure_result backend ge(State function statement continuation environment temporaries memory).
Proof.
  intros TYPE MUST STOP before world events value after next RUN.
  eapply gateway_actual_selected_failure;eassumption.
Qed.

Lemma gateway_failure_edge {World Event}(backend:gateway_backend World Event)ge source target :
  ~gateway_at_primitive source ->
  (forall memory,store_edge ge(gateway_replace_memory source memory)(gateway_replace_memory target memory)) ->
  gateway_failure_result backend ge target ->gateway_failure_result backend ge source.
Proof.
  intros INTERNAL EDGE FAILURE before world events value after next RUN.
  destruct(gateway_uniform_edge_side_cut backend ge(fun _ _=>True)
    ltac:(unfold gateway_runtime_discipline;intros;exact I)
    source target before world events value after next INTERNAL ltac:(intros;apply EDGE)I RUN)
    as(prefix &suffix &memory &current &EVENTS &AMBIENT &PREFIX &READY &REST).
  eapply FAILURE;exact REST.
Qed.
