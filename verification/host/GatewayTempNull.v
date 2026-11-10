(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Error cleanup retains the actual preinitialized null temporary. *)
From Stdlib Require Import List Bool.
From compcert Require Import Coqlib Maps AST Values Memory Events Integers Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps LocalAccess StoreSteps.
From HostGateway Require Import GatewayMachine GatewayFailurePaths.

Definition gateway_keeps_temp protected assigned :bool:=if ident_eq protected assigned then false else true.
Definition gateway_keeps_destination protected destination :bool:=
  match destination with None=>true|Some assigned=>gateway_keeps_temp protected assigned end.

Fixpoint gateway_no_temp_return protected(statement:statement):bool:=
  match statement with
  |Sskip|Sassign _ _=>true
  |Sset assigned _=>gateway_keeps_temp protected assigned
  |Scall destination _ _|Sbuiltin destination _ _ _=>gateway_keeps_destination protected destination
  |Ssequence first second|Sifthenelse _ first second=>
    gateway_no_temp_return protected first&&gateway_no_temp_return protected second
  |_=>false end.

Definition gateway_temp_pointer protected expression :Prop:=
  exists pointee attr,expression=Etempvar protected(Tpointer pointee attr).

Fixpoint gateway_must_temp protected(statement:statement):Prop:=
  match statement with
  |Sreturn(Some expression)=>gateway_temp_pointer protected expression
  |Ssequence first second=>gateway_must_temp protected first \/
    (gateway_no_temp_return protected first=true /\gateway_must_temp protected second)
  |Sifthenelse _ first second=>gateway_must_temp protected first /\gateway_must_temp protected second
  |_=>False end.

Fixpoint gateway_temp_barrier protected(continuation:cont):Prop:=
  match continuation with
  |Kseq statement rest=>
    (gateway_must_temp protected statement /\call_cont rest=Kstop) \/
    (gateway_no_temp_return protected statement=true /\gateway_temp_barrier protected rest)
  |_=>False end.

Fixpoint gateway_nested_temp protected(continuation:cont):Prop:=
  match continuation with
  |Kstop=>False
  |Kseq _ rest|Kloop1 _ _ rest|Kloop2 _ _ rest|Kswitch rest=>gateway_nested_temp protected rest
  |Kcall destination function _ parameters rest=>
    (gateway_pointer_return function /\parameters!protected=Some Vnullptr /\
      gateway_keeps_destination protected destination=true /\gateway_temp_barrier protected rest) \/
    gateway_nested_temp protected rest
  end.

Definition gateway_temp_null_source protected(source:Clight.state):Prop:=
  match source with
  |State function statement continuation _ parameters _=>
    (gateway_pointer_return function /\parameters!protected=Some Vnullptr /\call_cont continuation=Kstop /\
      (gateway_must_temp protected statement \/
        (gateway_no_temp_return protected statement=true /\gateway_temp_barrier protected continuation))) \/
      gateway_nested_temp protected continuation
  |Callstate _ _ continuation _=>gateway_nested_temp protected continuation
  |Returnstate value continuation _=>gateway_nested_temp protected continuation \/
    (continuation=Kstop /\value=Vnullptr)
  end.

Lemma gateway_temp_barrier_call_cont protected continuation :
  gateway_temp_barrier protected continuation ->call_cont continuation=Kstop.
Proof. induction continuation;cbn;intuition. Qed.

Lemma gateway_nested_temp_call_cont protected continuation :
  gateway_nested_temp protected(call_cont continuation)<->gateway_nested_temp protected continuation.
Proof. induction continuation;cbn;tauto. Qed.

Lemma gateway_keeps_temp_different protected assigned :
  gateway_keeps_temp protected assigned=true ->protected<>assigned.
Proof. unfold gateway_keeps_temp;destruct(ident_eq protected assigned);intuition discriminate. Qed.

Lemma gateway_keeps_set_destination protected destination value parameters :
  gateway_keeps_destination protected destination=true ->
  (set_opttemp destination value parameters)!protected=parameters!protected.
Proof.
  destruct destination;cbn;auto;intro KEEPS;apply PTree.gso.
  intro SAME;apply(gateway_keeps_temp_different _ _ KEEPS);congruence.
Qed.

Lemma gateway_temp_find_label protected label body continuation found rest :
  find_label label body continuation=Some(found,rest) ->
  gateway_nested_temp protected continuation ->gateway_nested_temp protected rest
with gateway_temp_find_label_branches protected label branches continuation found rest :
  find_label_ls label branches continuation=Some(found,rest) ->
  gateway_nested_temp protected continuation ->gateway_nested_temp protected rest.
Proof.
  - destruct body;cbn;intros FOUND NESTED;try discriminate.
    + destruct(find_label label body1(Kseq body2 continuation))as[[statement next]|]eqn:FIRST.
      * inversion FOUND;subst;eapply gateway_temp_find_label;[exact FIRST|exact NESTED].
      * eapply gateway_temp_find_label;[exact FOUND|exact NESTED].
    + destruct(find_label label body1 continuation)as[[statement next]|]eqn:FIRST.
      * inversion FOUND;subst;eapply gateway_temp_find_label;[exact FIRST|exact NESTED].
      * eapply gateway_temp_find_label;[exact FOUND|exact NESTED].
    + destruct(find_label label body1(Kloop1 body1 body2 continuation))as[[statement next]|]eqn:FIRST.
      * inversion FOUND;subst;eapply gateway_temp_find_label;[exact FIRST|exact NESTED].
      * eapply gateway_temp_find_label;[exact FOUND|exact NESTED].
    + eapply gateway_temp_find_label_branches;[exact FOUND|exact NESTED].
    + destruct(ident_eq label l).
      * inversion FOUND;subst;exact NESTED.
      * eapply gateway_temp_find_label;[exact FOUND|exact NESTED].
  - destruct branches;cbn;intros FOUND NESTED;try discriminate.
    destruct(find_label label s(Kseq(seq_of_labeled_statement branches)continuation))as[[statement next]|]eqn:FIRST.
    + inversion FOUND;subst;eapply gateway_temp_find_label;[exact FIRST|exact NESTED].
    + eapply gateway_temp_find_label_branches;[exact FOUND|exact NESTED].
Qed.

Lemma gateway_temp_literal ge protected environment parameters memory expression value target converted :
  gateway_temp_pointer protected expression ->parameters!protected=Some Vnullptr ->
  gateway_pointer_return target ->eval_expr ge environment parameters memory expression value ->
  sem_cast value(typeof expression)(fn_return target)memory=Some converted ->converted=Vnullptr.
Proof.
  intros[pointee[attr EXPRESSION]]NULL[result[result_attr TYPE]]EVALUATION CAST;subst expression.
  assert(VALUE:expression_value ge environment parameters memory(Etempvar protected(Tpointer pointee attr))Vnullptr).
  { apply old_expression_value,value_temp;exact NULL. }
  destruct VALUE as[VALUE UNIQUE];pose proof(UNIQUE _ EVALUATION)as SAME;subst value.
  rewrite TYPE in CAST;cbn in CAST;inversion CAST;reflexivity.
Qed.

Lemma gateway_temp_null_internal protected ge source trace after :
  gateway_temp_null_source protected source ->step2 ge source trace after ->gateway_temp_null_source protected after.
Proof.
  intros GOOD STEP;inversion STEP;subst;
    cbn[gateway_temp_null_source gateway_no_temp_return gateway_must_temp gateway_temp_barrier gateway_nested_temp call_cont]in *.
  all:repeat rewrite andb_true_iff in *.
  all:try solve[intuition discriminate].
  - destruct GOOD as[[TYPE[NULL[STOP[MUST|[KEEPS BARRIER]]]]]|NESTED];[contradiction| |tauto].
    left;split;[exact TYPE|]. split;[|tauto].
    rewrite PTree.gso;[exact NULL|intro SAME;apply(gateway_keeps_temp_different _ _ KEEPS);congruence].
  - destruct GOOD as[[TYPE[NULL[STOP[MUST|[KEEPS BARRIER]]]]]|NESTED];[contradiction| |tauto].
    left;split;[exact TYPE|]. split;[rewrite gateway_keeps_set_destination;assumption|]. tauto.
  - destruct b;tauto.
  - destruct H as[SAME|SAME];subst x;cbn[gateway_must_temp gateway_no_temp_return]in GOOD;intuition discriminate.
  - destruct GOOD as[[TYPE[NULL[STOP[IMPOSSIBLE|[NO_RETURN BARRIER]]]]]|NESTED];
      [contradiction|discriminate|].
    left;apply gateway_nested_temp_call_cont;exact NESTED.
  - destruct GOOD as[[TYPE[NULL[STOP[MUST|[IMPOSSIBLE BARRIER]]]]]|NESTED];[|discriminate|].
    + right;split;[exact STOP|eapply gateway_temp_literal;eassumption].
    + left;apply gateway_nested_temp_call_cont;exact NESTED.
  - destruct GOOD as[[TYPE[NULL[STOP[IMPOSSIBLE|[NO_RETURN BARRIER]]]]]|NESTED];
      [contradiction| |exact(or_introl NESTED)].
    destruct k;cbn in *;contradiction.
  - destruct H as[SAME|SAME];subst x;cbn[gateway_must_temp gateway_no_temp_return]in GOOD;intuition discriminate.
  - right;eapply gateway_temp_find_label;[eassumption|].
    apply gateway_nested_temp_call_cont;intuition discriminate.
  - destruct GOOD as[NESTED|[STOP VALUE]];[|discriminate].
    destruct NESTED as[[TYPE[NULL[KEEPS BARRIER]]]|NESTED].
    + left;split;[exact TYPE|]. split;[rewrite gateway_keeps_set_destination;assumption|].
      split;[apply(gateway_temp_barrier_call_cont protected);exact BARRIER|right;split;[reflexivity|exact BARRIER]].
    + right;exact NESTED.
Qed.

Definition gateway_temp_null_state {World}protected(state:gateway_state World):Prop:=
  match state with gateway_live source _=>gateway_temp_null_source protected source|gateway_dead _ _=>True end.

Lemma gateway_temp_null_step {World Event}(backend:gateway_backend World Event)protected ge before event after :
  gateway_temp_null_state protected before ->gateway_step backend ge before event after ->gateway_temp_null_state protected after.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn in *;try exact I.
  - eapply gateway_temp_null_internal;eassumption.
  - left;exact GOOD.
  - destruct GOOD as[[TYPE[NULL[STOP[MUST|[KEEPS BARRIER]]]]]|NESTED];[contradiction| |tauto].
    left;split;[exact TYPE|]. split;[rewrite gateway_keeps_set_destination;assumption|].
    split;[exact STOP|right;split;[reflexivity|exact BARRIER]].
  - destruct source;exact GOOD.
  - exact GOOD.
Qed.

Theorem gateway_actual_temp_null {World Event}(backend:gateway_backend World Event)protected ge
    source world events value after next :
  gateway_temp_null_source protected source ->
  gateway_steps backend ge(gateway_live source world)events(gateway_live(Returnstate value Kstop after)next) ->value=Vnullptr.
Proof.
  intros INITIAL RUN.
  assert(FINAL:gateway_temp_null_state protected(gateway_live(Returnstate value Kstop after)next)).
  { change(gateway_temp_null_state protected(gateway_live source world))in INITIAL.
    revert INITIAL;induction RUN;intros GOOD;[exact GOOD|apply IHRUN;eapply gateway_temp_null_step;eassumption]. }
  cbn in FINAL;tauto.
Qed.
