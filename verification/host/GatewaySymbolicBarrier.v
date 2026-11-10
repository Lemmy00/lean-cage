(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A retained nonzero source word selects its real cleanup return. *)
From Stdlib Require Import List Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Cop Clight.
Require Import Machine ClightSteps LocalAccess StoreSteps.
From HostGateway Require Import GatewayMachine GatewayReturnBarrier GatewayTempNull GatewayOperations GatewayFrames.
Import ListNotations.

Definition gateway_nonzero_test protected(expression:expr):bool:=
  match expression with
  |Etempvar identifier ty=>if ident_eq identifier protected then
      match classify_bool ty with bool_case_i=>true|_=>false end else false
  |_=>false end.
Definition gateway_symbolic_prefix allowed protected body:=
  gateway_barrier_prefix allowed body&&gateway_no_temp_return protected body.

Fixpoint gateway_symbolic_returns allowed protected(body:statement):Prop:=
  match body with
  |Sreturn _=>True
  |Ssequence first second=>gateway_symbolic_returns allowed protected first \/
    (gateway_symbolic_prefix allowed protected first=true /\gateway_symbolic_returns allowed protected second)
  |Sifthenelse expression yes no=>if gateway_nonzero_test protected expression then
      gateway_symbolic_returns allowed protected yes else
      gateway_symbolic_returns allowed protected yes /\gateway_symbolic_returns allowed protected no
  |_=>False end.

Fixpoint gateway_symbolic_cont allowed protected(continuation:cont):Prop:=
  match continuation with
  |Kseq body rest=>(gateway_symbolic_returns allowed protected body /\call_cont rest=Kstop) \/
    (gateway_symbolic_prefix allowed protected body=true /\gateway_symbolic_cont allowed protected rest)
  |_=>False end.

Definition gateway_symbolic_call owner environment allowed protected word(continuation:cont):Prop:=
  exists destination temporaries rest,continuation=Kcall destination owner environment temporaries rest /\
    temporaries!protected=Some(Vint word) /\gateway_keeps_destination protected destination=true /\
    gateway_symbolic_cont allowed protected rest.

Definition gateway_symbolic_source owner environment allowed protected word denied(source:Clight.state):Prop:=
  match source with
  |State function body continuation actual temporaries _=>
    function=owner /\actual=environment /\temporaries!protected=Some(Vint word) /\call_cont continuation=Kstop /\
    (gateway_symbolic_returns allowed protected body \/
      (gateway_symbolic_prefix allowed protected body=true /\gateway_symbolic_cont allowed protected continuation))
  |Callstate definition _ continuation _=>gateway_barrier_external denied definition /\
      gateway_symbolic_call owner environment allowed protected word continuation
  |Returnstate _ continuation _=>continuation=Kstop \/gateway_symbolic_call owner environment allowed protected word continuation
  end.

Lemma gateway_symbolic_cont_stop allowed protected continuation:
  gateway_symbolic_cont allowed protected continuation->call_cont continuation=Kstop.
Proof. induction continuation;cbn;intuition. Qed.

Lemma gateway_nonzero_test_true ge protected environment temporaries memory expression word value truth:
  gateway_nonzero_test protected expression=true->temporaries!protected=Some(Vint word)->Int.eq word Int.zero=false->
  eval_expr ge environment temporaries memory expression value->bool_val value(typeof expression)memory=Some truth->truth=true.
Proof.
  destruct expression;cbn[gateway_nonzero_test];intros TEST TEMP NONZERO VALUE BOOL;try discriminate.
  destruct(ident_eq i protected);[subst i|discriminate].
  destruct(classify_bool t)eqn:CLASS;try discriminate.
  assert(EXPRESSION:expression_value ge environment temporaries memory(Etempvar protected t)(Vint word))
    by(apply old_expression_value,value_temp;exact TEMP).
  pose proof((proj2 EXPRESSION)value VALUE)as SAME;subst value.
  unfold bool_val in BOOL;cbn[typeof]in BOOL;rewrite CLASS,NONZERO in BOOL;inversion BOOL;reflexivity.
Qed.

Lemma gateway_symbolic_selected ge allowed protected environment temporaries memory expression yes no word value truth:
  gateway_symbolic_returns allowed protected(Sifthenelse expression yes no)->
  temporaries!protected=Some(Vint word)->Int.eq word Int.zero=false->
  eval_expr ge environment temporaries memory expression value->bool_val value(typeof expression)memory=Some truth->
  gateway_symbolic_returns allowed protected(if truth then yes else no).
Proof.
  cbn[gateway_symbolic_returns];destruct(gateway_nonzero_test protected expression)eqn:TEST;
    intros PROFILE TEMP NONZERO VALUE BOOL.
  - pose proof(gateway_nonzero_test_true ge protected environment temporaries memory expression word value truth
      TEST TEMP NONZERO VALUE BOOL)as SAME;subst truth;exact PROFILE.
  - destruct truth;tauto.
Qed.

Lemma gateway_symbolic_source_internal ge owner environment allowed protected word denied source trace after:
  gateway_barrier_bindings ge environment allowed denied->Int.eq word Int.zero=false->
  gateway_symbolic_source owner environment allowed protected word denied source->~gateway_at_primitive source->
  step2 ge source trace after->gateway_symbolic_source owner environment allowed protected word denied after.
Proof.
  intros BINDINGS NONZERO GOOD INTERNAL STEP.
  destruct source as[function body continuation actual temporaries memory|definition arguments continuation memory|
    returned continuation memory].
  - destruct GOOD as[FUNCTION[ENVIRONMENT[TEMP[STOP PROFILE]]]];subst function actual.
    inversion STEP;subst;cbn[gateway_symbolic_source gateway_symbolic_returns gateway_symbolic_prefix gateway_barrier_prefix
      gateway_no_temp_return gateway_symbolic_cont]in *.
    all:unfold gateway_symbolic_prefix in *.
    all:cbn[gateway_barrier_prefix gateway_no_temp_return]in *.
    all:repeat rewrite andb_true_iff in *.
    all:try solve[intuition discriminate].
    all:try solve[exfalso;apply INTERNAL;exact I].
    all:try solve[match goal with CHOICE:?current=Sskip \/?current=Scontinue|-_=>
      destruct CHOICE as[SAME|SAME];subst current;
      cbn[gateway_symbolic_returns gateway_symbolic_prefix gateway_barrier_prefix gateway_no_temp_return]in PROFILE;
      intuition discriminate end].
    all:try solve[match goal with CHOICE:?current=Sskip \/?current=Sbreak|-_=>
      destruct CHOICE as[SAME|SAME];subst current;
      cbn[gateway_symbolic_returns gateway_symbolic_prefix gateway_barrier_prefix gateway_no_temp_return]in PROFILE;
      intuition discriminate end].
    all:try solve[match goal with CALL:is_call_cont ?kont|-_=>destruct kont;cbn in CALL,STOP;intuition discriminate end].
    + destruct PROFILE as[IMPOSSIBLE|[[PLAIN KEEPS]BARRIER]];[contradiction|].
      split;[reflexivity|]. split;[reflexivity|]. split.
      * rewrite PTree.gso;[exact TEMP|intro SAME;apply(gateway_keeps_temp_different _ _ KEEPS);congruence].
      * split;[exact STOP|right;split;[split;reflexivity|exact BARRIER]].
    + destruct PROFILE as[IMPOSSIBLE|[[PLAIN KEEPS]BARRIER]];[contradiction|].
      split.
      * eapply gateway_barrier_function_value;[exact BINDINGS|exact PLAIN|eassumption|eassumption].
      * exists optid,temporaries,continuation;split;[reflexivity|]. split;[exact TEMP|]. split;assumption.
    + destruct PROFILE as[RETURNS|[[YES NO]BARRIER]].
      * split;[reflexivity|]. split;[reflexivity|]. split;[exact TEMP|]. split;[exact STOP|].
        left;eapply gateway_symbolic_selected;eassumption.
      * destruct YES as[PLAIN_YES PLAIN_NO];destruct NO as[KEEP_YES KEEP_NO].
        destruct b;
          (split;[reflexivity|];split;[reflexivity|];split;[exact TEMP|];split;[exact STOP|];right;split;
            [split;assumption|exact BARRIER]).
  - destruct GOOD as[[EXTERNAL DIFFERENT]MARKED].
    destruct EXTERNAL as[external[types[result[convention DEFINITION]]]];subst definition.
    exact(False_rect _ (INTERNAL I)).
  - destruct GOOD as[STOP|[destination[temporaries[rest[CALL[TEMP[KEEPS BARRIER]]]]]]];subst continuation.
    + inversion STEP.
    + inversion STEP;subst;cbn[gateway_symbolic_source gateway_symbolic_returns gateway_symbolic_prefix
        gateway_barrier_prefix gateway_no_temp_return].
      split;[reflexivity|]. split;[reflexivity|]. split.
      * rewrite gateway_keeps_set_destination;assumption.
      * split;[exact(gateway_symbolic_cont_stop allowed protected rest BARRIER)|].
        right;split;[reflexivity|exact BARRIER].
Qed.

Definition gateway_symbolic_state {World}owner environment allowed protected word denied(state:gateway_state World):Prop:=
  match state with gateway_live source _=>gateway_symbolic_source owner environment allowed protected word denied source|
    gateway_dead _ _=>True end.

Lemma gateway_symbolic_step {World Event}(backend:gateway_backend World Event)ge owner environment allowed protected word denied
    before event after:
  gateway_barrier_bindings ge environment allowed denied->Int.eq word Int.zero=false->
  gateway_symbolic_state owner environment allowed protected word denied before->gateway_step backend ge before event after->
  gateway_symbolic_state owner environment allowed protected word denied after.
Proof.
  intros BINDINGS NONZERO GOOD STEP;inversion STEP;subst;cbn in *;try exact I.
  - eapply gateway_symbolic_source_internal;
      [exact BINDINGS|exact NONZERO|exact GOOD|apply gateway_internal_excludes_primitive;exact H|exact H0].
  - right;exact(proj2 GOOD).
  - destruct GOOD as[FUNCTION[ENVIRONMENT[TEMP[STOP[IMPOSSIBLE|[KEEPS BARRIER]]]]]];[contradiction|].
    split;[exact FUNCTION|]. split;[exact ENVIRONMENT|]. split.
    + rewrite gateway_keeps_set_destination;assumption.
    + split;[exact STOP|]. right;split;[reflexivity|exact BARRIER].
  - destruct source;exact GOOD.
  - exact GOOD.
Qed.

Theorem gateway_symbolic_barrier_excludes_call {World Event}(backend:gateway_backend World Event)ge
    owner environment allowed protected word denied body continuation temporaries before world events arguments target_cont after next:
  gateway_barrier_bindings ge environment allowed denied->Int.eq word Int.zero=false->
  temporaries!protected=Some(Vint word)->gateway_symbolic_returns allowed protected body->call_cont continuation=Kstop->
  gateway_steps backend ge(gateway_live(State owner body continuation environment temporaries before)world)events
    (gateway_live(Callstate denied arguments target_cont after)next)->False.
Proof.
  intros BINDINGS NONZERO TEMP RETURNS STOP RUN.
  assert(INITIAL:gateway_symbolic_state owner environment allowed protected word denied
    (gateway_live(State owner body continuation environment temporaries before)world)).
  { split;[reflexivity|]. split;[reflexivity|]. split;[exact TEMP|]. split;[exact STOP|left;exact RETURNS]. }
  assert(FINAL:gateway_symbolic_state owner environment allowed protected word denied
    (gateway_live(Callstate denied arguments target_cont after)next)).
  { revert INITIAL;induction RUN;intro READY;[exact READY|]. apply IHRUN;eapply gateway_symbolic_step;eassumption. }
  exact(proj2(proj1 FINAL)eq_refl).
Qed.
