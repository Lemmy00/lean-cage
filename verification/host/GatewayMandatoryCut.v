(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A nonnull result crosses the actual mandatory constructor boundary. *)
From Stdlib Require Import List Bool Classical_Prop.
From compcert Require Import Coqlib Maps AST Values Memory Events Integers Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps LocalAccess StoreSteps.
From HostGateway Require Import GatewayMachine GatewayContexts GatewayTempNull GatewayNullReset GatewayFailurePaths GatewayReturns GatewayFrames.
Import ListNotations.

Fixpoint gateway_mandatory_prefix protected(body:statement):bool:=
  match body with
  |Sskip|Sassign _ _|Sbreak|Scontinue=>true
  |Sset assigned _=>gateway_keeps_temp protected assigned
  |Scall destination _ _|Sbuiltin destination _ _ _=>gateway_keeps_destination protected destination
  |Ssequence first second|Sifthenelse _ first second|Sloop first second=>
    gateway_mandatory_prefix protected first&&gateway_mandatory_prefix protected second
  |Sreturn(Some expression)=>GatewayNullReset.gateway_null_literal expression
  |_=>false end.

Fixpoint gateway_mandatory_body protected marker tail(body:statement)(continuation:cont):Prop:=
  (body=marker /\continuation=tail) \/
  match body with
  |Ssequence first second=>gateway_mandatory_body protected marker tail first(Kseq second continuation) \/
    (gateway_mandatory_prefix protected first=true /\gateway_mandatory_body protected marker tail second continuation)
  |Sifthenelse _ first second=>gateway_mandatory_body protected marker tail first continuation /\
    gateway_mandatory_body protected marker tail second continuation
  |_=>False end.

Fixpoint gateway_mandatory_cont protected marker tail(continuation:cont):Prop:=
  match continuation with
  |Kseq body rest=>gateway_mandatory_body protected marker tail body rest \/
    (gateway_mandatory_prefix protected body=true /\gateway_mandatory_cont protected marker tail rest)
  |Kloop1 body increment rest|Kloop2 body increment rest=>
    gateway_mandatory_prefix protected body=true /\gateway_mandatory_prefix protected increment=true /\
      gateway_mandatory_cont protected marker tail rest
  |_=>False end.

Fixpoint gateway_mandatory_nested owner environment protected expected marker tail(continuation:cont):Prop:=
  match continuation with
  |Kstop=>False
  |Kseq _ rest|Kloop1 _ _ rest|Kloop2 _ _ rest|Kswitch rest=>
    gateway_mandatory_nested owner environment protected expected marker tail rest
  |Kcall destination function locals parameters rest=>
    (function=owner /\locals=environment /\parameters!protected=Some expected /\call_cont rest=Kstop /\
      gateway_keeps_destination protected destination=true /\gateway_mandatory_cont protected marker tail rest) \/
    gateway_mandatory_nested owner environment protected expected marker tail rest
  end.

Definition gateway_mandatory_source owner environment protected expected marker tail(source:Clight.state):Prop:=
  match source with
  |State function body continuation locals parameters _=>
    (function=owner /\locals=environment /\parameters!protected=Some expected /\call_cont continuation=Kstop /\
      (gateway_mandatory_body protected marker tail body continuation \/
       (gateway_mandatory_prefix protected body=true /\gateway_mandatory_cont protected marker tail continuation))) \/
    gateway_mandatory_nested owner environment protected expected marker tail continuation
  |Callstate _ _ continuation _=>gateway_mandatory_nested owner environment protected expected marker tail continuation
  |Returnstate value continuation _=>gateway_mandatory_nested owner environment protected expected marker tail continuation \/
    (continuation=Kstop /\value=Vnullptr)
  end.
Definition gateway_mandatory_at owner environment protected expected marker tail(source:Clight.state):Prop:=
  exists parameters memory,source=State owner marker tail environment parameters memory /\parameters!protected=Some expected.

Lemma gateway_mandatory_nested_call_cont owner environment protected expected marker tail continuation:
  gateway_mandatory_nested owner environment protected expected marker tail(call_cont continuation)<->
  gateway_mandatory_nested owner environment protected expected marker tail continuation.
Proof. induction continuation;cbn;tauto. Qed.

Lemma gateway_mandatory_find_label owner environment protected expected marker tail label body continuation found rest:
  find_label label body continuation=Some(found,rest)->
  gateway_mandatory_nested owner environment protected expected marker tail continuation->
  gateway_mandatory_nested owner environment protected expected marker tail rest
with gateway_mandatory_find_label_branches owner environment protected expected marker tail label branches continuation found rest:
  find_label_ls label branches continuation=Some(found,rest)->
  gateway_mandatory_nested owner environment protected expected marker tail continuation->
  gateway_mandatory_nested owner environment protected expected marker tail rest.
Proof.
  - destruct body;cbn;intros FOUND NESTED;try discriminate.
    + destruct(find_label label body1(Kseq body2 continuation))as[[statement next]|]eqn:FIRST.
      * inversion FOUND;subst;eapply gateway_mandatory_find_label;[exact FIRST|exact NESTED].
      * eapply gateway_mandatory_find_label;[exact FOUND|exact NESTED].
    + destruct(find_label label body1 continuation)as[[statement next]|]eqn:FIRST.
      * inversion FOUND;subst;eapply gateway_mandatory_find_label;[exact FIRST|exact NESTED].
      * eapply gateway_mandatory_find_label;[exact FOUND|exact NESTED].
    + destruct(find_label label body1(Kloop1 body1 body2 continuation))as[[statement next]|]eqn:FIRST.
      * inversion FOUND;subst;eapply gateway_mandatory_find_label;[exact FIRST|exact NESTED].
      * eapply gateway_mandatory_find_label;[exact FOUND|exact NESTED].
    + eapply gateway_mandatory_find_label_branches;[exact FOUND|exact NESTED].
    + destruct(ident_eq label l).
      * inversion FOUND;subst;exact NESTED.
      * eapply gateway_mandatory_find_label;[exact FOUND|exact NESTED].
  - destruct branches;cbn;intros FOUND NESTED;try discriminate.
    destruct(find_label label s(Kseq(seq_of_labeled_statement branches)continuation))as[[statement next]|]eqn:FIRST.
    + inversion FOUND;subst;eapply gateway_mandatory_find_label;[exact FIRST|exact NESTED].
    + eapply gateway_mandatory_find_label_branches;[exact FOUND|exact NESTED].
Qed.

Lemma gateway_mandatory_body_off protected marker tail body continuation:
  ~(body=marker /\continuation=tail)->gateway_mandatory_body protected marker tail body continuation->
  match body with
  |Ssequence first second=>gateway_mandatory_body protected marker tail first(Kseq second continuation) \/
    (gateway_mandatory_prefix protected first=true /\gateway_mandatory_body protected marker tail second continuation)
  |Sifthenelse _ first second=>gateway_mandatory_body protected marker tail first continuation /\
    gateway_mandatory_body protected marker tail second continuation
  |_=>False end.
Proof. destruct body;cbn;tauto. Qed.

Fixpoint gateway_mandatory_sequential(continuation:cont):bool:=
  match continuation with Kstop=>true|Kseq _ rest=>gateway_mandatory_sequential rest|_=>false end.

Lemma gateway_mandatory_body_sequential protected marker tail body continuation:
  gateway_mandatory_sequential tail=true->gateway_mandatory_body protected marker tail body continuation->
  gateway_mandatory_sequential continuation=true.
Proof.
  revert continuation;induction body;cbn;intros continuation TAIL[[_ SAME]|REST];try contradiction;
    try(subst continuation;exact TAIL).
  - destruct REST as[FIRST|[PROFILE SECOND]];[exact(IHbody1 _ TAIL FIRST)|exact(IHbody2 _ TAIL SECOND)].
  - exact(IHbody1 _ TAIL(proj1 REST)).
Qed.

Lemma gateway_mandatory_continue_blocked ge function continuation environment parameters memory:
  gateway_mandatory_sequential continuation=true->
  gateway_blocked_path ge(State function Scontinue continuation environment parameters memory).
Proof.
  induction continuation;cbn;intro SEQUENTIAL;try discriminate.
  - apply gateway_blocked_at;[cbn;tauto|intros;discriminate|intros another trace target STEP;inversion STEP].
  - eapply gateway_blocked_next with(next:=State function Scontinue continuation environment parameters memory).
    + cbn;tauto.
    + intros;apply unchanged_store_edge,edge_continue_seq.
    + apply IHcontinuation;exact SEQUENTIAL.
Qed.

Lemma gateway_mandatory_break_blocked ge function continuation environment parameters memory:
  gateway_mandatory_sequential continuation=true->
  gateway_blocked_path ge(State function Sbreak continuation environment parameters memory).
Proof.
  induction continuation;cbn;intro SEQUENTIAL;try discriminate.
  - apply gateway_blocked_at;[cbn;tauto|intros;discriminate|intros another trace target STEP;inversion STEP].
  - eapply gateway_blocked_next with(next:=State function Sbreak continuation environment parameters memory).
    + cbn;tauto.
    + intros;apply unchanged_store_edge,edge_break_seq.
    + apply IHcontinuation;exact SEQUENTIAL.
Qed.

Lemma gateway_mandatory_internal ge owner environment protected expected marker tail source trace after:
  gateway_pointer_return owner->gateway_mandatory_sequential tail=true->
  gateway_mandatory_source owner environment protected expected marker tail source->
  ~gateway_mandatory_at owner environment protected expected marker tail source->
  step2 ge source trace after->gateway_mandatory_source owner environment protected expected marker tail after \/gateway_blocked_path ge after.
Proof.
  intros POINTER SEQUENTIAL GOOD NOT_AT STEP.
  assert(OFF:forall function body continuation locals parameters memory,
    source=State function body continuation locals parameters memory->function=owner->locals=environment->
    parameters!protected=Some expected->~(body=marker /\continuation=tail)).
  { intros function body continuation locals parameters memory SOURCE FUNCTION ENVIRONMENT VALUE[STATEMENT CONTINUATION];
      subst source function locals body continuation;apply NOT_AT;eexists;eexists;split;[reflexivity|exact VALUE]. }
  inversion STEP;subst;
    cbn[gateway_mandatory_source gateway_mandatory_nested]in *.
  all:try match goal with
    H:(?f = ?outer /\ ?e = ?outer_env /\ (?le ! ?slot) = Some ?raw /\ call_cont ?k = Kstop /\
      (gateway_mandatory_body ?slot ?point ?ending ?s ?k \/_))\/_|-_=>
    destruct H as[[FUNCTION[ENVIRONMENT[VALUE[STOP[MANDATORY|[PROFILE BARRIER]]]]]]|NESTED];
      [pose proof(gateway_mandatory_body_off slot point ending s k
        (OFF f s k e le _ eq_refl FUNCTION ENVIRONMENT VALUE)MANDATORY)as PROFILE;clear MANDATORY|
       |]
    end.
  all:cbn[gateway_mandatory_prefix gateway_mandatory_cont]in *.
  all:repeat rewrite andb_true_iff in *.
  all:try solve[left;intuition discriminate].
  all:try solve[left;destruct b;intuition discriminate].
  all:try solve[match goal with CHOICE:?current=Sskip \/?current=Scontinue|-_=>
    destruct CHOICE as[SAME|SAME];subst current;
    cbn[gateway_mandatory_body gateway_mandatory_prefix]in *;left;intuition discriminate end].
  all:try solve[match goal with CHOICE:?current=Sskip \/?current=Sbreak|-_=>
    destruct CHOICE as[SAME|SAME];subst current;
    cbn[gateway_mandatory_body gateway_mandatory_prefix]in *;left;intuition discriminate end].
  - assert(LOOKUP:(PTree.set id v le)!protected=Some expected).
    { rewrite PTree.gso;[exact VALUE|intro SAME;apply(gateway_keeps_temp_different _ _ PROFILE);congruence]. }
    tauto.
  - rewrite gateway_keeps_set_destination by exact PROFILE;tauto.
  - destruct BARRIER as[MANDATORY|[SKIPPED BARRIER]].
    + right;apply gateway_mandatory_continue_blocked;eapply gateway_mandatory_body_sequential;eassumption.
    + left;cbn in STOP;tauto.
  - destruct BARRIER as[MANDATORY|[SKIPPED BARRIER]].
    + right;apply gateway_mandatory_break_blocked;eapply gateway_mandatory_body_sequential;eassumption.
    + left;cbn in STOP;tauto.
  - left;left;apply gateway_mandatory_nested_call_cont;exact NESTED.
  - left;right;split;[exact STOP|].
    eapply GatewayFailurePaths.gateway_null_literal;
      [apply GatewayNullReset.gateway_null_literal_equal;exact PROFILE|rewrite FUNCTION;exact POINTER|exact H|exact H0].
  - left;left;apply gateway_mandatory_nested_call_cont;exact NESTED.
  - destruct k;cbn in H,BARRIER;contradiction.
  - left;right;eapply gateway_mandatory_find_label;[eassumption|].
    apply gateway_mandatory_nested_call_cont;exact NESTED.
  - destruct GOOD as[NESTED|[STOP VALUE]];[|discriminate].
    destruct NESTED as[[FUNCTION[ENVIRONMENT[VALUE[STOP[KEEPS BARRIER]]]]]|NESTED].
    + left;left;split;[exact FUNCTION|]. split;[exact ENVIRONMENT|].
      split;[rewrite gateway_keeps_set_destination;assumption|]. split;[exact STOP|].
      right;split;[reflexivity|exact BARRIER].
    + left;right;exact NESTED.
Qed.


Lemma gateway_mandatory_live_step {World Event}(backend:gateway_backend World Event)ge
    owner environment protected expected marker tail source world event target next:
  gateway_pointer_return owner->gateway_mandatory_sequential tail=true->
  gateway_mandatory_source owner environment protected expected marker tail source->
  ~gateway_mandatory_at owner environment protected expected marker tail source->
  gateway_step backend ge(gateway_live source world)event(gateway_live target next)->
  gateway_mandatory_source owner environment protected expected marker tail target \/gateway_blocked_path ge target.
Proof.
  intros POINTER SEQUENTIAL GOOD NOT_AT STEP;inversion STEP;subst;cbn in *.
  - eapply gateway_mandatory_internal;eassumption.
  - left;left;exact GOOD.
  - destruct GOOD as[[FUNCTION[ENVIRONMENT[VALUE[STOP[MANDATORY|[PROFILE BARRIER]]]]]]|NESTED].
    + cbn[gateway_mandatory_body]in MANDATORY;destruct MANDATORY as[[SAME CONTINUATION]|IMPOSSIBLE];[|contradiction].
      exfalso;apply NOT_AT;subst function environment0 marker continuation;eexists;eexists;split;[reflexivity|exact VALUE].
    + left;left;split;[exact FUNCTION|]. split;[exact ENVIRONMENT|].
      split;[rewrite gateway_keeps_set_destination;[exact VALUE|exact PROFILE]|]. split;[exact STOP|].
      right;split;[reflexivity|exact BARRIER].
    + left;right;exact NESTED.
  - left;destruct source;exact GOOD.
  - left;exact GOOD.
Qed.

Theorem gateway_mandatory_actual_cut {World Event}(backend:gateway_backend World Event)ge
    owner environment protected expected marker tail source world events value after next:
  gateway_pointer_return owner->gateway_mandatory_sequential tail=true->
  gateway_mandatory_source owner environment protected expected marker tail source->
  gateway_steps backend ge(gateway_live source world)events(gateway_live(Returnstate value Kstop after)next)->
  value<>Vnullptr->
  exists prefix suffix parameters memory current,
    events=prefix++suffix /\parameters!protected=Some expected /\
    gateway_steps backend ge(gateway_live source world)prefix
      (gateway_live(State owner marker tail environment parameters memory)current) /\
    gateway_steps backend ge(gateway_live(State owner marker tail environment parameters memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros POINTER SEQUENTIAL;revert source world.
  induction events as[|event rest IH];intros source world GOOD RUN NONNULL.
  - inversion RUN;subst;cbn in GOOD;destruct GOOD as[IMPOSSIBLE|[STOP VALUE]];[contradiction|contradiction].
  - destruct(Classical_Prop.classic(gateway_mandatory_at owner environment protected expected marker tail source))as[AT|NOT_AT].
    + destruct AT as[parameters[memory[SOURCE VALUE]]];subst source.
      exists[],(event::rest),parameters,memory,world;cbn;split;[reflexivity|]. split;[exact VALUE|]. split;[constructor|exact RUN].
    + inversion RUN as[|first observed middle remaining last HEAD TAIL];subst.
      destruct middle as[target current|memory current].
      * destruct(gateway_mandatory_live_step backend ge owner environment protected expected marker tail source world event target current
          POINTER SEQUENTIAL GOOD NOT_AT HEAD)as[READY|BLOCKED].
        -- destruct(IH target current READY TAIL NONNULL)as[prefix[suffix[parameters[memory[reached[EVENTS[VALUE[PREFIX SUFFIX]]]]]]]].
           exists(event::prefix),suffix,parameters,memory,reached;split;[cbn;congruence|]. split;[exact VALUE|].
           split;[econstructor;[exact HEAD|exact PREFIX]|exact SUFFIX].
        -- exfalso;eapply gateway_blocked_cannot_return;eassumption.
      * destruct(gateway_dead_steps _ _ _ _ _ _ TAIL)as[_ IMPOSSIBLE];discriminate.
Qed.
