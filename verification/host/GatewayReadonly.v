(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Read-only source helpers preserve runtime readiness per
   actual step. *)
From Stdlib Require Import List Bool.
From compcert Require Import AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewayMachine GatewayContexts GatewayPure GatewayFrames GatewayCallPath GatewayOperations GatewayFunctionEntry.
Import ListNotations.

Fixpoint gateway_readonly_statement(source:statement):bool:=
  match source with
  |Sskip|Sset _ _|Sbreak|Scontinue|Sreturn _=>true
  |Ssequence first second|Sifthenelse _ first second|Sloop first second=>
    gateway_readonly_statement first&&gateway_readonly_statement second
  |Slabel _ body=>gateway_readonly_statement body
  |_=>false end.
Fixpoint gateway_readonly_cont(continuation:cont):bool:=
  match continuation with
  |Kstop=>true
  |Kseq body rest=>gateway_readonly_statement body&&gateway_readonly_cont rest
  |Kloop1 first second rest|Kloop2 first second rest=>
    gateway_readonly_statement first&&gateway_readonly_statement second&&gateway_readonly_cont rest
  |_=>false end.
Definition gateway_readonly_state(source:Clight.state):Prop:=
  match source with
  |State function body continuation environment _ _=>fn_vars function=[] /\environment=empty_env /\
      gateway_readonly_statement body=true /\gateway_readonly_cont continuation=true
  |Callstate(Internal function)_ Kstop _=>fn_vars function=[] /\gateway_readonly_statement(fn_body function)=true
  |Returnstate _ Kstop _=>True
  |_=>False end.

Lemma gateway_readonly_call_cont continuation :
  gateway_readonly_cont continuation=true ->call_cont continuation=Kstop.
Proof.
  induction continuation;cbn;intro GOOD;try reflexivity;try discriminate;
    repeat rewrite andb_true_iff in GOOD;intuition.
Qed.

Lemma gateway_readonly_replace source memory :
  gateway_readonly_state source ->gateway_readonly_state(gateway_replace_memory source memory).
Proof.
  destruct source as[function body continuation environment temporaries original|
    definition arguments continuation original|value continuation original].
  - cbn;tauto.
  - destruct definition;destruct continuation;cbn;tauto.
  - destruct continuation;cbn;tauto.
Qed.

Lemma gateway_readonly_not_primitive source :
  gateway_readonly_state source ->~gateway_at_primitive source.
Proof.
  destruct source as[function body continuation environment temporaries memory|definition arguments continuation memory|
    value continuation memory];cbn.
  - destruct body;cbn;intros GOOD PRIMITIVE;try contradiction;intuition discriminate.
  - destruct definition;cbn;[destruct continuation|];tauto.
  - destruct continuation;cbn;tauto.
Qed.

Lemma gateway_readonly_source_step ge before trace after :
  gateway_readonly_state before ->step2 ge before trace after ->
  gateway_readonly_state after /\memory_of after=memory_of before.
Proof.
  destruct before as[function body continuation environment temporaries memory|
    definition arguments continuation memory|value continuation memory];intro GOOD.
  - destruct GOOD as[VARS[ENVIRONMENT[BODY CONTINUATION]]];subst environment;intro STEP.
    inversion STEP;subst;cbn[gateway_readonly_statement]in BODY;
      cbn[gateway_readonly_cont]in CONTINUATION;try discriminate.
    all:repeat rewrite andb_true_iff in *.
    all:repeat match goal with H:_ /\_|-_=>destruct H end.
    all:try match goal with FREE:Mem.free_list ?original (blocks_of_env _ empty_env)=Some ?changed|-_=>
      change(Some original=Some changed)in FREE;inversion FREE;subst end.
    all:try match goal with CONT:gateway_readonly_cont ?kont=true|-context[call_cont ?kont]=>
      rewrite(gateway_readonly_call_cont kont CONT)end.
    all:cbn[gateway_readonly_state gateway_readonly_statement gateway_readonly_cont memory_of].
    all:repeat rewrite andb_true_iff.
    all:try destruct b.
    all:try(intuition;fail).
    all:try match goal with CALL:is_call_cont ?kont|-_=>destruct kont;cbn in *;intuition discriminate end.
    all:intuition.
  - destruct definition;[|contradiction].
    destruct continuation;cbn in GOOD;try contradiction.
    destruct GOOD as[VARS BODY];intro STEP;inversion STEP;subst.
    match goal with ENTRY:function_entry2 _ _ _ _ _ _ _|-_=>inversion ENTRY;subst end.
    match goal with VARIABLES:alloc_variables _ _ _ (fn_vars _)_ _|-_=>
      rewrite VARS in VARIABLES;inversion VARIABLES;subst end.
    cbn[gateway_readonly_state gateway_readonly_cont memory_of];intuition.
  - destruct continuation;cbn in GOOD;try contradiction;intro STEP;inversion STEP.
Qed.

Definition gateway_readonly_runtime {World}ready(state:gateway_state World):Prop:=
  match state with
  |gateway_live source world=>gateway_readonly_state source /\ready(memory_of source)world
  |gateway_dead _ _=>True end.

Lemma gateway_readonly_runtime_step {World Event}(backend:gateway_backend World Event)ge ready
    (discipline:gateway_runtime_discipline backend ready)before event after :
  gateway_readonly_runtime ready before ->gateway_step backend ge before event after ->
  gateway_readonly_runtime ready after.
Proof.
  intros GOOD STEP;destruct before as[source world|memory world].
  - destruct GOOD as[PROFILE READY].
    destruct(gateway_nonprimitive_step backend ge _ _ _ _
      (gateway_readonly_not_primitive _ PROFILE)STEP)
      as[[trace[next[EVENT[REAL TARGET]]]]|
        [[changed[next_world[EVENT[INTERFERENCE TARGET]]]]|[EVENT TARGET]]];subst.
    + destruct(gateway_readonly_source_step _ _ _ _ PROFILE REAL)as[NEXT SAME].
      split;[exact NEXT|rewrite SAME;exact READY].
    + split;[apply gateway_readonly_replace;exact PROFILE|].
      rewrite gateway_replace_memory_of;eapply discipline;eassumption.
    + exact I.
  - inversion STEP.
Qed.

Theorem gateway_readonly_run_side {World Event}(backend:gateway_backend World Event)ge ready
    (discipline:gateway_runtime_discipline backend ready)source world events value after next :
  gateway_readonly_state source ->ready(memory_of source)world ->
  gateway_steps backend ge(gateway_live source world)events
    (gateway_live(Returnstate value Kstop after)next) ->ready after next.
Proof.
  intros PROFILE READY RUN.
  assert(INITIAL:gateway_readonly_runtime ready(gateway_live source world))by(split;assumption).
  assert(FINAL:gateway_readonly_runtime ready(gateway_live(Returnstate value Kstop after)next)).
  { revert INITIAL;induction RUN;intro GOOD;[exact GOOD|].
    apply IHRUN;eapply gateway_readonly_runtime_step;eassumption. }
  exact(proj2 FINAL).
Qed.

Lemma gateway_retained_replace ge definition arguments continuation source memory :
  gateway_retained_call_path ge definition arguments continuation source ->
  gateway_retained_call_path ge definition arguments continuation(gateway_replace_memory source memory).
Proof.
  intro SCRIPT;induction SCRIPT;[constructor|].
  eapply gateway_retained_next with(next:=gateway_replace_memory next memory).
  - intro PRIMITIVE;apply H;exact((proj1(gateway_memory_replace_primitive source memory))PRIMITIVE).
  - intro another;rewrite !gateway_memory_replace_twice;apply H0.
  - exact IHSCRIPT.
Qed.

Definition gateway_quiet_event {Event}(event:gateway_event Event):Prop:=
  event=gateway_source E0 \/event=gateway_ambient.

(* The selected call is the first one on this actual source path. Its readiness
   and quiet prefix are produced together with the same memory/world cut. *)
Theorem gateway_retained_call_ready_cut {World Event}(backend:gateway_backend World Event)ge ready
    (discipline:gateway_runtime_discipline backend ready)definition arguments continuation
    source world events returned after next :
  gateway_retained_call_path ge definition arguments continuation source ->ready(memory_of source)world ->
  gateway_steps backend ge(gateway_live source world)events
    (gateway_live(Returnstate returned Kstop after)next) ->
  exists prefix suffix memory called_world,
    events=prefix++suffix /\Forall gateway_quiet_event prefix /\
    gateway_steps backend ge(gateway_live source world)prefix
      (gateway_live(Callstate definition arguments continuation memory)called_world) /\
    ready memory called_world /\
    gateway_steps backend ge(gateway_live(Callstate definition arguments continuation memory)called_world)
      suffix(gateway_live(Returnstate returned Kstop after)next).
Proof.
  revert source world;induction events as[|observed rest IH];intros source world SCRIPT READY RUN.
  - inversion RUN;subst;inversion SCRIPT;subst.
    destruct(H0 after)as[_[REAL _]];cbn in REAL;inversion REAL.
  - inversion SCRIPT;subst.
    + exists[],(observed::rest),memory,world;cbn.
      split;[reflexivity|]. split;[constructor|]. split;[constructor|]. split;assumption.
    + inversion RUN as[|first event middle remaining target HEAD TAIL];subst.
      destruct(gateway_nonprimitive_step backend ge _ _ _ _ H HEAD)
        as[[trace[following[EVENT[REAL TARGET]]]]|
          [[changed[following_world[EVENT[INTERFERENCE TARGET]]]]|[EVENT TARGET]]];subst.
      * destruct(H0(memory_of source))as[INTERNAL[CANON UNIQUE]].
        rewrite gateway_memory_replace_identity in INTERNAL,CANON,UNIQUE.
        destruct(UNIQUE _ _ REAL)as[ZERO SAME];subst.
        destruct(IH(gateway_replace_memory next0(memory_of source))world
          ltac:(apply gateway_retained_replace;assumption)
          ltac:(rewrite gateway_replace_memory_of;exact READY)TAIL)
          as[prefix[suffix[memory[called_world[EVENTS[QUIET[PREFIX[CALLED SUFFIX]]]]]]]].
        exists(gateway_source E0::prefix),suffix,memory,called_world.
        split;[cbn;congruence|]. split;[constructor;[left;reflexivity|exact QUIET]|].
        split;[econstructor;[apply gateway_internal;[exact INTERNAL|exact REAL]|exact PREFIX]|].
        split;assumption.
      * destruct(IH(gateway_replace_memory source changed)following_world
          ltac:(apply gateway_retained_replace;assumption)
          ltac:(rewrite gateway_replace_memory_of;eapply discipline;eassumption)TAIL)
          as[prefix[suffix[memory[called_world[EVENTS[QUIET[PREFIX[CALLED SUFFIX]]]]]]]].
        exists(gateway_ambient::prefix),suffix,memory,called_world.
        split;[cbn;congruence|]. split;[constructor;[right;reflexivity|exact QUIET]|].
        split;[econstructor;[apply gateway_interleaved;exact INTERFERENCE|exact PREFIX]|].
        split;assumption.
      * destruct(gateway_dead_steps _ _ _ _ _ _ TAIL)as[_ BAD];discriminate.
Qed.

Theorem gateway_actual_function_entry_side {World Event}(backend:gateway_backend World Event)ge side
    (discipline:gateway_runtime_discipline backend side)function arguments continuation
    before world events value returned_cont after next :
  side before world ->
  gateway_steps backend ge(gateway_live(Callstate(Internal function)arguments continuation before)world)events
    (gateway_live(Returnstate value returned_cont after)next) ->
  exists prefix suffix entry_memory entry_world environment temporaries allocated,
    events=prefix++gateway_source E0::suffix /\Forall gateway_quiet_event prefix /\
    gateway_steps backend ge
      (gateway_live(Callstate(Internal function)arguments continuation before)world)prefix
      (gateway_live(Callstate(Internal function)arguments continuation entry_memory)entry_world) /\
    side entry_memory entry_world /\
    function_entry2 ge function arguments entry_memory environment temporaries allocated /\
    gateway_steps backend ge
      (gateway_live(State function(fn_body function)continuation environment temporaries allocated)entry_world)
      suffix(gateway_live(Returnstate value returned_cont after)next).
Proof.
  revert before world;induction events as[|observed rest IH];intros before world SIDE RUN.
  - inversion RUN.
  - inversion RUN as[|first event middle remaining target HEAD TAIL];subst.
    destruct(gateway_function_call_step _ _ _ _ _ _ _ _ _ HEAD)
      as[[environment[temporaries[allocated[EVENT[ENTRY TARGET]]]]]|
        [[changed[following[EVENT[INTERFERENCE TARGET]]]]|[EVENT TARGET]]];subst.
    + exists[],rest,before,world,environment,temporaries,allocated;cbn.
      split;[reflexivity|]. split;[constructor|]. split;[constructor|].
      split;[exact SIDE|]. split;assumption.
    + destruct(IH changed following ltac:(eapply discipline;eassumption)TAIL)
        as[prefix[suffix[entry_memory[entry_world[environment[temporaries[allocated
          [EVENTS[QUIET[PREFIX[ENTRY_SIDE[ENTRY BODY]]]]]]]]]]]].
      exists(gateway_ambient::prefix),suffix,entry_memory,entry_world,environment,temporaries,allocated.
      split;[cbn;congruence|]. split;[constructor;[right;reflexivity|exact QUIET]|]. split.
      * econstructor;[apply gateway_interleaved;exact INTERFERENCE|exact PREFIX].
      * split;[exact ENTRY_SIDE|]. split;assumption.
    + destruct(gateway_dead_steps _ _ _ _ _ _ TAIL)as[_ BAD];discriminate.
Qed.

(* §AR-host-boundary.interfaces: A checked pure suffix keeps its actual result, roots and
   event origin. *)
Theorem gateway_pure_path_ready_return {World Event}(backend:gateway_backend World Event)ge side
    (discipline:gateway_runtime_discipline backend side)source expected world events actual after next :
  gateway_pure_path ge source expected ->side(memory_of source)world ->
  gateway_steps backend ge(gateway_live source world)events
    (gateway_live(Returnstate actual Kstop after)next) ->
  actual=expected /\side after next /\Forall gateway_quiet_event events.
Proof.
  revert source world;induction events as[|observed rest IH];intros source world SCRIPT SIDE RUN.
  - inversion RUN;subst;inversion SCRIPT;subst.
    + repeat split;auto;constructor.
    + destruct(H0 after)as[_[REAL _]];cbn in REAL;inversion REAL.
  - assert(INTERNAL:~gateway_at_primitive source).
    { inversion SCRIPT;subst;[cbn;tauto|assumption]. }
    inversion RUN as[|first event middle remaining target HEAD TAIL];subst.
    destruct(gateway_nonprimitive_step backend ge _ _ _ _ INTERNAL HEAD)
      as[[trace[following[EVENT[REAL TARGET]]]]|
        [[changed[following_world[EVENT[INTERFERENCE TARGET]]]]|[EVENT TARGET]]];subst.
    + inversion SCRIPT;subst.
      * inversion REAL.
      * destruct(H0(memory_of source))as[PRIVATE[CANON UNIQUE]].
        rewrite gateway_memory_replace_identity in PRIVATE,CANON,UNIQUE.
        destruct(UNIQUE _ _ REAL)as[ZERO SAME];subst.
        destruct(IH(gateway_replace_memory next0(memory_of source))world
          ltac:(apply gateway_pure_path_replace;assumption)
          ltac:(rewrite gateway_replace_memory_of;exact SIDE)TAIL)as[RESULT[FINAL QUIET]].
        split;[exact RESULT|]. split;[exact FINAL|]. constructor;[left;reflexivity|exact QUIET].
    + destruct(IH(gateway_replace_memory source changed)following_world
        ltac:(apply gateway_pure_path_replace;exact SCRIPT)
        ltac:(rewrite gateway_replace_memory_of;eapply discipline;eassumption)TAIL)
        as[RESULT[FINAL QUIET]].
      split;[exact RESULT|]. split;[exact FINAL|]. constructor;[right;reflexivity|exact QUIET].
    + destruct(gateway_dead_steps _ _ _ _ _ _ TAIL)as[_ BAD];discriminate.
Qed.
