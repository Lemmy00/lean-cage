(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A selected setup failure cannot reach its original exchange spawn. *)
From Stdlib Require Import List Bool.
From compcert Require Import Coqlib Maps AST Values Memory Events Globalenvs Ctypes Cop Clight.
Require Import Machine ClightSteps LocalAccess StoreSteps.
From HostGateway Require Import GatewayMachine GatewayOperations GatewayFrames.
Import ListNotations.

Definition gateway_barrier_callee(allowed:ident->bool)(expression:expr):bool:=
  match expression with Evar identifier(Tfunction _ _ _)=>allowed identifier|_=>false end.

Fixpoint gateway_barrier_prefix(allowed:ident->bool)(body:statement):bool:=
  match body with
  |Sskip|Sassign _ _|Sset _ _|Sbuiltin _ _ _ _=>true
  |Scall _ function _=>gateway_barrier_callee allowed function
  |Ssequence first second|Sifthenelse _ first second=>
    gateway_barrier_prefix allowed first&&gateway_barrier_prefix allowed second
  |_=>false
  end.

Fixpoint gateway_barrier_returns(allowed:ident->bool)(body:statement):Prop:=
  match body with
  |Sreturn _=>True
  |Ssequence first second=>gateway_barrier_returns allowed first \/
    (gateway_barrier_prefix allowed first=true /\gateway_barrier_returns allowed second)
  |Sifthenelse _ first second=>gateway_barrier_returns allowed first /\gateway_barrier_returns allowed second
  |_=>False
  end.

Fixpoint gateway_barrier_cont(allowed:ident->bool)(continuation:cont):Prop:=
  match continuation with
  |Kseq body rest=>(gateway_barrier_returns allowed body /\call_cont rest=Kstop) \/
    (gateway_barrier_prefix allowed body=true /\gateway_barrier_cont allowed rest)
  |_=>False
  end.

Definition gateway_barrier_external denied(definition:Ctypes.fundef Clight.function):Prop:=
  (exists external types result convention,definition=External external types result convention) /\definition<>denied.

Definition gateway_barrier_bindings(ge:Clight.genv)(environment:env)(allowed:ident->bool)denied:Prop:=
  forall identifier,allowed identifier=true->environment!identifier=None /\
    exists symbol definition,Genv.find_symbol ge identifier=Some symbol /\
      Genv.find_funct_ptr ge symbol=Some definition /\gateway_barrier_external denied definition.

Definition gateway_barrier_call owner environment allowed(continuation:cont):Prop:=
  exists result temporaries rest,
    continuation=Kcall result owner environment temporaries rest /\gateway_barrier_cont allowed rest.

Definition gateway_barrier_source owner environment allowed denied(source:Clight.state):Prop:=
  match source with
  |State function body continuation locals _ _=>
    function=owner /\locals=environment /\call_cont continuation=Kstop /\
    (gateway_barrier_returns allowed body \/
      (gateway_barrier_prefix allowed body=true /\gateway_barrier_cont allowed continuation))
  |Callstate definition _ continuation _=>gateway_barrier_external denied definition /\
      gateway_barrier_call owner environment allowed continuation
  |Returnstate _ continuation _=>continuation=Kstop \/gateway_barrier_call owner environment allowed continuation
  end.

Lemma gateway_barrier_cont_stop allowed continuation:
  gateway_barrier_cont allowed continuation->call_cont continuation=Kstop.
Proof. induction continuation;cbn;intuition. Qed.

Lemma gateway_barrier_function_value ge environment temporaries memory allowed denied
    function value definition:
  gateway_barrier_bindings ge environment allowed denied->gateway_barrier_callee allowed function=true->
  eval_expr ge environment temporaries memory function value->Genv.find_funct ge value=Some definition->
  gateway_barrier_external denied definition.
Proof.
  intros BINDINGS PROFILE EVALUATION CALL.
  destruct function;cbn[gateway_barrier_callee]in PROFILE;try discriminate.
  destruct t;cbn[gateway_barrier_callee]in PROFILE;try discriminate.
  destruct(BINDINGS i PROFILE)as[LOCAL[symbol[actual[SYMBOL[FUNCTION OTHER]]]]].
  assert(VALUE:expression_value ge environment temporaries memory(Evar i(Tfunction l t c))(Vptr symbol Integers.Ptrofs.zero)).
  { apply old_expression_value;eapply value_function;[exact LOCAL|exact SYMBOL|reflexivity]. }
  destruct VALUE as[VALUE UNIQUE];pose proof(UNIQUE _ EVALUATION)as SAME;subst value.
  cbn in CALL;rewrite FUNCTION in CALL;inversion CALL;subst definition;exact OTHER.
Qed.

Lemma gateway_barrier_source_internal ge owner environment allowed denied source trace after:
  gateway_barrier_bindings ge environment allowed denied->
  gateway_barrier_source owner environment allowed denied source->~gateway_at_primitive source->
  step2 ge source trace after->gateway_barrier_source owner environment allowed denied after.
Proof.
  intros BINDINGS GOOD INTERNAL STEP.
  destruct source as[function body continuation locals temporaries memory|definition arguments continuation memory|
    returned continuation memory].
  - destruct GOOD as[FUNCTION[ENVIRONMENT[STOP PROFILE]]];subst function locals.
    inversion STEP;subst;cbn[gateway_barrier_source gateway_barrier_returns gateway_barrier_prefix gateway_barrier_cont]in *.
    all:repeat rewrite andb_true_iff in *.
    all:try solve[intuition discriminate].
    all:try solve[destruct b;intuition discriminate].
    all:try solve[match goal with CHOICE:?current=Sskip \/?current=Scontinue|-_=>
      destruct CHOICE as[SAME|SAME];subst current;
      cbn[gateway_barrier_returns gateway_barrier_prefix]in PROFILE;intuition discriminate end].
    all:try solve[match goal with CHOICE:?current=Sskip \/?current=Sbreak|-_=>
      destruct CHOICE as[SAME|SAME];subst current;
      cbn[gateway_barrier_returns gateway_barrier_prefix]in PROFILE;intuition discriminate end].
    all:try solve[match goal with CALL:is_call_cont ?kont|-_=>
      destruct kont;cbn in CALL,STOP;intuition discriminate end].
    destruct PROFILE as[IMPOSSIBLE|[ALLOWED BARRIER]];[contradiction|]. split.
    + eapply gateway_barrier_function_value;[exact BINDINGS|exact ALLOWED|eassumption|eassumption].
    + exists optid,temporaries,continuation;split;[reflexivity|exact BARRIER].
  - destruct GOOD as[[EXTERNAL DIFFERENT]MARKED];destruct EXTERNAL as[external[types[result[convention DEFINITION]]]];
      subst definition;exact(False_rect _ (INTERNAL I)).
  - destruct GOOD as[STOP|[result[temporaries[rest[CALL BARRIER]]]]];subst continuation.
    + inversion STEP.
    + inversion STEP;subst;cbn[gateway_barrier_source gateway_barrier_returns gateway_barrier_prefix].
      split;[reflexivity|]. split;[reflexivity|]. split;[exact(gateway_barrier_cont_stop allowed rest BARRIER)|].
      right;split;[reflexivity|exact BARRIER].
Qed.

Definition gateway_barrier_state {World}owner environment allowed denied(state:gateway_state World):Prop:=
  match state with gateway_live source _=>gateway_barrier_source owner environment allowed denied source|gateway_dead _ _=>True end.

Lemma gateway_internal_excludes_primitive source:
  internal_state source->~gateway_at_primitive source.
Proof.
  destruct source as[function body continuation environment temporaries memory|definition arguments continuation memory|
    value continuation memory];cbn;[destruct body|destruct definition|];tauto.
Qed.

Lemma gateway_barrier_step {World Event}(backend:gateway_backend World Event)ge owner environment allowed denied before event after:
  gateway_barrier_bindings ge environment allowed denied->gateway_barrier_state owner environment allowed denied before->
  gateway_step backend ge before event after->gateway_barrier_state owner environment allowed denied after.
Proof.
  intros BINDINGS GOOD STEP;inversion STEP;subst;cbn in *;try exact I.
  - eapply gateway_barrier_source_internal;
      [exact BINDINGS|exact GOOD|apply gateway_internal_excludes_primitive;exact H|exact H0].
  - right;exact(proj2 GOOD).
  - destruct GOOD as[FUNCTION[ENVIRONMENT[STOP[IMPOSSIBLE|[PREFIX BARRIER]]]]];[contradiction|].
    split;[exact FUNCTION|]. split;[exact ENVIRONMENT|]. split;[exact STOP|].
    right;split;[reflexivity|exact BARRIER].
  - destruct source;exact GOOD.
  - exact GOOD.
Qed.

Theorem gateway_return_barrier_excludes_call {World Event}(backend:gateway_backend World Event)ge
    owner environment allowed denied body continuation temporaries before world events arguments target_cont after next:
  gateway_barrier_bindings ge environment allowed denied->gateway_barrier_returns allowed body->
  call_cont continuation=Kstop->
  gateway_steps backend ge
    (gateway_live(State owner body continuation environment temporaries before)world)events
    (gateway_live(Callstate denied arguments target_cont after)next)->False.
Proof.
  intros BINDINGS RETURNS STOP RUN.
  assert(INITIAL:gateway_barrier_state owner environment allowed denied
    (gateway_live(State owner body continuation environment temporaries before)world)).
  { split;[reflexivity|]. split;[reflexivity|]. split;[exact STOP|left;exact RETURNS]. }
  assert(FINAL:gateway_barrier_state owner environment allowed denied(gateway_live(Callstate denied arguments target_cont after)next)).
  { revert INITIAL;induction RUN;intro READY;[exact READY|]. apply IHRUN;eapply gateway_barrier_step;eassumption. }
  exact(proj2(proj1 FINAL)eq_refl).
Qed.
