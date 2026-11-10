(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Check each helper's actual direct calls before cutting a caller prefix. *)
From Stdlib Require Import List Bool.
From compcert Require Import Coqlib Maps AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewayMachine GatewayReturnBarrier GatewayStackAllocation GatewayFrames GatewayOperations.
Import ListNotations.

Fixpoint gateway_closed_statement(allowed:ident->bool)(body:statement):bool:=
  match body with
  |Sskip|Sassign _ _|Sset _ _|Sreturn _|Sbreak|Scontinue|Sbuiltin _ _ _ _=>true
  |Scall _ function _=>gateway_barrier_callee allowed function
  |Ssequence first second|Sifthenelse _ first second|Sloop first second=>
    gateway_closed_statement allowed first&&gateway_closed_statement allowed second
  |_=>false
  end.

Fixpoint gateway_closed_cont(allowed:ident->bool)(continuation:cont):bool:=
  match continuation with
  |Kstop=>true
  |Kseq body rest=>gateway_closed_statement allowed body&&gateway_closed_cont allowed rest
  |Kloop1 first second rest|Kloop2 first second rest=>
    gateway_closed_statement allowed first&&gateway_closed_statement allowed second&&gateway_closed_cont allowed rest
  |Kswitch rest=>gateway_closed_cont allowed rest
  |Kcall _ _ _ _ _=>false
  end.

Definition gateway_closed_environment(allowed:ident->bool)(environment:env):Prop:=
  forall identifier,allowed identifier=true->environment!identifier=None.
Definition gateway_closed_globals(ge:Clight.genv)(allowed:ident->bool)denied:Prop:=
  forall identifier,allowed identifier=true->exists symbol definition,
    Genv.find_symbol ge identifier=Some symbol /\Genv.find_funct_ptr ge symbol=Some definition /\
    gateway_barrier_external denied definition.

Definition gateway_closed_call owner allowed(continuation:cont):Prop:=
  exists destination environment temporaries rest,
    continuation=Kcall destination owner environment temporaries rest /\
    gateway_closed_environment allowed environment /\gateway_closed_cont allowed rest=true.

Definition gateway_closed_source owner allowed denied(source:Clight.state):Prop:=
  match source with
  |State function body continuation environment _ _=>function=owner /\
    gateway_closed_environment allowed environment /\gateway_closed_statement allowed body=true /\
    gateway_closed_cont allowed continuation=true
  |Callstate definition _ continuation _=>(definition=Internal owner /\continuation=Kstop) \/
    (gateway_barrier_external denied definition /\gateway_closed_call owner allowed continuation)
  |Returnstate _ continuation _=>continuation=Kstop \/gateway_closed_call owner allowed continuation
  end.

Lemma gateway_closed_cont_stop allowed continuation:
  gateway_closed_cont allowed continuation=true->call_cont continuation=Kstop.
Proof.
  induction continuation;cbn;repeat rewrite andb_true_iff;intuition discriminate.
Qed.

Lemma gateway_closed_allocated(ge:Clight.genv)allowed owner before environment after:
  (forall identifier,allowed identifier=true->~In identifier(map fst(fn_vars owner)))->
  alloc_variables ge empty_env before(fn_vars owner)environment after->
  gateway_closed_environment allowed environment.
Proof.
  intros NONLOCAL ALLOC identifier ALLOWED.
  rewrite(gateway_alloc_variables_lookup ge empty_env before(fn_vars owner)environment after identifier ALLOC
    (NONLOCAL identifier ALLOWED));apply PTree.gempty.
Qed.

Lemma gateway_closed_bindings(ge:Clight.genv)allowed denied environment:
  gateway_closed_globals ge allowed denied->gateway_closed_environment allowed environment->
  gateway_barrier_bindings ge environment allowed denied.
Proof.
  intros GLOBALS ENVIRONMENT identifier ALLOWED;split;
    [apply ENVIRONMENT|apply GLOBALS];exact ALLOWED.
Qed.

Lemma gateway_closed_source_internal ge owner allowed denied source trace after:
  gateway_closed_globals ge allowed denied->gateway_closed_statement allowed(fn_body owner)=true->
  (forall identifier,allowed identifier=true->~In identifier(map fst(fn_vars owner)))->
  gateway_closed_source owner allowed denied source->~gateway_at_primitive source->
  step2 ge source trace after->gateway_closed_source owner allowed denied after.
Proof.
  intros GLOBALS BODY NONLOCAL GOOD INTERNAL STEP.
  destruct source as[function body continuation environment temporaries memory|
    definition arguments continuation memory|value continuation memory].
  - destruct GOOD as[FUNCTION[ENVIRONMENT[PROFILE CONT]]];subst function.
    inversion STEP;subst;cbn[gateway_closed_source gateway_closed_statement gateway_closed_cont]in *.
    all:repeat rewrite andb_true_iff in *.
    all:try solve[intuition discriminate].
    all:try solve[destruct b;intuition discriminate].
    all:try solve[match goal with CALL:is_call_cont ?kont|-_=>
      destruct kont;cbn in CALL,CONT;intuition discriminate end].
    all:try solve[left;exact(gateway_closed_cont_stop allowed _ CONT)].
    right;split.
    + eapply gateway_barrier_function_value;
        [apply gateway_closed_bindings;[exact GLOBALS|exact ENVIRONMENT]|exact PROFILE|eassumption|eassumption].
    + exists optid,environment,temporaries,continuation;split;[reflexivity|]. split;assumption.
  - destruct GOOD as[[DEFINITION STOP]|[[EXTERNAL DIFFERENT]CALL]].
    + subst definition continuation;inversion STEP;subst.
      match goal with ENTRY:function_entry2 _ _ _ _ _ _ _|-_=>inversion ENTRY;subst end.
      split;[reflexivity|]. split.
      * eapply gateway_closed_allocated;[exact NONLOCAL|eassumption].
      * split;[exact BODY|reflexivity].
    + destruct EXTERNAL as[external[types[result[convention DEFINITION]]]];subst definition;
        exact(False_rect _ (INTERNAL I)).
  - destruct GOOD as[STOP|[destination[environment[temporaries[rest[CALL[ENVIRONMENT CONT]]]]]]];subst continuation.
    + inversion STEP.
    + inversion STEP;subst;cbn[gateway_closed_source gateway_closed_statement].
      split;[reflexivity|]. split;[exact ENVIRONMENT|]. split;[reflexivity|exact CONT].
Qed.

Definition gateway_closed_state {World}owner allowed denied(state:gateway_state World):Prop:=
  match state with gateway_live source _=>gateway_closed_source owner allowed denied source|gateway_dead _ _=>True end.

Lemma gateway_closed_step {World Event}(backend:gateway_backend World Event)ge owner allowed denied before event after:
  gateway_closed_globals ge allowed denied->gateway_closed_statement allowed(fn_body owner)=true->
  (forall identifier,allowed identifier=true->~In identifier(map fst(fn_vars owner)))->
  gateway_closed_state owner allowed denied before->gateway_step backend ge before event after->
  gateway_closed_state owner allowed denied after.
Proof.
  intros GLOBALS BODY NONLOCAL GOOD STEP;inversion STEP;subst;cbn in *;try exact I.
  - eapply gateway_closed_source_internal;
      [exact GLOBALS|exact BODY|exact NONLOCAL|exact GOOD|apply gateway_internal_excludes_primitive;exact H|exact H0].
  - destruct GOOD as[[FALSE STOP]|[OTHER CALL]];[discriminate|right;exact CALL].
  - destruct GOOD as[FUNCTION[ENVIRONMENT[PROFILE CONT]]].
    split;[exact FUNCTION|]. split;[exact ENVIRONMENT|]. split;[reflexivity|exact CONT].
  - destruct source;exact GOOD.
  - exact GOOD.
Qed.

Theorem gateway_actual_closed_helper {World Event}(backend:gateway_backend World Event)ge owner allowed denied
    arguments before world events target_arguments target_cont after next:
  gateway_closed_globals ge allowed denied->gateway_closed_statement allowed(fn_body owner)=true->
  (forall identifier,allowed identifier=true->~In identifier(map fst(fn_vars owner)))->
  denied<>Internal owner->
  gateway_steps backend ge(gateway_live(Callstate(Internal owner)arguments Kstop before)world)events
    (gateway_live(Callstate denied target_arguments target_cont after)next)->False.
Proof.
  intros GLOBALS BODY NONLOCAL DIFFERENT RUN.
  assert(INITIAL:gateway_closed_state owner allowed denied
    (gateway_live(Callstate(Internal owner)arguments Kstop before)world)).
  { left;split;reflexivity. }
  assert(FINAL:gateway_closed_state owner allowed denied
    (gateway_live(Callstate denied target_arguments target_cont after)next)).
  { revert INITIAL;induction RUN;intro READY;[exact READY|]. apply IHRUN;eapply gateway_closed_step;eassumption. }
  destruct FINAL as[[SAME STOP]|[OTHER CALL]];[apply DIFFERENT;exact SAME|exact(proj2 OTHER eq_refl)].
Qed.
