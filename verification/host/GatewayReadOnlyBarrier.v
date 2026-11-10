(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A selected source return excludes all own assignments, including on SDK loss. *)
From Stdlib Require Import List Bool.
From compcert Require Import Coqlib Maps AST Values Memory Events Globalenvs Ctypes Cop Clight.
Require Import Machine ClightSteps LocalAccess StoreSteps.
From HostGateway Require Import GatewayMachine GatewayOperations GatewayFrames GatewayNoStoreControl GatewayFramedRuntime.
Import ListNotations.

Definition gateway_readonly_callee(allowed:ident->bool)(expression:expr):bool:=
  match expression with Evar identifier(Tfunction _ _ _)=>allowed identifier|_=>false end.

Fixpoint gateway_readonly_prefix(allowed:ident->bool)(body:statement):bool:=
  match body with
  |Sskip|Sset _ _=>true
  |Scall _ function _=>gateway_readonly_callee allowed function
  |Ssequence first second|Sifthenelse _ first second=>
    gateway_readonly_prefix allowed first&&gateway_readonly_prefix allowed second
  |_=>false
  end.

Fixpoint gateway_readonly_returns(allowed:ident->bool)(body:statement):Prop:=
  match body with
  |Sreturn _=>True
  |Ssequence first second=>gateway_readonly_returns allowed first \/
    (gateway_readonly_prefix allowed first=true /\gateway_readonly_returns allowed second)
  |Sifthenelse _ first second=>gateway_readonly_returns allowed first /\gateway_readonly_returns allowed second
  |_=>False
  end.

Fixpoint gateway_readonly_cont(allowed:ident->bool)(continuation:cont):Prop:=
  match continuation with
  |Kseq body rest=>(gateway_readonly_returns allowed body /\call_cont rest=Kstop) \/
    (gateway_readonly_prefix allowed body=true /\gateway_readonly_cont allowed rest)
  |_=>False
  end.

Definition gateway_readonly_external denied(definition:Ctypes.fundef Clight.function):Prop:=
  (exists external types result convention,definition=External external types result convention) /\definition<>denied.

Definition gateway_readonly_bindings(ge:Clight.genv)(environment:env)(allowed:ident->bool)denied:Prop:=
  forall identifier,allowed identifier=true->environment!identifier=None /\
    exists symbol definition,Genv.find_symbol ge identifier=Some symbol /\
      Genv.find_funct_ptr ge symbol=Some definition /\gateway_readonly_external denied definition.

Definition gateway_readonly_call owner environment allowed(continuation:cont):Prop:=
  exists result temporaries rest,
    continuation=Kcall result owner environment temporaries rest /\gateway_readonly_cont allowed rest.

Definition gateway_readonly_source owner environment allowed denied(source:Clight.state):Prop:=
  match source with
  |State function body continuation locals _ _=>
    function=owner /\locals=environment /\call_cont continuation=Kstop /\
    (gateway_readonly_returns allowed body \/
      (gateway_readonly_prefix allowed body=true /\gateway_readonly_cont allowed continuation))
  |Callstate definition _ continuation _=>gateway_readonly_external denied definition /\
      gateway_readonly_call owner environment allowed continuation
  |Returnstate _ continuation _=>continuation=Kstop \/gateway_readonly_call owner environment allowed continuation
  end.

Lemma gateway_readonly_cont_stop allowed continuation:
  gateway_readonly_cont allowed continuation->call_cont continuation=Kstop.
Proof. induction continuation;cbn;intuition. Qed.

Lemma gateway_readonly_function_value ge environment temporaries memory allowed denied
    function value definition:
  gateway_readonly_bindings ge environment allowed denied->gateway_readonly_callee allowed function=true->
  eval_expr ge environment temporaries memory function value->Genv.find_funct ge value=Some definition->
  gateway_readonly_external denied definition.
Proof.
  intros BINDINGS PROFILE EVALUATION CALL.
  destruct function;cbn[gateway_readonly_callee]in PROFILE;try discriminate.
  destruct t;cbn[gateway_readonly_callee]in PROFILE;try discriminate.
  destruct(BINDINGS i PROFILE)as[LOCAL[symbol[actual[SYMBOL[FUNCTION OTHER]]]]].
  assert(VALUE:expression_value ge environment temporaries memory(Evar i(Tfunction l t c))(Vptr symbol Integers.Ptrofs.zero)).
  { apply old_expression_value;eapply value_function;[exact LOCAL|exact SYMBOL|reflexivity]. }
  destruct VALUE as[VALUE UNIQUE];pose proof(UNIQUE _ EVALUATION)as SAME;subst value.
  cbn in CALL;rewrite FUNCTION in CALL;inversion CALL;subst definition;exact OTHER.
Qed.

Lemma gateway_readonly_source_internal ge owner environment allowed denied source trace after:
  gateway_readonly_bindings ge environment allowed denied->
  gateway_readonly_source owner environment allowed denied source->~gateway_at_primitive source->
  step2 ge source trace after->gateway_readonly_source owner environment allowed denied after.
Proof.
  intros BINDINGS GOOD INTERNAL STEP.
  destruct source as[function body continuation locals temporaries memory|definition arguments continuation memory|
    returned continuation memory].
  - destruct GOOD as[FUNCTION[ENVIRONMENT[STOP PROFILE]]];subst function locals.
    inversion STEP;subst;cbn[gateway_readonly_source gateway_readonly_returns gateway_readonly_prefix gateway_readonly_cont]in *.
    all:repeat rewrite andb_true_iff in *.
    all:try solve[intuition discriminate].
    all:try solve[destruct b;intuition discriminate].
    all:try solve[match goal with CHOICE:?current=Sskip \/?current=Scontinue|-_=>
      destruct CHOICE as[SAME|SAME];subst current;
      cbn[gateway_readonly_returns gateway_readonly_prefix]in PROFILE;intuition discriminate end].
    all:try solve[match goal with CHOICE:?current=Sskip \/?current=Sbreak|-_=>
      destruct CHOICE as[SAME|SAME];subst current;
      cbn[gateway_readonly_returns gateway_readonly_prefix]in PROFILE;intuition discriminate end].
    all:try solve[match goal with CALL:is_call_cont ?kont|-_=>
      destruct kont;cbn in CALL,STOP;intuition discriminate end].
    destruct PROFILE as[IMPOSSIBLE|[ALLOWED BARRIER]];[contradiction|]. split.
    + eapply gateway_readonly_function_value;[exact BINDINGS|exact ALLOWED|eassumption|eassumption].
    + exists optid,temporaries,continuation;split;[reflexivity|exact BARRIER].
  - destruct GOOD as[[EXTERNAL DIFFERENT]MARKED];destruct EXTERNAL as[external[types[result[convention DEFINITION]]]];
      subst definition;exact(False_rect _ (INTERNAL I)).
  - destruct GOOD as[STOP|[result[temporaries[rest[CALL BARRIER]]]]];subst continuation.
    + inversion STEP.
    + inversion STEP;subst;cbn[gateway_readonly_source gateway_readonly_returns gateway_readonly_prefix].
      split;[reflexivity|]. split;[reflexivity|]. split;[exact(gateway_readonly_cont_stop allowed rest BARRIER)|].
      right;split;[reflexivity|exact BARRIER].
Qed.


Lemma gateway_readonly_replace owner environment allowed denied source memory :
  gateway_readonly_source owner environment allowed denied source ->
  gateway_readonly_source owner environment allowed denied (gateway_replace_memory source memory).
Proof. destruct source; exact (fun x => x). Qed.

Lemma gateway_readonly_no_assignment owner environment allowed denied source :
  gateway_readonly_source owner environment allowed denied source -> gateway_not_assignment source.
Proof.
  destruct source as [function body continuation locals parameters memory |definition arguments continuation memory |
    value continuation memory]; cbn [gateway_not_assignment]; try tauto.
  destruct body; cbn [gateway_not_assignment]; try tauto.
  intros [_ [_ [_ [IMPOSSIBLE |[IMPOSSIBLE _]]]]]; cbn in IMPOSSIBLE; contradiction || discriminate.
Qed.

Lemma gateway_readonly_state_internal owner environment allowed denied function body continuation locals parameters memory :
  gateway_readonly_source owner environment allowed denied (State function body continuation locals parameters memory) ->
  ~ gateway_at_primitive (State function body continuation locals parameters memory).
Proof.
  intros [_ [_ [_ PROFILE]]]; destruct body; cbn [gateway_at_primitive]; try tauto.
  destruct PROFILE as [IMPOSSIBLE |[IMPOSSIBLE _]]; cbn in IMPOSSIBLE; contradiction || discriminate.
Qed.

Theorem gateway_readonly_source_certificate {World Event} (backend : gateway_backend World Event)
    ge owner environment allowed denied source :
  gateway_readonly_bindings ge environment allowed denied ->
  gateway_readonly_source owner environment allowed denied source ->
  gateway_nostore_control backend ge (fun _ _ => True) source.
Proof.
  revert source; cofix REC; intros source BINDINGS READY.
  assert (CLOSED : gateway_ambient_closed backend (fun _ _ => True))
    by (unfold gateway_ambient_closed; intros; exact I).
  destruct source as [function body continuation locals parameters memory |definition arguments continuation memory |
    value continuation memory].
  - apply gateway_nostore_source; [exact CLOSED |eapply gateway_readonly_state_internal; exact READY |
      eapply gateway_readonly_no_assignment; exact READY |].
    intros before world observed target _ STEP; exists (fun _ _ => True); split; [exact I |].
    apply REC; [exact BINDINGS |].
    eapply (gateway_readonly_source_internal ge owner environment allowed denied
      (State function body continuation locals parameters before)); [exact BINDINGS | | |exact STEP].
    + exact READY.
    + exact (gateway_readonly_state_internal owner environment allowed denied
        function body continuation locals parameters before READY).
  - destruct READY as [[EXTERNAL DIFFERENT] CONTINUATION].
    destruct EXTERNAL as [ef [types [result [convention SAME]]]]; subst definition.
    apply gateway_nostore_external; [exact CLOSED |].
    intros before world value after next observed _ OPERATION.
    exists (fun _ _ => True); split; [exact I |].
    apply REC; [exact BINDINGS |right; exact CONTINUATION].
  - apply gateway_nostore_source; [exact CLOSED |cbn; tauto |exact I |].
    intros before world observed target _ STEP; exists (fun _ _ => True); split; [exact I |].
    apply REC; [exact BINDINGS |].
    eapply (gateway_readonly_source_internal ge owner environment allowed denied
      (Returnstate value continuation before)); [exact BINDINGS | |cbn; tauto |exact STEP].
    exact READY.
Qed.

Theorem gateway_readonly_selected_certificate {World Event} (backend : gateway_backend World Event)
    ge owner environment allowed denied body continuation parameters memory :
  gateway_readonly_bindings ge environment allowed denied -> gateway_readonly_returns allowed body ->
  call_cont continuation = Kstop ->
  gateway_nostore_control backend ge (fun _ _ => True)
    (State owner body continuation environment parameters memory).
Proof.
  intros BINDINGS RETURNS STOP; eapply gateway_readonly_source_certificate; [exact BINDINGS |].
  split; [reflexivity |]. split; [reflexivity |]. split; [exact STOP |left; exact RETURNS].
Qed.
