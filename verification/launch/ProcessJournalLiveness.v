(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.origin: Derive live prefixes from the same strictly imported kernel journal. *)
From Stdlib Require Import Arith List Lia.
From LeanImport Require Import Lean.
From EntryProcess Require Import ProcessImport ProcessJournal.
From EntryNamespace Require Import NamespacePhysical.
Import ListNotations.
Local Close Scope lean_scope.

Lemma journal_strict_trans(A:Type)(first middle last:A):
  Lean.eq first middle ->Lean.eq middle last ->Lean.eq first last.
Proof. intros ONE TWO;destruct ONE;exact TWO. Qed.

Lemma journal_strict_transport(A:Type)(P:A->SProp)left right:
  Lean.eq left right ->P left ->P right.
Proof. intros SAME FIRST;destruct SAME;exact FIRST. Qed.

Lemma journal_eq_test(A:Type)(test:A->bool)first last:
  test first=true ->test last=false ->Lean.eq first last ->Lean.sEmpty.
Proof.
  intros FIRST LAST SAME.
  set(P:=fun value=>if test value then Lean.eq ProcessImport.Bool_true ProcessImport.Bool_true else Lean.sEmpty).
  assert(START:P first)by(unfold P;rewrite FIRST;constructor).
  pose proof(journal_strict_transport A P _ _ SAME START)as FINISH.
  unfold P in FINISH;rewrite LAST in FINISH;exact FINISH.
Qed.

Lemma journal_strict_sym(A:Type)(first last:A):Lean.eq first last ->Lean.eq last first.
Proof. intro SAME;destruct SAME;constructor. Qed.

Lemma journal_nat_contradiction first last:
  nat_of_Nat first<>nat_of_Nat last ->Lean.eq first last ->Lean.sEmpty.
Proof.
  intros DIFFERENT SAME.
  eapply(journal_eq_test Lean.Nat(fun value=>Nat.eqb(nat_of_Nat first)(nat_of_Nat value))first last).
  - apply Nat.eqb_refl.
  - apply Nat.eqb_neq;exact DIFFERENT.
  - exact SAME.
Qed.

Lemma journal_tracer_contradiction tracer actor:
  Lean.eq tracer(Option_none_inst1 LeanCage_Entry_ProcessIdentity) ->
  Lean.eq tracer(Option_some_inst1 LeanCage_Entry_ProcessIdentity actor) ->Lean.sEmpty.
Proof.
  intros DETACHED TRACED.
  assert(BAD:Lean.eq(Option_none_inst1 LeanCage_Entry_ProcessIdentity)
    (Option_some_inst1 LeanCage_Entry_ProcessIdentity actor))by(destruct DETACHED;exact TRACED).
  eapply(journal_eq_test _ (fun value=>match value with Option_none_inst1 _=>true|Option_some_inst1 _ _=>false end)
    (Option_none_inst1 LeanCage_Entry_ProcessIdentity)(Option_some_inst1 LeanCage_Entry_ProcessIdentity actor));
    [reflexivity|reflexivity|exact BAD].
Qed.

Lemma journal_requests_append first rest:
  LeanCage_Entry_CallerRequestsAllowed first ->LeanCage_Entry_CallerRequestsAllowed rest ->
  LeanCage_Entry_CallerRequestsAllowed(HAppend_hAppend_inst7(List_inst1 Lean.Nat)(List_inst1 Lean.Nat)
    (List_inst1 Lean.Nat)(instHAppendOfAppend_inst1(List_inst1 Lean.Nat)(List_instAppend_inst1 Lean.Nat))first rest).
Proof.
  intros FIRST LAST;induction first;cbn in *;[exact LAST|].
  destruct FIRST as[HEAD TAIL];constructor;[exact HEAD|apply IHfirst;exact TAIL].
Qed.

Theorem journal_step_context_safe mayTrace owner child history before action after:
  LeanCage_Entry_CallerPhysical_ContextSafe owner before ->
  LeanCage_Entry_CallerPhysical_SourceUse mayTrace history before action ->
  LeanCage_Entry_CallerPhysical_Step mayTrace owner child before action after ->
  LeanCage_Entry_CallerPhysical_ContextSafe owner after.
Proof.
  intros SAFE SOURCE STEP.
  destruct STEP as[|after TRACER OPTIONS ISSUED PARENT ALIVE SPACE GROUP|after UNSAFE|
    UNTRACED PARENT ALIVE|actor value TRACED ALIVE|actor request value TRACED ALIVE OPCODE|
    actor request value PERMISSION UNTRACED ALIVE OPCODE|after actor request value PERMISSION OPCODE|
    actor request value PERMISSION UNTRACED|actor request value|group| | |];try exact SAFE.
  - destruct SAFE as[DETACHED|[OWNED[CHECKED ALLOWED]]].
    + left;eapply journal_strict_trans;[exact TRACER|exact DETACHED].
    + right;constructor;[eapply journal_strict_trans;[exact TRACER|exact OWNED]|].
      destruct ISSUED,OPTIONS;constructor;assumption.
  - destruct(UNSAFE SAFE).
  - right;constructor;[constructor|]. constructor;[constructor|left;constructor].
  - destruct(SOURCE ltac:(right;exact TRACED))as[MEMBER[REQUEST PAYLOAD]].
    destruct SAFE as[DETACHED|[OWNED[CHECKED ALLOWED]]].
    + destruct(journal_tracer_contradiction _ _ DETACHED TRACED).
    + right;constructor;[exact OWNED|]. constructor.
      * apply journal_requests_append;[exact CHECKED|]. constructor;[exact REQUEST|constructor].
      * right;apply PAYLOAD;constructor.
  - destruct(SOURCE ltac:(right;exact TRACED))as[MEMBER[REQUEST PAYLOAD]].
    destruct SAFE as[DETACHED|[OWNED[CHECKED ALLOWED]]].
    + destruct(journal_tracer_contradiction _ _ DETACHED TRACED).
    + right;constructor;[exact OWNED|]. constructor;[|exact ALLOWED].
      apply journal_requests_append;[exact CHECKED|]. constructor;[exact REQUEST|constructor].
  - destruct(SOURCE ltac:(left;exact PERMISSION))as[MEMBER[REQUEST PAYLOAD]].
    destruct OPCODE as[SAME|SAME].
    + assert(LITERAL:LeanCage_Entry_NonSubstitutingRequest(Nat_of_nat 16))
        by(exact(journal_strict_transport _ LeanCage_Entry_NonSubstitutingRequest _ _ SAME REQUEST)).
      destruct LITERAL as[BAD|[BAD|BAD]];
        match type of BAD with Lean.eq ?first ?last=>
          pose proof(journal_nat_contradiction first last ltac:(vm_compute;discriminate)BAD)as IMPOSSIBLE end;
        destruct IMPOSSIBLE.
    + assert(LITERAL:LeanCage_Entry_NonSubstitutingRequest(Nat_of_nat 16902))
        by(exact(journal_strict_transport _ LeanCage_Entry_NonSubstitutingRequest _ _ SAME REQUEST)).
      destruct LITERAL as[BAD|[BAD|BAD]];
        match type of BAD with Lean.eq ?first ?last=>
          pose proof(journal_nat_contradiction first last ltac:(vm_compute;discriminate)BAD)as IMPOSSIBLE end;
        destruct IMPOSSIBLE.
  - destruct(SOURCE PERMISSION)as[MEMBER[REQUEST PAYLOAD]];destruct(OPCODE REQUEST).
  - left;constructor.
Qed.

Lemma journal_false_true:
  Lean.eq ProcessImport.Bool_false ProcessImport.Bool_true ->Lean.sEmpty.
Proof.
  intro SAME;eapply(journal_eq_test _ (fun value=>match value with ProcessImport.Bool_false=>true|ProcessImport.Bool_true=>false end)
    ProcessImport.Bool_false ProcessImport.Bool_true);[reflexivity|reflexivity|exact SAME].
Qed.

Theorem journal_step_parent_backward mayTrace owner child history before action after:
  LeanCage_Entry_CallerPhysical_ContextSafe owner before ->
  LeanCage_Entry_CallerPhysical_SourceUse mayTrace history before action ->
  LeanCage_Entry_CallerPhysical_Step mayTrace owner child before action after ->
  Lean.eq(LeanCage_Entry_CallerPhysical_Context_parentAlive after)ProcessImport.Bool_true ->
  Lean.eq(LeanCage_Entry_CallerPhysical_Context_parentAlive before)ProcessImport.Bool_true.
Proof.
  intros SAFE SOURCE STEP LIVE;destruct STEP;try exact LIVE.
  - match goal with PARENT:Lean.eq(LeanCage_Entry_CallerPhysical_Context_parentAlive _)
      (LeanCage_Entry_CallerPhysical_Context_parentAlive _)|-_=>
      eapply journal_strict_trans;[apply journal_strict_sym;exact PARENT|exact LIVE]end.
  - match goal with UNSAFE:Not(LeanCage_Entry_CallerPhysical_ContextSafe _ _)|-_=>destruct(UNSAFE SAFE)end.
  - match goal with PERMISSION:Lean.Or _ _,DENIED:Not(LeanCage_Entry_NonSubstitutingRequest _)|-_=>
      destruct(SOURCE PERMISSION)as[MEMBER[REQUEST PAYLOAD]];destruct(DENIED REQUEST)end.
  - destruct(journal_false_true LIVE).
  - destruct(journal_false_true LIVE).
Qed.

Theorem journal_request_parent_after mayTrace owner child history before actor request options after:
  LeanCage_Entry_CallerPhysical_SourceUse mayTrace history before
    (LeanCage_Entry_CallerPhysical_Action_request actor request options) ->
  LeanCage_Entry_CallerPhysical_Step mayTrace owner child before
    (LeanCage_Entry_CallerPhysical_Action_request actor request options)after ->
  Lean.eq(LeanCage_Entry_CallerPhysical_Context_parentAlive before)ProcessImport.Bool_true ->
  Lean.eq(LeanCage_Entry_CallerPhysical_Context_parentAlive after)ProcessImport.Bool_true.
Proof.
  intros SOURCE STEP LIVE;inversion STEP;subst;try exact LIVE.
  match goal with PERMISSION:Lean.Or _ _,DENIED:Not(LeanCage_Entry_NonSubstitutingRequest _)|-_=>
    destruct(SOURCE PERMISSION)as[MEMBER[REQUEST PAYLOAD]];destruct(DENIED REQUEST)end.
Qed.

Theorem journal_selected_operation mayTrace owner child history ticks before after offset tick:
  LeanCage_Entry_CallerPhysical_Journal mayTrace owner child history before(tick_values ticks)after ->
  nth_error ticks offset=Some tick ->
  Lean.And(LeanCage_Entry_CallerPhysical_SourceUse mayTrace history
      (LeanCage_Entry_CallerPhysical_Tick_before tick)(LeanCage_Entry_CallerPhysical_Tick_action tick))
    (LeanCage_Entry_CallerPhysical_Step mayTrace owner child
      (LeanCage_Entry_CallerPhysical_Tick_before tick)(LeanCage_Entry_CallerPhysical_Tick_action tick)
      (LeanCage_Entry_CallerPhysical_Tick_after tick)).
Proof.
  revert before offset;induction ticks as[|head ticks IH];intros before[|offset]RUN SELECTED;try discriminate.
  - inversion RUN as[context|current remaining final SOURCE STEP REST];subst.
    inversion SELECTED;subst;constructor;assumption.
  - inversion RUN as[context|current remaining final SOURCE STEP REST];subst.
    eapply IH;[exact REST|exact SELECTED].
Qed.

Theorem journal_selected_request_live mayTrace owner child history ticks before after offset tick actor request options:
  LeanCage_Entry_CallerPhysical_Journal mayTrace owner child history before(tick_values ticks)after ->
  nth_error ticks offset=Some tick ->
  LeanCage_Entry_CallerPhysical_Tick_action tick=LeanCage_Entry_CallerPhysical_Action_request actor request options ->
  Lean.eq(LeanCage_Entry_CallerPhysical_Context_parentAlive(LeanCage_Entry_CallerPhysical_Tick_before tick))ProcessImport.Bool_true ->
  Lean.eq(LeanCage_Entry_CallerPhysical_Context_parentAlive(LeanCage_Entry_CallerPhysical_Tick_after tick))ProcessImport.Bool_true.
Proof.
  intros RUN SELECTED ACTION LIVE.
  destruct(journal_selected_operation _ _ _ _ _ _ _ _ _ RUN SELECTED)as[SOURCE STEP].
  rewrite ACTION in SOURCE,STEP;eapply journal_request_parent_after;eassumption.
Qed.

Theorem journal_selected_value ticks offset tick:
  LeanCage_Entry_CallerPhysical_TickAt(tick_values ticks)offset tick ->
  match nth_error ticks(nat_of_Nat offset)with
  |Some current=>Lean.eq current tick
  |None=>Lean.sEmpty
  end.
Proof.
  revert offset;induction ticks as[|head ticks IH];intros[|offset]SELECTED;
    cbn[tick_values LeanCage_Entry_CallerPhysical_TickAt]in SELECTED|-*.
  - destruct SELECTED.
  - destruct SELECTED.
  - exact SELECTED.
  - apply IH;exact SELECTED.
Qed.

Theorem journal_checkpoint_prefix mayTrace owner child history ticks before after checkpoint_offset checkpoint:
  LeanCage_Entry_CallerPhysical_Journal mayTrace owner child history before(tick_values ticks)after ->
  LeanCage_Entry_CallerPhysical_ContextSafe owner before ->
  nth_error ticks checkpoint_offset=Some checkpoint ->
  Lean.eq(LeanCage_Entry_CallerPhysical_Context_parentAlive(LeanCage_Entry_CallerPhysical_Tick_after checkpoint))
    ProcessImport.Bool_true ->
  Lean.And(Lean.eq(LeanCage_Entry_CallerPhysical_Context_parentAlive before)ProcessImport.Bool_true)
    (forall offset tick,(offset<=checkpoint_offset)%nat ->nth_error ticks offset=Some tick ->
      Lean.eq(LeanCage_Entry_CallerPhysical_Context_parentAlive(LeanCage_Entry_CallerPhysical_Tick_after tick))
        ProcessImport.Bool_true).
Proof.
  revert before checkpoint_offset;induction ticks as[|head ticks IH];
    intros before[|checkpoint_offset]RUN SAFE SELECTED LIVE;try discriminate.
  - inversion RUN as[context|current remaining final SOURCE STEP REST];subst.
    inversion SELECTED;subst checkpoint;constructor.
    + eapply journal_step_parent_backward;eassumption.
    + intros[|offset]tick BOUND AT;[inversion AT;subst;exact LIVE|lia].
  - inversion RUN as[context|current remaining final SOURCE STEP REST];subst.
    pose proof(journal_step_context_safe _ _ _ _ _ _ _ SAFE SOURCE STEP)as NEXT_SAFE.
    destruct(IH _ _ REST NEXT_SAFE SELECTED LIVE)as[MIDDLE_LIVE PREFIX].
    constructor.
    + eapply journal_step_parent_backward;eassumption.
    + intros[|offset]tick BOUND AT.
      * inversion AT;subst;exact MIDDLE_LIVE.
      * apply(PREFIX offset tick);[lia|exact AT].
Qed.

Theorem journal_parent_live_before_checkpoint mayTrace owner child history ticks namespace group after
    start checkpoint_offset checkpoint:
  LeanCage_Entry_CallerPhysical_Journal mayTrace owner child history
    (LeanCage_Entry_CallerPhysical_born namespace group)(tick_values ticks)after ->
  nth_error ticks checkpoint_offset=Some checkpoint ->
  Lean.eq(LeanCage_Entry_CallerPhysical_Context_parentAlive(LeanCage_Entry_CallerPhysical_Tick_after checkpoint))
    ProcessImport.Bool_true ->
  LeanCage_Entry_CallerPhysical_ParentLiveBefore(Nat_of_nat start)(tick_values ticks)
    (Nat_of_nat(start+checkpoint_offset+1)).
Proof.
  intros RUN SELECTED LIVE.
  assert(SAFE:LeanCage_Entry_CallerPhysical_ContextSafe owner(LeanCage_Entry_CallerPhysical_born namespace group))
    by(left;constructor).
  destruct(journal_checkpoint_prefix _ _ _ _ _ _ _ _ _ RUN SAFE SELECTED LIVE)as[INITIAL PREFIX].
  intros offset tick BOUND AT.
  pose proof(Nat_le_nat_le' _ _ BOUND)as LESS.
  change(S(nat_of_Nat(ProcessImport.Nat_add(Nat_of_nat start)offset))<=
    nat_of_Nat(Nat_of_nat(start+checkpoint_offset+1)))%nat in LESS.
  rewrite physical_add_exact,!nat2Natid in LESS.
  pose proof(journal_selected_value _ _ _ AT)as ACTUAL.
  destruct(nth_error ticks(nat_of_Nat offset))as[current|]eqn:LOOKUP;[|destruct ACTUAL].
  pose proof(PREFIX(nat_of_Nat offset)current ltac:(lia)LOOKUP)as CURRENT_LIVE.
  exact(journal_strict_transport _ (fun current=>Lean.eq
    (LeanCage_Entry_CallerPhysical_Context_parentAlive(LeanCage_Entry_CallerPhysical_Tick_after current))
    ProcessImport.Bool_true)_ _ ACTUAL CURRENT_LIVE).
Qed.
