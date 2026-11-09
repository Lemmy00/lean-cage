(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-entry.provenance: Actual source supplies each operation, payload and log use. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Clight.
From LeanImport Require Import Lean.
Require Import Machine.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessControl ProcessTrace ProcessGlobalCalls
  ProcessCaller ProcessCallerConnection ProcessConnection ProcessImport.
From EntryNamespace Require Import NamespaceMachine.
Import ListNotations.
Local Close Scope lean_scope.
Local Open Scope Z_scope.

Definition caller_payload_word(data:Values.val):int64:=match data with Vlong word=>word|_=>Int64.zero end.

Theorem caller_source_supervisor_word request payload :
  tracer_request_allowed request=true ->
  (request=Int.repr 16896 ->payload=Int64.repr 1048592) ->
  LeanCage_Entry_SourceSupervisor(caller_request_nat request)(caller_options_nat payload).
Proof.
  intros REQUEST PAYLOAD;unfold LeanCage_Entry_SourceSupervisor;constructor.
  - apply checked_tracer_request_word;exact REQUEST.
  - intro SELECTED.
    assert(SAME:request=Int.repr 16896).
    { destruct(Int.eq request(Int.repr 16896))eqn:EQUAL.
      - apply Int.same_if_eq;exact EQUAL.
      - assert(DIFFERENT:request<>Int.repr 16896).
        { intro SAME;subst request;rewrite Int.eq_true in EQUAL;discriminate. }
        destruct(caller_word_different request 16896 ltac:(cbn;lia)DIFFERENT SELECTED). }
    specialize(PAYLOAD SAME);subst payload.
    apply caller_native_nat_eq;unfold caller_options_nat;rewrite nat2Natid.
    rewrite Int64.unsigned_repr by(change Int64.max_unsigned with 18446744073709551615;lia).
    repeat first[rewrite caller_double_nat|progress(cbn[nat_of_Nat OfNat_ofNat_inst1 instOfNatNat ofNat0])].
    lia.
Qed.

Lemma caller_source_history_member request requests :
  In request requests ->
  LeanCage_Entry_SourceRequestMember(caller_request_nat request)(caller_request_values requests).
Proof.
  intro MEMBER;induction requests as[|first rest IH];[contradiction|].
  cbn[caller_request_values LeanCage_Entry_SourceRequestMember].
  destruct MEMBER as[SAME|LATER].
  - subst request;apply Lean.Or_inl;constructor.
  - apply Lean.Or_inr;apply IH;exact LATER.
Qed.

Theorem caller_source_returned_control cell before events after request child address data returned :
  caller_source_machine before ->namespace_steps caller_ge cell before events after ->
  In(namespace_process(process_traced request child address data returned))events ->
  LeanCage_Entry_SourceSupervisorUse
    (caller_request_values(flat_map caller_event_requests events))
    (caller_request_nat request)(caller_options_nat(caller_payload_word data)).
Proof.
  intros SOURCE RUN MEMBER.
  assert(HISTORY:In request(flat_map caller_event_requests events)).
  { apply in_flat_map;exists(namespace_process(process_traced request child address data returned)).
    split;[exact MEMBER|left;reflexivity]. }
  pose proof(caller_actual_request_history _ _ _ _ SOURCE RUN)as REQUESTS.
  apply Forall_forall with(x:=request)in REQUESTS;[|exact HISTORY].
  pose proof(caller_actual_options_history _ _ _ _ SOURCE RUN)as OPTIONS.
  apply Forall_forall with(x:=namespace_process(process_traced request child address data returned))in OPTIONS;
    [|exact MEMBER].
  unfold LeanCage_Entry_SourceSupervisorUse;constructor.
  - apply caller_source_history_member;exact HISTORY.
  - apply caller_source_supervisor_word;[exact REQUESTS|].
    intro SELECTED;specialize(OPTIONS SELECTED);rewrite OPTIONS;reflexivity.
Qed.

Theorem caller_source_lost_control cell before events after request child address data :
  caller_source_machine before ->namespace_steps caller_ge cell before events after ->
  In(namespace_process(process_trace_lost request child address data))events ->
  LeanCage_Entry_SourceSupervisorUse
    (caller_request_values(flat_map caller_event_requests events))
    (caller_request_nat request)(caller_options_nat(caller_payload_word data)).
Proof.
  intros SOURCE RUN MEMBER.
  assert(HISTORY:In request(flat_map caller_event_requests events)).
  { apply in_flat_map;exists(namespace_process(process_trace_lost request child address data)).
    split;[exact MEMBER|left;reflexivity]. }
  pose proof(caller_actual_request_history _ _ _ _ SOURCE RUN)as REQUESTS.
  apply Forall_forall with(x:=request)in REQUESTS;[|exact HISTORY].
  pose proof(caller_actual_options_history _ _ _ _ SOURCE RUN)as OPTIONS.
  apply Forall_forall with(x:=namespace_process(process_trace_lost request child address data))in OPTIONS;
    [|exact MEMBER].
  unfold LeanCage_Entry_SourceSupervisorUse;constructor.
  - apply caller_source_history_member;exact HISTORY.
  - apply caller_source_supervisor_word;[exact REQUESTS|].
    intro SELECTED;specialize(OPTIONS SELECTED);rewrite OPTIONS;reflexivity.
Qed.

Definition caller_entry_lineage_label(event:entry_handoff_event):nat*Lean.Nat:=
  match event with
  |entry_library library=>
      match library with
      |LibraryMachine.original_event(io_step _ _)|LibraryMachine.original_event(partial_loss _ _ _)=>
          (7%nat,Nat_of_nat 0)
      |LibraryMachine.original_event _|LibraryMachine.library_wait=>(5%nat,Nat_of_nat 0)
      |LibraryMachine.close_returned _ _=>(9%nat,Nat_of_nat 0)
      |LibraryMachine.exit_requested _=>(8%nat,Nat_of_nat 0)
      |_ =>(12%nat,Nat_of_nat 0)
      end
  |entry_formatted _ _ _ _|entry_format_lost _ _ _=>(11%nat,Nat_of_nat 0)
  |entry_flags_returned _ _ _|entry_flags_lost _ _=>(9%nat,Nat_of_nat 0)
  |entry_exec_returned _ _ _ _|entry_exec_lost _ _ _|entry_image _ _ _=>(1%nat,Nat_of_nat 0)
  |entry_primitive_wait=>(5%nat,Nat_of_nat 0)
  end.

Definition caller_process_lineage_label(event:process_event):nat*Lean.Nat:=
  match event with
  |process_entry entry=>caller_entry_lineage_label entry
  |process_traced request _ _ data _|process_trace_lost request _ _ data=>
      if Int.eq request(Int.repr 16896)
      then(13%nat,caller_options_nat(caller_payload_word data))
      else(6%nat,caller_request_nat request)
  |process_clocked _ _ _ _|process_clock_lost _ _ _=>(10%nat,Nat_of_nat 0)
  |_ =>(8%nat,Nat_of_nat 0)
  end.

Definition caller_namespace_lineage_label(event:namespace_event):nat*Lean.Nat:=
  match event with
  |namespace_process process=>caller_process_lineage_label process
  |namespace_forked _|namespace_fork_lost=>(0%nat,Nat_of_nat 0)
  |namespace_paired _ _ _ _ _ _ _ _|namespace_duplicated _ _ _|
    namespace_pair_lost _ _ _ _ _|namespace_duplicate_lost _ _=>(9%nat,Nat_of_nat 0)
  |namespace_masked _ _|namespace_defaulted _ _|namespace_mask_lost _|namespace_default_lost _=>
      (8%nat,Nat_of_nat 0)
  |namespace_waiting=>(5%nat,Nat_of_nat 0)
  end.

Lemma caller_plain_lineage_kind(kind:nat)payload :
  In kind[0%nat;1%nat;4%nat;5%nat;7%nat;8%nat;9%nat;10%nat;11%nat;12%nat] ->
  LeanCage_Entry_CallerLineageAllowed(Nat_of_nat kind)payload.
Proof.
  intros MEMBER;repeat destruct MEMBER as[SAME|MEMBER];try contradiction;subst kind;
    unfold LeanCage_Entry_CallerLineageAllowed;
    repeat first[solve[apply Lean.Or_inl;constructor]|apply Lean.Or_inr].
Qed.

Lemma caller_entry_lineage_allowed event :
  LeanCage_Entry_CallerLineageAllowed(Nat_of_nat(Datatypes.fst(caller_entry_lineage_label event)))
    (Datatypes.snd(caller_entry_lineage_label event)).
Proof.
  destruct event;cbn[caller_entry_lineage_label Datatypes.fst Datatypes.snd];
    try(solve[apply caller_plain_lineage_kind;cbn;auto 12]).
  destruct event;cbn[caller_entry_lineage_label Datatypes.fst Datatypes.snd];
    try(solve[apply caller_plain_lineage_kind;cbn;auto 12]).
  destruct ev;cbn[caller_entry_lineage_label Datatypes.fst Datatypes.snd];apply caller_plain_lineage_kind;cbn;auto 12.
Qed.

Theorem caller_source_lineage_event cell before events after event :
  caller_source_machine before ->namespace_steps caller_ge cell before events after ->In event events ->
  LeanCage_Entry_CallerLineageAllowed(Nat_of_nat(Datatypes.fst(caller_namespace_lineage_label event)))
    (Datatypes.snd(caller_namespace_lineage_label event)).
Proof.
  intros SOURCE RUN MEMBER.
  destruct event;cbn[caller_namespace_lineage_label Datatypes.fst Datatypes.snd];
    try(solve[apply caller_plain_lineage_kind;cbn;auto 12]).
  destruct event;cbn[caller_process_lineage_label Datatypes.fst Datatypes.snd];
    try(solve[apply caller_plain_lineage_kind;cbn;auto 12]);
    try(solve[apply caller_entry_lineage_allowed]).
  - destruct(Int.eq request(Int.repr 16896))eqn:OPTIONS.
    + apply Int.same_if_eq in OPTIONS;subst request.
      pose proof(caller_actual_options_history _ _ _ _ SOURCE RUN)as CHECK.
      apply Forall_forall with(x:=namespace_process(process_traced(Int.repr 16896)child address data returned))in CHECK;
        [|exact MEMBER].
      cbn[caller_event_options]in CHECK;specialize(CHECK ltac:(reflexivity));rewrite CHECK.
      apply caller_setoptions_lineage_ordinary_Lean;reflexivity.
    + apply caller_ptrace_lineage_ordinary_Lean.
      * pose proof(caller_actual_request_history _ _ _ _ SOURCE RUN)as CHECK.
        apply Forall_forall with(x:=request)in CHECK;[exact CHECK|].
        apply in_flat_map;exists(namespace_process(process_traced request child address data returned));split;
          [exact MEMBER|left;reflexivity].
      * intro SAME;subst request;rewrite Int.eq_true in OPTIONS;discriminate.
  - destruct(Int.eq request(Int.repr 16896))eqn:OPTIONS.
    + apply Int.same_if_eq in OPTIONS;subst request.
      pose proof(caller_actual_options_history _ _ _ _ SOURCE RUN)as CHECK.
      apply Forall_forall with(x:=namespace_process(process_trace_lost(Int.repr 16896)child address data))in CHECK;
        [|exact MEMBER].
      cbn[caller_event_options]in CHECK;specialize(CHECK ltac:(reflexivity));rewrite CHECK.
      apply caller_setoptions_lineage_ordinary_Lean;reflexivity.
    + apply caller_ptrace_lineage_ordinary_Lean.
      * pose proof(caller_actual_request_history _ _ _ _ SOURCE RUN)as CHECK.
        apply Forall_forall with(x:=request)in CHECK;[exact CHECK|].
        apply in_flat_map;exists(namespace_process(process_trace_lost request child address data));split;
          [exact MEMBER|left;reflexivity].
      * intro SAME;subst request;rewrite Int.eq_true in OPTIONS;discriminate.
Qed.

Definition caller_lineage_value event :=
  LeanCage_Entry_LineageLabel_mk
    (Nat_of_nat (Datatypes.fst (caller_namespace_lineage_label event)))
    (Datatypes.snd (caller_namespace_lineage_label event)).

Fixpoint caller_lineage_values events :=
  match events with
  | [] => List_nil_inst1 LeanCage_Entry_LineageLabel
  | event :: rest => List_cons_inst1 LeanCage_Entry_LineageLabel
      (caller_lineage_value event) (caller_lineage_values rest)
  end.

Theorem caller_source_labels_ordinary_Lean cell before events after :
  caller_source_machine before -> namespace_steps caller_ge cell before events after ->
  LeanCage_Entry_CallerLabelsAllowed (caller_lineage_values events).
Proof.
  intros SOURCE RUN.
  assert (CHECK : forall selected,(forall event,In event selected -> In event events) ->
    LeanCage_Entry_CallerLabelsAllowed (caller_lineage_values selected)).
  { intro selected;induction selected as [|event rest IH];intro INCLUDED;
      cbn[caller_lineage_values LeanCage_Entry_CallerLabelsAllowed caller_lineage_value].
    - constructor.
    - constructor.
      + eapply caller_source_lineage_event;[exact SOURCE|exact RUN|apply INCLUDED;left;reflexivity].
      + apply IH;intros later MEMBER;apply INCLUDED;right;exact MEMBER. }
  apply CHECK;auto.
Qed.
