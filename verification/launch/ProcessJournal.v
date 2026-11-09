(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.origin: Actual source occurrences produce one shared physical journal. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Clight.
From LeanImport Require Import Lean.
Require Import IO Machine.
From EntryProcess Require Import ProcessMachine ProcessTrace ProcessImport ProcessConnection
  ProcessGlobalCalls ProcessCaller ProcessCallerConnection ProcessSourceOrigin.
From EntryNamespace Require Import NamespaceMachine NamespaceSocket.
Import ListNotations.
Local Close Scope lean_scope.

Record CallerSourceRun := {
  source_actor : LeanCage_Entry_ProcessIdentity;
  source_cell : tls;
  source_before : machine;
  source_events : list namespace_event;
  source_after : machine;
  source_started : caller_source_machine source_before;
  source_executed : namespace_steps caller_ge source_cell source_before source_events source_after
}.

Definition source_run_history run := flat_map caller_event_requests (source_events run).
Definition source_runs_history runs := flat_map source_run_history runs.

(* Foreign PID-namespace ancestors use a source no-debugger certificate. Their
   host PID words are not compared with this local fork's child PID. *)
Definition AncestorNoDebugger(run:CallerSourceRun):Prop:=source_run_history run=[].

Theorem ancestor_no_returned_debugger run ordinal request target address data returned:
  AncestorNoDebugger run ->nth_error(source_events run)ordinal=
    Some(namespace_process(process_traced request target address data returned)) ->False.
Proof.
  intros NONE EVENT;assert(MEMBER:In request(source_run_history run)).
  { unfold source_run_history;apply in_flat_map.
    exists(namespace_process(process_traced request target address data returned));split;
      [eapply nth_error_In;exact EVENT|left;reflexivity]. }
  rewrite NONE in MEMBER;contradiction.
Qed.

Theorem ancestor_no_lost_debugger run ordinal request target address data:
  AncestorNoDebugger run ->nth_error(source_events run)ordinal=
    Some(namespace_process(process_trace_lost request target address data)) ->False.
Proof.
  intros NONE EVENT;assert(MEMBER:In request(source_run_history run)).
  { unfold source_run_history;apply in_flat_map.
    exists(namespace_process(process_trace_lost request target address data));split;
      [eapply nth_error_In;exact EVENT|left;reflexivity]. }
  rewrite NONE in MEMBER;contradiction.
Qed.

(* One actual C task owns one program stream in this entry interpreter. This
   identifies the stream; it says nothing about authorization of its writes. *)
Record SourceProgramOwner(runs:list CallerSourceRun)(actor:LeanCage_Entry_ProcessIdentity)(program:nat):Prop:={
  source_owner_actor:forall run,nth_error runs program=Some run ->source_actor run=actor;
  source_owner_unique:forall other run,nth_error runs other=Some run ->source_actor run=actor ->other=program
}.

Lemma source_actor_indices_unique runs first second left right:
  NoDup(map source_actor runs) ->nth_error runs first=Some left ->nth_error runs second=Some right ->
  source_actor left=source_actor right ->first=second.
Proof.
  revert first second;induction runs as[|run rest IH];intros[|first][|second]UNIQUE LEFT RIGHT SAME;
    try discriminate;try reflexivity;inversion UNIQUE as[|a l ABSENT REST];subst a l.
  - inversion LEFT;subst left;exfalso;apply ABSENT;rewrite SAME.
    apply in_map;eapply nth_error_In;exact RIGHT.
  - inversion RIGHT;subst right;exfalso;apply ABSENT;rewrite <-SAME.
    apply in_map;eapply nth_error_In;exact LEFT.
  - f_equal;eapply IH;eassumption.
Qed.

Theorem source_distinct_tasks_own_program runs actor program run:
  NoDup(map source_actor runs) ->nth_error runs program=Some run ->source_actor run=actor ->
  SourceProgramOwner runs actor program.
Proof.
  intros UNIQUE PROGRAM ACTOR;constructor.
  - intros actual SAME;assert(EQUAL:actual=run)by congruence;subst actual;exact ACTOR.
  - intros other actual ACTUAL SAME;eapply source_actor_indices_unique;
      [exact UNIQUE|exact ACTUAL|exact PROGRAM|congruence].
Qed.

Lemma source_runs_request_words runs :
  Forall (fun request => tracer_request_allowed request = true) (source_runs_history runs).
Proof.
  induction runs as [|run rest IH];[constructor|].
  cbn[source_runs_history];apply Forall_app;split;[|exact IH].
  exact (caller_actual_request_history _ _ _ _ (source_started run) (source_executed run)).
Qed.

Theorem source_runs_history_checked runs :
  LeanCage_Entry_CallerRequestsAllowed (caller_request_values (source_runs_history runs)).
Proof. apply caller_history_ordinary_Lean,source_runs_request_words. Qed.

Lemma source_run_request_in_history runs run event request :
  In run runs -> In event (source_events run) -> In request (caller_event_requests event) ->
  In request (source_runs_history runs).
Proof.
  intros RUN EVENT REQUEST;apply in_flat_map;exists run;split;[exact RUN|].
  apply in_flat_map;exists event;split;assumption.
Qed.

Fixpoint journal_byte_values bytes := match bytes with
  | []=>List_nil_inst1 Lean.Nat
  | byte::rest=>List_cons_inst1 Lean.Nat (Nat_of_nat(Z.to_nat(Byte.unsigned byte)))
      (journal_byte_values rest)
  end.
Definition journal_lost_value(lost:bool) := if lost then ProcessImport.Bool_true else ProcessImport.Bool_false.

(* This is the same indexed C event and the same tick's observed write. Loss
   records committed bytes without pretending that the caller received a reply. *)
Inductive SourceWrite (runs:list CallerSourceRun) tick actor fd bytes lost : Prop :=
| source_write_actual : forall run program ordinal event io,
    nth_error runs program=Some run ->nth_error(source_events run)ordinal=Some event ->
    namespace_socket_io event=Some io ->operation(source_socket_request io)=writing ->
    actor=source_actor run ->fd=caller_request_nat(descriptor(source_socket_request io)) ->
    bytes=journal_byte_values(source_socket_bytes io) ->lost=journal_lost_value(source_socket_lost io) ->
    ProcessImport.socket tick=LeanCage_Entry_CallerPhysical_SocketObservation_wrote actor fd bytes lost ->
    LeanCage_Entry_CallerPhysical_Tick_source tick=
      Option_some_inst1 LeanCage_Entry_CallerPhysical_SourceReference
        (LeanCage_Entry_CallerPhysical_SourceReference_mk(Nat_of_nat program)(Nat_of_nat ordinal)) ->
    SourceWrite runs tick actor fd bytes lost.

Inductive WriteOrigin runs tick actor fd bytes lost : Prop :=
| write_from_source : SourceWrite runs tick actor fd bytes lost ->WriteOrigin runs tick actor fd bytes lost
| write_outside_c_source :
    LeanCage_Entry_CallerPhysical_Tick_source tick=
      Option_none_inst1 LeanCage_Entry_CallerPhysical_SourceReference ->
    ProcessImport.socket tick=LeanCage_Entry_CallerPhysical_SocketObservation_wrote actor fd bytes lost ->
    WriteOrigin runs tick actor fd bytes lost.

(* Control safety depends on the actual opcode and payload, independently of
   the target's PID view. Admission's separate primitive projection proves
   the exact local-fork target. Ancestors retain their own actual source run. *)
Inductive SourceTick (runs : list CallerSourceRun)
    (mayTrace : LeanCage_Entry_ProcessIdentity -> SProp)
    (child : LeanCage_Entry_ProcessIdentity) : LeanCage_Entry_CallerPhysical_Tick -> Prop :=
| source_tick_returned : forall tick run instance ordinal request target address data returned,
    nth_error runs instance = Some run ->
    nth_error (source_events run) ordinal =
      Some (namespace_process (process_traced request target address data returned)) ->
    LeanCage_Entry_CallerPhysical_Tick_action tick =
      LeanCage_Entry_CallerPhysical_Action_request (source_actor run)
        (caller_request_nat request) (caller_options_nat (caller_payload_word data)) ->
    LeanCage_Entry_CallerPhysical_Tick_source tick =
      Option_some_inst1 LeanCage_Entry_CallerPhysical_SourceReference
        (LeanCage_Entry_CallerPhysical_SourceReference_mk (Nat_of_nat instance) (Nat_of_nat ordinal)) ->
    SourceTick runs mayTrace child tick
| source_tick_lost : forall tick run instance ordinal request target address data,
    nth_error runs instance = Some run ->
    nth_error (source_events run) ordinal =
      Some (namespace_process (process_trace_lost request target address data)) ->
    LeanCage_Entry_CallerPhysical_Tick_action tick =
      LeanCage_Entry_CallerPhysical_Action_request (source_actor run)
        (caller_request_nat request) (caller_options_nat (caller_payload_word data)) ->
    LeanCage_Entry_CallerPhysical_Tick_source tick =
      Option_some_inst1 LeanCage_Entry_CallerPhysical_SourceReference
        (LeanCage_Entry_CallerPhysical_SourceReference_mk (Nat_of_nat instance) (Nat_of_nat ordinal)) ->
    SourceTick runs mayTrace child tick
| source_tick_denied : forall tick actor request options,
    Not (mayTrace actor) ->
    Not (Lean.eq
      (LeanCage_Entry_CallerPhysical_Context_tracer (LeanCage_Entry_CallerPhysical_Tick_before tick))
      (Option_some_inst1 LeanCage_Entry_ProcessIdentity actor)) ->
    LeanCage_Entry_CallerPhysical_Tick_action tick =
      LeanCage_Entry_CallerPhysical_Action_request actor request options ->
    SourceTick runs mayTrace child tick
| source_tick_idle : forall tick,
    LeanCage_Entry_CallerPhysical_Tick_action tick = LeanCage_Entry_CallerPhysical_Action_idle ->
    SourceTick runs mayTrace child tick
| source_tick_native : forall tick,
    LeanCage_Entry_CallerPhysical_Tick_action tick = LeanCage_Entry_CallerPhysical_Action_native ->
    SourceTick runs mayTrace child tick
| source_tick_traceme : forall tick,
    LeanCage_Entry_CallerPhysical_Tick_action tick = LeanCage_Entry_CallerPhysical_Action_traceMe ->
    SourceTick runs mayTrace child tick
| source_tick_placement : forall tick group actor fd bytes lost,
    WriteOrigin runs tick actor fd bytes lost ->
    LeanCage_Entry_CallerPhysical_Tick_action tick = LeanCage_Entry_CallerPhysical_Action_placement group ->
    SourceTick runs mayTrace child tick
| source_tick_parent_death : forall tick,
    LeanCage_Entry_CallerPhysical_Tick_action tick = LeanCage_Entry_CallerPhysical_Action_parentDeath ->
    SourceTick runs mayTrace child tick
| source_tick_child_death : forall tick,
    LeanCage_Entry_CallerPhysical_Tick_action tick = LeanCage_Entry_CallerPhysical_Action_childDeath ->
    SourceTick runs mayTrace child tick.

Theorem source_tick_use runs mayTrace child tick : SourceTick runs mayTrace child tick ->
  LeanCage_Entry_CallerPhysical_SourceUse mayTrace
    (caller_request_values (source_runs_history runs))
    (LeanCage_Entry_CallerPhysical_Tick_before tick)
    (LeanCage_Entry_CallerPhysical_Tick_action tick).
Proof.
  intro SOURCE;destruct SOURCE as
    [tick run instance ordinal request target address data returned RUN EVENT ACTION REFERENCE
    |tick run instance ordinal request target address data RUN EVENT ACTION REFERENCE
    |tick actor request options DENIED UNTRACED ACTION
    |tick ACTION|tick ACTION|tick ACTION|tick group actor fd bytes lost WRITE ACTION|tick ACTION|tick ACTION];
    rewrite ACTION;cbn[LeanCage_Entry_CallerPhysical_SourceUse];try solve[constructor].
  - intro AUTHORITY;constructor.
    + apply caller_source_history_member.
      eapply source_run_request_in_history;
        [eapply nth_error_In;exact RUN|eapply nth_error_In;exact EVENT|left;reflexivity].
    + pose proof (caller_source_returned_control _ _ _ _ _ _ _ _ _
        (source_started run) (source_executed run) (nth_error_In _ _ EVENT)) as CHECK.
      destruct CHECK as [_ SAFE];exact SAFE.
  - intro AUTHORITY;constructor.
    + apply caller_source_history_member.
      eapply source_run_request_in_history;
        [eapply nth_error_In;exact RUN|eapply nth_error_In;exact EVENT|left;reflexivity].
    + pose proof (caller_source_lost_control _ _ _ _ _ _ _ _
        (source_started run) (source_executed run) (nth_error_In _ _ EVENT)) as CHECK.
      destruct CHECK as [_ SAFE];exact SAFE.
  - intro AUTHORITY;destruct AUTHORITY as [ALLOWED|OWNED].
    + destruct (DENIED ALLOWED).
    + destruct (UNTRACED OWNED).
Qed.

Fixpoint tick_values (ticks : list LeanCage_Entry_CallerPhysical_Tick) :=
  match ticks with
  | [] => List_nil_inst1 LeanCage_Entry_CallerPhysical_Tick
  | tick :: rest => List_cons_inst1 LeanCage_Entry_CallerPhysical_Tick tick (tick_values rest)
  end.

(* The primitive relation retains arbitrary debugger operations and failures.
   This composition adds the real source emission at each same physical tick. *)
Inductive RecordedRun runs mayTrace owner child :
    LeanCage_Entry_CallerPhysical_Context -> list LeanCage_Entry_CallerPhysical_Tick ->
    LeanCage_Entry_CallerPhysical_Context -> Prop :=
| recorded_done : forall context,RecordedRun runs mayTrace owner child context [] context
| recorded_next : forall tick ticks final,
    SourceTick runs mayTrace child tick ->
    LeanCage_Entry_CallerPhysical_Step mayTrace owner child
      (LeanCage_Entry_CallerPhysical_Tick_before tick) (LeanCage_Entry_CallerPhysical_Tick_action tick)
      (LeanCage_Entry_CallerPhysical_Tick_after tick) ->
    RecordedRun runs mayTrace owner child (LeanCage_Entry_CallerPhysical_Tick_after tick) ticks final ->
    RecordedRun runs mayTrace owner child (LeanCage_Entry_CallerPhysical_Tick_before tick)
      (tick :: ticks) final.

Theorem actual_source_produces_journal runs mayTrace owner child before ticks after :
  RecordedRun runs mayTrace owner child before ticks after ->
  LeanCage_Entry_CallerPhysical_Journal mayTrace owner child
    (caller_request_values (source_runs_history runs)) before (tick_values ticks) after.
Proof.
  intro RUN;induction RUN as [context|tick ticks final SOURCE KERNEL REMAINING IH];cbn[tick_values].
  - constructor.
  - econstructor;[exact (source_tick_use _ _ child _ SOURCE)|exact KERNEL|exact IH].
Qed.

Theorem actual_tick_position ticks offset tick : nth_error ticks offset = Some tick ->
  LeanCage_Entry_CallerPhysical_TickAt (tick_values ticks) (Nat_of_nat offset) tick.
Proof.
  revert offset;induction ticks as [|first rest IH];intros [|offset] SELECTED;
    try discriminate;cbn[tick_values LeanCage_Entry_CallerPhysical_TickAt] in *.
  - inversion SELECTED;subst;constructor.
  - apply IH;exact SELECTED.
Qed.

Definition source_reference program ordinal :=
  Option_some_inst1 LeanCage_Entry_CallerPhysical_SourceReference
    (LeanCage_Entry_CallerPhysical_SourceReference_mk(Nat_of_nat program)(Nat_of_nat ordinal)).
Definition source_cursor_next (before:nat->nat) program :=
  fun query=>if Nat.eqb query program then S(before program)else before query.

Inductive SourceCursorStep : (nat->nat)->LeanCage_Entry_CallerPhysical_Tick->(nat->nat)->Prop :=
| source_cursor_external : forall before tick,
    LeanCage_Entry_CallerPhysical_Tick_source tick=
      Option_none_inst1 LeanCage_Entry_CallerPhysical_SourceReference ->SourceCursorStep before tick before
| source_cursor_advance : forall before tick program,
    LeanCage_Entry_CallerPhysical_Tick_source tick=source_reference program(before program) ->
    SourceCursorStep before tick(source_cursor_next before program).

Inductive SourceSchedule : (nat->nat)->list LeanCage_Entry_CallerPhysical_Tick->(nat->nat)->Prop :=
| source_schedule_done : forall before,SourceSchedule before [] before
| source_schedule_next : forall before tick middle ticks after,
    SourceCursorStep before tick middle ->SourceSchedule middle ticks after ->
    SourceSchedule before(tick::ticks)after.

Definition SourceIO runs tick := forall actor fd bytes lost,
  ProcessImport.socket tick=LeanCage_Entry_CallerPhysical_SocketObservation_wrote actor fd bytes lost ->
  WriteOrigin runs tick actor fd bytes lost.

(* The application interpreter emits every source event once in source order.
   Primitive observations and native interleavings retain that same tick. *)
Inductive ScheduledRecordedRun runs mayTrace owner child :
    (nat->nat)->LeanCage_Entry_CallerPhysical_Context->list LeanCage_Entry_CallerPhysical_Tick->
    (nat->nat)->LeanCage_Entry_CallerPhysical_Context->Prop :=
| scheduled_recorded_done : forall cursor context,
    ScheduledRecordedRun runs mayTrace owner child cursor context [] cursor context
| scheduled_recorded_next : forall cursor before tick next ticks final after,
    SourceTick runs mayTrace child tick ->SourceIO runs tick ->SourceCursorStep cursor tick next ->
    LeanCage_Entry_CallerPhysical_Tick_before tick=before ->
    LeanCage_Entry_CallerPhysical_Step mayTrace owner child before
      (LeanCage_Entry_CallerPhysical_Tick_action tick)(LeanCage_Entry_CallerPhysical_Tick_after tick) ->
    ScheduledRecordedRun runs mayTrace owner child next
      (LeanCage_Entry_CallerPhysical_Tick_after tick)ticks final after ->
    ScheduledRecordedRun runs mayTrace owner child cursor before(tick::ticks)final after.

Theorem scheduled_run_records runs mayTrace owner child cursor before ticks final after :
  ScheduledRecordedRun runs mayTrace owner child cursor before ticks final after ->
  RecordedRun runs mayTrace owner child before ticks after.
Proof.
  intro RUN;induction RUN;[constructor|]. subst before;econstructor;eassumption.
Qed.

Theorem scheduled_run_source_order runs mayTrace owner child cursor before ticks final after :
  ScheduledRecordedRun runs mayTrace owner child cursor before ticks final after ->
  SourceSchedule cursor ticks final.
Proof.
  intro RUN;induction RUN.
  - apply source_schedule_done.
  - eapply source_schedule_next;eassumption.
Qed.

Theorem scheduled_run_source_io runs mayTrace owner child cursor before ticks final after :
  ScheduledRecordedRun runs mayTrace owner child cursor before ticks final after ->Forall(SourceIO runs)ticks.
Proof.
  intro RUN;induction RUN.
  - constructor.
  - constructor;assumption.
Qed.

Theorem actual_scheduled_source_produces_journal runs mayTrace owner child cursor before ticks final after :
  ScheduledRecordedRun runs mayTrace owner child cursor before ticks final after ->
  LeanCage_Entry_CallerPhysical_Journal mayTrace owner child
    (caller_request_values(source_runs_history runs))before(tick_values ticks)after.
Proof. intro RUN;apply actual_source_produces_journal;eapply scheduled_run_records;exact RUN. Qed.

Theorem scheduled_c_write_has_actual_source runs mayTrace owner child cursor before ticks final after
    offset tick actor fd bytes lost program ordinal :
  ScheduledRecordedRun runs mayTrace owner child cursor before ticks final after ->
  nth_error ticks offset=Some tick ->
  LeanCage_Entry_CallerPhysical_Tick_source tick=source_reference program ordinal ->
  ProcessImport.socket tick=LeanCage_Entry_CallerPhysical_SocketObservation_wrote actor fd bytes lost ->
  SourceWrite runs tick actor fd bytes lost.
Proof.
  intros RUN SELECTED SOURCE SOCKET.
  pose proof(scheduled_run_source_io _ _ _ _ _ _ _ _ _ RUN)as IO.
  apply Forall_forall with(x:=tick)in IO;[|eapply nth_error_In;exact SELECTED].
  destruct(IO _ _ _ _ SOCKET)as[ACTUAL|OUTSIDE _];[exact ACTUAL|].
  rewrite SOURCE in OUTSIDE;discriminate.
Qed.

Lemma source_reference_injective p q i j : source_reference p i=source_reference q j ->p=q /\i=j.
Proof.
  intro SAME;inversion SAME.
  split;apply(f_equal nat_of_Nat)in H0,H1;rewrite !nat2Natid in H0,H1;assumption.
Qed.

Lemma source_cursor_monotone before tick after : SourceCursorStep before tick after ->
  forall program,(before program<=after program)%nat.
Proof.
  intro STEP;destruct STEP as[before tick SOURCE|before tick selected SOURCE];
    intro query;[apply Nat.le_refl|].
  unfold source_cursor_next;destruct(Nat.eqb query selected)eqn:SAME.
  - apply Nat.eqb_eq in SAME;subst query;apply Nat.le_succ_diag_r.
  - apply Nat.le_refl.
Qed.

Theorem source_schedule_monotone before ticks after :SourceSchedule before ticks after ->
  forall program,(before program<=after program)%nat.
Proof.
  intro RUN;induction RUN;intro program;[apply Nat.le_refl|].
  eapply Nat.le_trans;[eapply source_cursor_monotone;exact H|apply IHRUN].
Qed.

Lemma source_cursor_selected before tick after program ordinal :
  SourceCursorStep before tick after ->
  LeanCage_Entry_CallerPhysical_Tick_source tick=source_reference program ordinal ->
  before program=ordinal /\after program=S ordinal.
Proof.
  intros STEP SOURCE;inversion STEP;subst.
  - rewrite SOURCE in H;discriminate.
  - assert(REFERENCE:source_reference program0(before program0)=source_reference program ordinal)by congruence.
    destruct(source_reference_injective _ _ _ _ REFERENCE)as[PROGRAM ORDINAL];subst program0 ordinal.
    split;[reflexivity|]. unfold source_cursor_next;rewrite Nat.eqb_refl;reflexivity.
Qed.

Lemma source_schedule_selected before ticks after offset tick program ordinal :
  SourceSchedule before ticks after ->nth_error ticks offset=Some tick ->
  LeanCage_Entry_CallerPhysical_Tick_source tick=source_reference program ordinal ->
  (before program<=ordinal)%nat /\(ordinal<after program)%nat.
Proof.
  intro RUN;revert offset;induction RUN;intros[|offset]SELECTED SOURCE;try discriminate.
  - inversion SELECTED;subst.
    destruct(source_cursor_selected _ _ _ _ _ H SOURCE)as[BEFORE MIDDLE].
    split;[rewrite BEFORE;apply Nat.le_refl|].
    pose proof(source_schedule_monotone _ _ _ RUN program);rewrite MIDDLE in H0;lia.
  - destruct(IHRUN _ SELECTED SOURCE)as[LOW HIGH];split;[|exact HIGH].
    eapply Nat.le_trans;[eapply source_cursor_monotone;exact H|exact LOW].
Qed.

Theorem source_schedule_order before ticks after first second left right program earlier later :
  SourceSchedule before ticks after ->(first<second)%nat ->
  nth_error ticks first=Some left ->nth_error ticks second=Some right ->
  LeanCage_Entry_CallerPhysical_Tick_source left=source_reference program earlier ->
  LeanCage_Entry_CallerPhysical_Tick_source right=source_reference program later ->(earlier<later)%nat.
Proof.
  intro RUN;revert first second;induction RUN;intros[|first][|second]ORDER LEFT RIGHT EARLIER LATER;
    try lia;try discriminate.
  - inversion LEFT;subst.
    destruct(source_cursor_selected _ _ _ _ _ H EARLIER)as[BEFORE MIDDLE].
    destruct(source_schedule_selected _ _ _ _ _ _ _ RUN RIGHT LATER)as[LOW HIGH].
    rewrite MIDDLE in LOW;lia.
  - apply(IHRUN first second);[lia|exact LEFT|exact RIGHT|exact EARLIER|exact LATER].
Qed.

Lemma source_cursor_increment before tick after program :
  SourceCursorStep before tick after ->(before program<after program)%nat ->
  after program=S(before program) /\
  LeanCage_Entry_CallerPhysical_Tick_source tick=source_reference program(before program).
Proof.
  intros STEP INCREASE;destruct STEP as[before tick SOURCE|before tick selected SOURCE];[lia|].
  unfold source_cursor_next in *;destruct(Nat.eqb program selected)eqn:SAME;[|lia].
  apply Nat.eqb_eq in SAME;subst selected;split;[reflexivity|exact SOURCE].
Qed.

(* A source event between the initial and final cursors has an occurrence in
   this physical history, including events between two selected operations. *)
Theorem source_schedule_covers before ticks after program ordinal :
  SourceSchedule before ticks after ->
  (before program<=ordinal<after program)%nat ->
  exists offset tick,nth_error ticks offset=Some tick /\
    LeanCage_Entry_CallerPhysical_Tick_source tick=source_reference program ordinal.
Proof.
  intro RUN;induction RUN;intro BOUNDS;[lia|].
  destruct(lt_dec ordinal(middle program))as[HEAD|TAIL].
  - assert(INCREASE:(before program<middle program)%nat)by lia.
    destruct(source_cursor_increment _ _ _ _ H INCREASE)as[INCREMENT SOURCE].
    assert(ORDINAL:ordinal=before program)by lia;subst ordinal.
    exists 0%nat,tick;split;[reflexivity|exact SOURCE].
  - destruct IHRUN as[offset[selected[POSITION SOURCE]]];[lia|].
    exists(S offset),selected;split;[exact POSITION|exact SOURCE].
Qed.

Theorem source_schedule_order_inverse before ticks after first second left right program earlier later :
  SourceSchedule before ticks after ->(earlier<later)%nat ->
  nth_error ticks first=Some left ->nth_error ticks second=Some right ->
  LeanCage_Entry_CallerPhysical_Tick_source left=source_reference program earlier ->
  LeanCage_Entry_CallerPhysical_Tick_source right=source_reference program later ->(first<second)%nat.
Proof.
  intros RUN ORDER LEFT RIGHT EARLIER LATER.
  destruct(Nat.lt_trichotomy first second)as[BEFORE|[SAME|AFTER]];[exact BEFORE| |].
  - subst second;assert(TICK:left=right)by congruence;subst right.
    assert(REFERENCE:source_reference program earlier=source_reference program later)by congruence.
    destruct(source_reference_injective _ _ _ _ REFERENCE)as[_ SAME];lia.
  - pose proof(source_schedule_order _ _ _ _ _ _ _ _ _ _ RUN AFTER RIGHT LEFT LATER EARLIER);lia.
Qed.

Theorem source_owned_write_reference runs actor program tick fd bytes lost:
  SourceProgramOwner runs actor program ->SourceWrite runs tick actor fd bytes lost ->
  exists ordinal,LeanCage_Entry_CallerPhysical_Tick_source tick=source_reference program ordinal.
Proof.
  intros OWNER WRITE;destruct WRITE as[run selected ordinal event io PROGRAM EVENT IO WRITING
    ACTOR FD BYTES LOST SOCKET REFERENCE].
  assert(SELECTED:selected=program).
  { eapply source_owner_unique;[exact OWNER|exact PROGRAM|symmetry;exact ACTOR]. }
  subst selected;exists ordinal;exact REFERENCE.
Qed.
