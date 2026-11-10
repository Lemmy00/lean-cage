(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The real control entry and guard carry one caller buffer history. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine StoreSteps ClightSteps.
From HostGateway Require Import GatewaySource GatewayMachine GatewayCancellation GatewayCancellationRuntime
  GatewayCancellationBuffers GatewayThreadRuntime GatewayStreamInterface GatewayReadContext GatewayReadMemory
  GatewayBufferReference GatewayGuardScope GatewayGuardFunction GatewayGuardObservation GatewayRuntimeCuts
  GatewayReadonly GatewayOperations GatewayFrames GatewayPrimitiveCalls GatewayTransferMath.
Import ListNotations.
Open Scope Z_scope.

Section CancellationEntryBuffers.
Context {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (io : Event -> option gateway_native_io)
    (native_private : World -> block -> Prop) (stable_readonly : World -> block -> Z -> Prop)
    (discipline : option val -> mem -> World -> Prop) (thread_errno : World -> int).
Context (runtime : gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).
Context (stream_block : block) (stream_offset : ptrofs) (initial : gateway_stream_values)
    (data_block : block) (data_offset : ptrofs) (amount : Z) (readonly : block -> Z -> Prop).
Variables (reference : mem) (owner : World).
Local Definition read_context := gateway_read_context native_private stable_readonly discipline None
  stream_block stream_offset initial data_block data_offset amount readonly.
Local Definition history := control_buffer_history native_private stream_block data_block readonly reference owner.
Definition control_entry_read_context memory world : Prop := read_context memory world /\ history memory world.
Definition control_entry_buffer_context command memory world : Prop :=
  control_context native_private stable_readonly discipline stream_block stream_offset initial
    data_block data_offset amount readonly command memory world /\ history memory world.

Lemma control_entry_read_ambient : gateway_runtime_discipline backend control_entry_read_context.
Proof.
  apply (gateway_owned_buffer_context_ambient backend io native_private stable_readonly discipline thread_errno runtime
    stream_block data_block stream_offset data_offset initial amount readonly reference owner None).
Qed.

Lemma control_entry_buffer_ambient command : gateway_runtime_discipline backend (control_entry_buffer_context command).
Proof.
  intros before world after next [CONTEXT HISTORY] INTERFERENCE; split.
  - eapply control_context_ambient; [exact runtime | exact CONTEXT | exact INTERFERENCE].
  - destruct (gateway_thread_ambient _ _ _ _ _ _ runtime None _ _ _ _ (proj1 (proj1 CONTEXT)) INTERFERENCE)
      as [SIDE [ACCESS FRAME]].
    eapply control_buffer_history_operation; [exact (proj1 CONTEXT) | exact ACCESS | exact FRAME | exact HISTORY].
Qed.

Lemma control_entry_guard_runtime command : gateway_guard_runtime backend (control_entry_buffer_context command).
Proof.
  constructor; [apply control_entry_buffer_ambient |].
  intros pointer before world result after next observed [CONTEXT HISTORY] OPERATION.
  destruct (gateway_volatile_int_load _ _ _ _ _ _ runtime None _ _ _ _ _ _ _
    (proj1 (proj1 CONTEXT)) OPERATION) as [VALUE [SIDE [ACCESS [FRAME IO]]]].
  split.
  - eapply control_context_preserved; eassumption.
  - eapply control_buffer_history_operation; [exact (proj1 CONTEXT) | exact ACCESS | exact FRAME | exact HISTORY].
Qed.

Lemma control_entry_guard_silent command pointer before world result after next observed :
  control_entry_buffer_context command before world ->
  gateway_builtin backend (EF_vload Mint32) [Ctypesdefs.tptr (Ctypesdefs.tvolatile Ctypesdefs.tint)] [pointer]
    before world result after next observed -> io observed = None.
Proof.
  intros [CONTEXT HISTORY] OPERATION.
  exact (proj2 (proj2 (proj2 (proj2 (gateway_volatile_int_load _ _ _ _ _ _ runtime None _ _ _ _ _ _ _
    (proj1 (proj1 CONTEXT)) OPERATION))))).
Qed.

Lemma control_entry_allocated command before world allocated :
  control_entry_read_context before world -> Mem.alloc before 0 1 = (allocated, command) ->
  control_entry_buffer_context command allocated world.
Proof.
  intros [INPUT [BUFFER NATIVE]] ALLOC; split.
  - eapply control_allocation_context; [exact runtime | exact INPUT | exact ALLOC].
  - split.
    + eapply gateway_buffer_reference_transitive; [exact BUFFER |].
      assert (FRAME : Mem.unchanged_on (fun _ _ => True) before allocated) by
        (eapply Mem.alloc_unchanged_on; exact ALLOC).
      split.
      * eapply Mem.unchanged_on_implies; [exact FRAME |]. intros; exact I.
      * intros object [SAME | SAME] position kind permission; subst object;
          apply (Mem.unchanged_on_perm _ _ _ FRAME _ position kind permission); try exact I.
        -- eapply gateway_read_stream_live; exact (proj2 (proj2 (proj2 (proj2 INPUT)))).
        -- exact (gateway_read_data_live _ _ _ _ _ _ _ _ (proj2 (proj2 (proj2 (proj2 INPUT))))).
    + eapply gateway_native_reference_transitive; [exact NATIVE |].
      intros object LIVE PRIVATE; split; [eapply Mem.valid_block_alloc; eassumption | exact PRIVATE].
Qed.

Theorem actual_control_guard_buffer_cut before world events returned after next :
  control_entry_read_context before world ->
  gateway_steps backend ge
    (gateway_live (Callstate (Internal f_host_control) [Vptr stream_block stream_offset] Kstop before) world) events
    (gateway_live (Returnstate returned Kstop after) next) ->
  exists prefix suffix command reached reached_world,
    events = prefix ++ suffix /\ gateway_received_bytes io (stream_descriptor initial) prefix = [] /\
    control_entry_buffer_context command (memory_of reached) reached_world /\
    gateway_guard_source _stream (Vptr stream_block stream_offset) (Kseq control_after_guard Kstop)
      (control_environment command) reached /\ gateway_guard_function f_host_control reached /\
    gateway_guard_terminal (Kseq control_after_guard Kstop) reached /\
    gateway_steps backend ge
      (gateway_live (Callstate (Internal f_host_control) [Vptr stream_block stream_offset] Kstop before) world)
      prefix (gateway_live reached reached_world) /\
    gateway_steps backend ge (gateway_live reached reached_world) suffix
      (gateway_live (Returnstate returned Kstop after) next).
Proof.
  intros INPUT RUN.
  destruct (gateway_actual_function_entry_side backend ge control_entry_read_context control_entry_read_ambient
    f_host_control [Vptr stream_block stream_offset] Kstop before world events returned Kstop after next INPUT RUN)
    as (entry_prefix & body_events & allocation_before & allocation_world & environment & temporaries & allocated &
      EVENTS & QUIET & PREFIX & CONTEXT & ENTRY & BODY).
  destruct (actual_control_entry_canonical ge allocation_before (Vptr stream_block stream_offset)
    environment temporaries allocated ENTRY)
    as (command & ENV & TEMPS & ALLOC & FRESH & PERMISSION & FRAME); subst environment temporaries.
  pose proof (control_entry_allocated command allocation_before allocation_world allocated CONTEXT ALLOC) as ALLOCATED.
  destruct (gateway_uniform_edge_side_cut backend ge (control_entry_buffer_context command)
    (control_entry_buffer_ambient command)
    (State f_host_control (fn_body f_host_control) Kstop (control_environment command)
      (control_temporaries (Vptr stream_block stream_offset)) allocated)
    (State f_host_control control_entry_guard (Kseq control_after_guard Kstop) (control_environment command)
      (control_temporaries (Vptr stream_block stream_offset)) allocated)
    allocated allocation_world body_events returned after next ltac:(cbn; tauto)
    ltac:(intro memory; apply unchanged_store_edge; rewrite actual_control_body_structure; apply edge_seq)
    ALLOCATED BODY)
    as (pending & rest & memory & guard_world & BODY_EVENTS & AMBIENT & GUARD_PREFIX & READY & GUARD).
  assert (PROFILE : gateway_guard_source _stream (Vptr stream_block stream_offset)
    (Kseq control_after_guard Kstop) (control_environment command)
    (State f_host_control control_entry_guard (Kseq control_after_guard Kstop) (control_environment command)
      (control_temporaries (Vptr stream_block stream_offset)) memory)).
  { cbn [gateway_guard_source]; split; [reflexivity |]. split; [apply PTree.gss |].
    split; [exact actual_control_guard_classification | constructor]. }
  destruct (gateway_guard_silent_terminal_cut backend ge io (stream_descriptor initial)
    (control_entry_buffer_context command) (control_entry_guard_runtime command) (control_entry_guard_silent command)
    f_host_control _stream (Vptr stream_block stream_offset) control_after_guard (control_environment command)
    _ guard_world rest returned after next actual_control_after_guard_is_mutating PROFILE eq_refl READY GUARD)
    as (guard_prefix & suffix & reached & reached_world & GUARD_EVENTS & EMPTY & GUARD_PATH & SCOPE &
      IDENTITY & REACHED & TERMINAL & SUFFIX).
  set (prefix := entry_prefix ++ gateway_source E0 :: (pending ++ gateway_source E0 :: guard_prefix)).
  exists prefix, suffix, command, reached, reached_world.
  split.
  - unfold prefix; rewrite EVENTS, BODY_EVENTS, GUARD_EVENTS; repeat rewrite <- app_assoc; cbn;
      repeat rewrite <- app_assoc; cbn; reflexivity.
  - split.
    + assert (ENTRY_EMPTY : gateway_received_bytes io (stream_descriptor initial) entry_prefix = []) by
        (apply gateway_quiet_received_empty; exact QUIET).
      assert (PENDING_EMPTY : gateway_received_bytes io (stream_descriptor initial) pending = []).
      { apply gateway_quiet_received_empty; eapply Forall_impl; [|exact AMBIENT].
        intros event SAME; right; exact SAME. }
      unfold prefix; repeat rewrite gateway_received_bytes_append; rewrite ENTRY_EMPTY.
      cbn [app]; rewrite gateway_received_source_cons, gateway_received_bytes_append,
        gateway_received_source_cons, PENDING_EMPTY, EMPTY; reflexivity.
    + split; [exact REACHED |]. split; [exact SCOPE |]. split; [exact IDENTITY |].
      split; [exact TERMINAL |]. split; [|exact SUFFIX].
      eapply gateway_steps_append; [exact PREFIX |].
      econstructor; [apply gateway_internal; [exact I | apply step_internal_function; exact ENTRY] |].
      eapply gateway_steps_append; [exact GUARD_PREFIX |].
      econstructor; [apply gateway_internal; [exact I | apply step_seq] | exact GUARD_PATH].
Qed.

End CancellationEntryBuffers.
