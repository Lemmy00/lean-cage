(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual control guard keeps its input owners and stream parameter. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps.
From HostGateway Require Import GatewaySource GatewayMachine GatewayCancellation GatewayGuardScope
  GatewayThreadRuntime GatewayStreamInterface GatewayReadMemory GatewayReadContext GatewayOperations
  GatewayReadonly GatewayRuntimeCuts GatewayFrames GatewayReadyInterface GatewayInstructions GatewayCalls
  GatewayGuardFunction.
Import ListNotations.
Open Scope Z_scope.

Section CancellationRuntime.
Context {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (io : Event -> option gateway_native_io)
    (native_private : World -> block -> Prop) (stable_readonly : World -> block -> Z -> Prop)
    (discipline : option val -> mem -> World -> Prop) (thread_errno : World -> int).
Context (runtime : gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).
Context (stream_block : block) (stream_offset : ptrofs) (initial : gateway_stream_values)
    (data_block : block) (data_offset : ptrofs) (amount : Z) (readonly : block -> Z -> Prop).

Definition control_read_context := gateway_read_context native_private stable_readonly discipline None
  stream_block stream_offset initial data_block data_offset amount readonly.

Definition control_context command memory world : Prop :=
  control_read_context memory world /\ native_private world command /\
  Mem.range_perm memory command 0 1 Cur Freeable /\
  command <> stream_block /\ command <> data_block /\ (forall position, ~ readonly command position).

Lemma control_context_command_live command memory world :
  control_context command memory world -> Mem.valid_block memory command.
Proof. intros [_ [_ [BUFFER SEPARATE]]]; eapply Mem.perm_valid_block; apply (BUFFER 0); lia. Qed.

Lemma control_context_preserved command before world after next :
  control_context command before world -> discipline None after next ->
  gateway_access_retained native_private stable_readonly before world next ->
  gateway_native_frame native_private stable_readonly gateway_native_no_output world before after ->
  control_context command after next.
Proof.
  intros CONTEXT SIDE ACCESS FRAME; destruct CONTEXT as [INPUT [PRIVATE [BUFFER SEPARATE]]].
  split; [eapply gateway_read_context_preserved; eassumption |]. split.
  - apply (proj1 ACCESS); [| exact PRIVATE].
    eapply control_context_command_live; split; [exact INPUT |]. split; [exact PRIVATE |]. split; assumption.
  - split; [| exact SEPARATE].
    intros position RANGE; eapply Mem.perm_unchanged_on; [exact FRAME | | apply BUFFER; exact RANGE].
    split; [left; exact PRIVATE | unfold gateway_native_no_output; tauto].
Qed.

Lemma control_context_ambient command : gateway_runtime_discipline backend (control_context command).
Proof.
  intros before world after next CONTEXT INTERFERENCE.
  destruct (gateway_thread_ambient _ _ _ _ _ _ runtime None _ _ _ _
    (proj1 (proj1 CONTEXT)) INTERFERENCE) as [SIDE [ACCESS FRAME]].
  eapply control_context_preserved; eassumption.
Qed.

Lemma control_context_guard_runtime command : gateway_guard_runtime backend (control_context command).
Proof.
  constructor.
  - apply control_context_ambient.
  - intros arguments before world result after next observed CONTEXT OPERATION.
    destruct (gateway_volatile_int_load _ _ _ _ _ _ runtime None _ _ _ _ _ _ _
      (proj1 (proj1 CONTEXT)) OPERATION) as [VALUE [SIDE [ACCESS [FRAME IO]]]].
    eapply control_context_preserved; eassumption.
Qed.

Lemma control_allocation_context command before world allocated :
  control_read_context before world -> Mem.alloc before 0 1 = (allocated, command) ->
  control_context command allocated world.
Proof.
  intros INPUT ALLOC.
  assert (SIDE : discipline None allocated world).
  { eapply gateway_thread_native_alloc; [exact runtime | exact (proj1 INPUT) | exact ALLOC]. }
  split.
  - eapply gateway_read_context_preserved; [exact INPUT | exact SIDE | |].
    + split; intros; assumption.
    + eapply Mem.alloc_unchanged_on; exact ALLOC.
  - split.
    + eapply gateway_thread_fresh_native; [exact runtime | exact (proj1 INPUT) |].
      eapply Mem.fresh_block_alloc; exact ALLOC.
    + split.
      * intros position RANGE; eapply Mem.perm_alloc_2; eassumption.
      * assert (FRESH : ~ Mem.valid_block before command) by (eapply Mem.fresh_block_alloc; exact ALLOC).
        pose proof (proj2 (proj2 (proj2 (proj2 INPUT)))) as RAW.
        split.
        -- intro SAME; subst command; apply FRESH; eapply gateway_read_stream_live; exact RAW.
        -- split.
           ++ intro SAME; subst command; apply FRESH; exact (gateway_read_data_live _ _ _ _ _ _ _ _ RAW).
           ++ intros position PRIVATE; apply FRESH;
                exact (gateway_read_readonly_live _ _ _ _ _ _ _ _ RAW _ _ PRIVATE).
Qed.

Lemma control_free_context command before world after :
  control_context command before world -> Mem.free before command 0 1 = Some after ->
  control_read_context after world /\
  Mem.unchanged_on (gateway_read_region stream_block stream_offset data_block data_offset amount readonly) before after.
Proof.
  intros [INPUT [PRIVATE [BUFFER [STREAM [DATA IMMUTABLE]]]]] FREE.
  assert (FRAME : Mem.unchanged_on
    (gateway_read_region stream_block stream_offset data_block data_offset amount readonly) before after).
  { eapply Mem.free_unchanged_on; [exact FREE |].
    intros position RANGE [IN_STREAM | [IN_DATA | IN_READONLY]].
    - destruct IN_STREAM as [SAME BOUNDS]; contradiction.
    - destruct IN_DATA as [SAME BOUNDS]; contradiction.
    - exact (IMMUTABLE position IN_READONLY). }
  split; [| exact FRAME].
  destruct INPUT as [SIDE [STREAM_PRIVATE [DATA_PRIVATE [STABLE RAW]]]].
  split.
  - eapply gateway_thread_native_free; [exact runtime | exact SIDE | exact PRIVATE | exact FREE].
  - split; [exact STREAM_PRIVATE |]. split; [exact DATA_PRIVATE |]. split; [exact STABLE |].
    eapply gateway_read_inputs_unchanged; eassumption.
Qed.

Lemma control_scope_free command before world after :
  control_context command before world ->
  Mem.free_list before (blocks_of_env ge (control_environment command)) = Some after ->
  control_read_context after world /\
  Mem.unchanged_on (gateway_read_region stream_block stream_offset data_block data_offset amount readonly) before after.
Proof.
  intros CONTEXT FREE.
  change (Mem.free_list before [(command, 0, 1)] = Some after) in FREE.
  cbn in FREE; destruct (Mem.free before command 0 1) as [changed |] eqn:ACTUAL; [| discriminate].
  inversion FREE; subst; eapply control_free_context; eassumption.
Qed.

Lemma control_store_context command before world after byte :
  control_context command before world ->
  Mem.store Mint8unsigned before command 0 (Vint byte) = Some after ->
  control_context command after world /\
  Mem.unchanged_on (gateway_read_region stream_block stream_offset data_block data_offset amount readonly) before after.
Proof.
  intros [INPUT [PRIVATE [BUFFER [STREAM [DATA IMMUTABLE]]]]] STORE.
  assert (FRAME : Mem.unchanged_on
    (gateway_read_region stream_block stream_offset data_block data_offset amount readonly) before after).
  { eapply Mem.store_unchanged_on; [exact STORE |].
    intros position RANGE [IN_STREAM | [IN_DATA | IN_READONLY]].
    - destruct IN_STREAM as [SAME BOUNDS]; contradiction.
    - destruct IN_DATA as [SAME BOUNDS]; contradiction.
    - exact (IMMUTABLE position IN_READONLY). }
  split; [| exact FRAME]. split.
  - destruct INPUT as [SIDE [STREAM_PRIVATE [DATA_PRIVATE [STABLE RAW]]]].
    split.
    + eapply gateway_thread_native_store; [exact runtime | exact SIDE | exact PRIVATE | exact STORE].
    + split; [exact STREAM_PRIVATE |]. split; [exact DATA_PRIVATE |]. split; [exact STABLE |].
      eapply gateway_read_inputs_unchanged; eassumption.
  - split; [exact PRIVATE |]. split.
    + intros position RANGE; eapply Mem.perm_store_1; [exact STORE | apply BUFFER; exact RANGE].
    + split; [exact STREAM |]. split; [exact DATA | exact IMMUTABLE].
Qed.

Lemma actual_control_return_branch function expression continuation command temporaries
    before world events returned after next :
  call_cont continuation = Kstop -> control_context command before world ->
  gateway_steps backend ge
    (gateway_live (State function (Sreturn expression) continuation (control_environment command) temporaries before) world)
    events (gateway_live (Returnstate returned Kstop after) next) -> control_read_context after next.
Proof.
  intros STOP CONTEXT RUN.
  destruct (gateway_source_instruction_occurrence backend ge function (Sreturn expression) continuation
    (control_environment command) temporaries before world events returned after next ltac:(cbn; tauto) RUN)
    as [prefix [suffix [memory [current [trace [target [EVENTS [AMBIENT [PREFIX [REAL SUFFIX]]]]]]]]]].
  assert (CALLED : control_context command memory current).
  { eapply gateway_ambient_run_ready with
      (source := State function (Sreturn expression) continuation (control_environment command) temporaries before);
      [apply control_context_ambient | exact CONTEXT | exact AMBIENT | exact PREFIX]. }
  inversion REAL; subst;
    try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
  all: rewrite STOP in SUFFIX.
  all: match goal with FREE : Mem.free_list ?called_memory (blocks_of_env ge (control_environment ?actual_command)) = Some ?freed |- _ =>
    destruct (control_scope_free actual_command called_memory _ freed CALLED FREE) as [READY FRAME]
  end.
  all: match type of SUFFIX with
    gateway_steps _ _ (gateway_live ?actual_source ?actual_world) _ _ =>
      eapply gateway_readonly_run_side with (source := actual_source) (world := actual_world);
        [eapply gateway_read_context_ambient; exact runtime | exact I | exact READY | exact SUFFIX]
  end.
Qed.

(* §FS-host-boundary.caller: The real helper supplies the control guard's fresh local byte. *)
Theorem actual_control_guard_source before world events returned after next :
  control_read_context before world ->
  gateway_steps backend ge
    (gateway_live (Callstate (Internal f_host_control) [Vptr stream_block stream_offset] Kstop before) world)
    events (gateway_live (Returnstate returned Kstop after) next) ->
  exists prefix suffix command reached reached_world,
    events = prefix ++ suffix /\ control_context command (memory_of reached) reached_world /\
    gateway_guard_source _stream (Vptr stream_block stream_offset) (Kseq control_after_guard Kstop)
      (control_environment command) reached /\
    gateway_guard_function f_host_control reached /\
    gateway_guard_terminal (Kseq control_after_guard Kstop) reached /\
    gateway_steps backend ge
      (gateway_live (Callstate (Internal f_host_control) [Vptr stream_block stream_offset] Kstop before) world)
      prefix (gateway_live reached reached_world) /\
    gateway_steps backend ge (gateway_live reached reached_world) suffix
      (gateway_live (Returnstate returned Kstop after) next).
Proof.
  intros INPUT RUN.
  destruct (gateway_actual_function_entry_side backend ge control_read_context
    (gateway_read_context_ambient _ _ _ _ _ _ runtime None _ _ _ _ _ _ _) f_host_control
    [Vptr stream_block stream_offset] Kstop before world events returned Kstop after next INPUT RUN)
    as [entry_prefix [body_events [allocation_before [allocation_world [environment [temporaries
      [allocated [EVENTS [QUIET [PREFIX [CONTEXT [ENTRY BODY]]]]]]]]]]]].
  destruct (actual_control_entry_canonical ge allocation_before (Vptr stream_block stream_offset)
    environment temporaries allocated ENTRY)
    as [command [ENV [TEMPS [ALLOC [FRESH [PERMISSION FRAME]]]]]]; subst environment temporaries.
  assert (ALLOCATED : control_context command allocated allocation_world).
  { eapply control_allocation_context; eassumption. }
  destruct (gateway_uniform_edge_side_cut backend ge (control_context command) (control_context_ambient command)
    (State f_host_control (fn_body f_host_control) Kstop (control_environment command)
      (control_temporaries (Vptr stream_block stream_offset)) allocated)
    (State f_host_control control_entry_guard (Kseq control_after_guard Kstop) (control_environment command)
      (control_temporaries (Vptr stream_block stream_offset)) allocated)
    allocated allocation_world body_events returned after next
    ltac:(cbn; tauto)
    ltac:(intro memory; apply unchanged_store_edge; rewrite actual_control_body_structure; apply edge_seq)
    ALLOCATED BODY)
    as [pending [rest [memory [guard_world [BODY_EVENTS [AMBIENT [GUARD_PREFIX [READY GUARD]]]]]]]].
  assert (PROFILE : gateway_guard_source _stream (Vptr stream_block stream_offset)
    (Kseq control_after_guard Kstop) (control_environment command)
    (State f_host_control control_entry_guard (Kseq control_after_guard Kstop) (control_environment command)
      (control_temporaries (Vptr stream_block stream_offset)) memory)).
  { cbn [gateway_guard_source]; split; [reflexivity |]. split.
    - apply PTree.gss.
    - split; [exact actual_control_guard_classification | constructor]. }
  destruct (gateway_guard_function_terminal_cut backend ge (control_context command) (control_context_guard_runtime command)
    f_host_control _stream (Vptr stream_block stream_offset) control_after_guard (control_environment command)
    _ guard_world rest returned after next actual_control_after_guard_is_mutating PROFILE eq_refl READY GUARD)
    as (guard_prefix & suffix & reached & reached_world & GUARD_EVENTS & GUARD_PATH & SCOPE &
      IDENTITY & REACHED & TERMINAL & SUFFIX).
  exists (entry_prefix ++ gateway_source E0 :: (pending ++ gateway_source E0 :: guard_prefix)), suffix,
    command, reached, reached_world.
  split.
  - rewrite EVENTS, BODY_EVENTS, GUARD_EVENTS; repeat rewrite <- app_assoc; cbn;
      repeat rewrite <- app_assoc; cbn; reflexivity.
  - split; [exact REACHED |]. split; [exact SCOPE |]. split; [exact IDENTITY |].
    split; [exact TERMINAL |]. split; [| exact SUFFIX].
    eapply gateway_steps_append; [exact PREFIX |].
    econstructor; [apply gateway_internal; [exact I | apply step_internal_function; exact ENTRY] |].
    eapply gateway_steps_append; [exact GUARD_PREFIX |].
    econstructor; [apply gateway_internal; [exact I | apply step_seq] | exact GUARD_PATH].
Qed.

End CancellationRuntime.
