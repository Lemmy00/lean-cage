(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Clock source aftermath retains actual interpreter ownership. *)
From Stdlib Require Import ZArith List Bool Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine ClightSteps StoreSteps.
From HostGateway Require Import GatewaySource GatewayMachine GatewayClock GatewayThreadRuntime
  GatewayLocalRuntime GatewayRuntimeCuts GatewayReadonly GatewayStreamInterface GatewayOperations
  GatewayCallPath GatewayRuntime GatewayContexts.
Import ListNotations.
Open Scope Z_scope.

Definition clock_returned_temporaries (status : int) :=
  set_opttemp (Some _t'1) (Vint status) clock_temporaries.

Definition clock_return_cont := Kseq clock_call_test (Kseq clock_sample_guard (Kseq clock_after_guard Kstop)).

Lemma actual_clock_after_api_readonly :
  gateway_readonly_cont clock_return_cont = true.
Proof. reflexivity. Qed.

Section ClockRuntime.
Context {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (io : Event -> option gateway_native_io)
    (native_private : World -> block -> Prop) (stable_readonly : World -> block -> Z -> Prop)
    (discipline : option val -> mem -> World -> Prop) (thread_errno : World -> int).
Context (runtime : gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).

(* This is the real return from clock_gettime to its actual source continuation.
   Its subsequent branches contain no API calls. Local frees are justified from
   their actual private scope; no whole clock/helper frame is supplied. *)
Theorem actual_clock_after_api_side sample memory world events status returned after next :
  discipline None memory world ->
  gateway_native_environment native_private world memory (clock_environment sample) ->
  gateway_steps backend ge
    (gateway_live (Returnstate (Vint status) (clock_api_cont sample Kstop) memory) world) events
    (gateway_live (Returnstate returned Kstop after) next) -> discipline None after next.
Proof.
  intros SIDE PRIVATE RUN.
  set (ready := fun memory world => discipline None memory world /\
    gateway_native_environment native_private world memory (clock_environment sample)).
  assert (DISCIPLINE : gateway_runtime_discipline backend ready).
  { eapply gateway_local_runtime_discipline; exact runtime. }
  destruct (gateway_uniform_edge_side_cut backend ge ready DISCIPLINE
    (Returnstate (Vint status) (clock_api_cont sample Kstop) memory)
    (State f_host_now Sskip clock_return_cont (clock_environment sample)
      (clock_returned_temporaries status) memory)
    memory world events returned after next
    ltac:(cbn; tauto)
    ltac:(intro another; apply unchanged_store_edge, edge_returnstate)
    ltac:(split; assumption) RUN)
    as [pending [rest [called_memory [called_world [EVENTS [AMBIENT [PREFIX [READY SUFFIX]]]]]]]].
  destruct READY as [SIDE_AFTER PRIVATE_AFTER].
  eapply gateway_local_readonly_run_side with
    (source := State f_host_now Sskip clock_return_cont (clock_environment sample)
      (clock_returned_temporaries status) called_memory);
    [exact runtime | | exact SIDE_AFTER | exact SUFFIX].
  cbn [gateway_local_readonly_source gateway_replace_memory gateway_readonly_statement].
  split; [reflexivity |]. split; [exact actual_clock_after_api_readonly | exact PRIVATE_AFTER].
Qed.

Definition clock_sample_ready sample memory world : Prop :=
  discipline None memory world /\ native_private world sample /\
  Mem.range_perm memory sample 0 16 Cur Freeable.

Lemma clock_sample_ready_valid sample memory world :
  clock_sample_ready sample memory world -> Mem.valid_block memory sample.
Proof.
  intros [_ [_ BUFFER]]; eapply Mem.perm_valid_block; apply (BUFFER 0); lia.
Qed.

Lemma clock_sample_ready_discipline sample : gateway_runtime_discipline backend (clock_sample_ready sample).
Proof.
  intros before world after next READY INTERFERENCE.
  destruct READY as [SIDE [PRIVATE BUFFER]].
  destruct (gateway_thread_ambient _ _ _ _ _ _ runtime None _ _ _ _ SIDE INTERFERENCE)
    as [SIDE_AFTER [[NATIVE STABLE] FRAME]].
  split; [exact SIDE_AFTER |]. split.
  - apply NATIVE; [apply (clock_sample_ready_valid sample before world); split; [exact SIDE | split; assumption] |
      exact PRIVATE].
  - intros position RANGE; eapply Mem.perm_unchanged_on; [exact FRAME | | apply BUFFER; exact RANGE].
    split; [left; exact PRIVATE | unfold gateway_native_no_output; tauto].
Qed.

(* §FS-host-boundary.caller: The clock API's output authority comes from its actual source stack. *)
Theorem actual_clock_ready_call before world events returned after next symbol :
  sizeof (genv_cenv ge) clock_sample_type = 16 ->
  Genv.find_symbol ge _clock_gettime = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some clock_gettime_definition ->
  discipline None before world ->
  gateway_steps backend ge (gateway_live (Callstate (Internal f_host_now) [] Kstop before) world) events
    (gateway_live (Returnstate returned Kstop after) next) ->
  exists prefix suffix sample memory called_world,
    events = prefix ++ suffix /\ clock_sample_ready sample memory called_world /\
    gateway_steps backend ge (gateway_live (Callstate (Internal f_host_now) [] Kstop before) world) prefix
      (gateway_live (Callstate clock_gettime_definition [Vint Int.one; Vptr sample Ptrofs.zero]
        (clock_api_cont sample Kstop) memory) called_world) /\
    gateway_steps backend ge
      (gateway_live (Callstate clock_gettime_definition [Vint Int.one; Vptr sample Ptrofs.zero]
        (clock_api_cont sample Kstop) memory) called_world) suffix
      (gateway_live (Returnstate returned Kstop after) next).
Proof.
  intros SIZE SYMBOL FUNCTION SIDE RUN.
  assert (ENTRY_DISCIPLINE : gateway_runtime_discipline backend (discipline None)).
  { intros first current changed other HELD AMBIENT.
    exact (proj1 (gateway_thread_ambient _ _ _ _ _ _ runtime None _ _ _ _ HELD AMBIENT)). }
  destruct (gateway_actual_function_entry_side backend ge (discipline None) ENTRY_DISCIPLINE
    f_host_now [] Kstop before world events returned Kstop after next SIDE RUN)
    as [entry_prefix [body_events [allocation_before [allocation_world [environment [temporaries
      [allocated [EVENTS [QUIET [PREFIX [HELD [ENTRY BODY]]]]]]]]]]]].
  destruct (clock_actual_entry_canonical ge allocation_before environment temporaries allocated ENTRY)
    as [sample [ENV [TEMPS [ALLOC [FRESH [PERMISSION FRAME]]]]]]; subst environment temporaries.
  assert (ALLOCATED_READY : clock_sample_ready sample allocated allocation_world).
  { split.
    - eapply gateway_thread_native_alloc; [exact runtime | exact HELD | exact ALLOC].
    - split.
      + eapply gateway_thread_fresh_native; [exact runtime | exact HELD | exact FRESH].
      + rewrite SIZE in PERMISSION; exact PERMISSION. }
  destruct (gateway_retained_call_ready_cut backend ge (clock_sample_ready sample)
    (clock_sample_ready_discipline sample) clock_gettime_definition
    [Vint Int.one; Vptr sample Ptrofs.zero] (clock_api_cont sample Kstop)
    (State f_host_now (fn_body f_host_now) Kstop (clock_environment sample) clock_temporaries allocated)
    allocation_world body_events returned after next
    (clock_body_first_call_retained ge sample allocated Kstop symbol SYMBOL FUNCTION) ALLOCATED_READY BODY)
    as [body_prefix [suffix [memory [called_world [BODY_EVENTS [BODY_QUIET [CALL [READY REST]]]]]]]].
  exists (entry_prefix ++ gateway_source E0 :: body_prefix), suffix, sample, memory, called_world.
  split; [rewrite EVENTS, BODY_EVENTS; rewrite <- app_assoc; reflexivity |].
  split; [exact READY |]. split; [| exact REST].
  eapply gateway_steps_append; [exact PREFIX |].
  econstructor; [apply gateway_internal; [exact I | apply step_internal_function; exact ENTRY] | exact CALL].
Qed.

Lemma clock_sample_ready_pointer sample memory world :
  clock_sample_ready sample memory world -> gateway_native_pointer memory sample Ptrofs.zero 16 Writable.
Proof.
  intro READY; destruct READY as [SIDE [PRIVATE BUFFER]].
  split; [lia |]. split; [change (16 <= 18446744073709551616); lia |]. split.
  - apply (clock_sample_ready_valid sample memory world); split; [exact SIDE | split; assumption].
  - intros position RANGE; change (0 <= position < 16) in RANGE.
    eapply Mem.perm_implies; [apply BUFFER; exact RANGE | constructor].
Qed.

Lemma clock_external_retains_ready sample before world events returned after next :
  clock_sample_ready sample before world ->
  gateway_steps backend ge
    (gateway_live (Callstate clock_gettime_definition [Vint Int.one; Vptr sample Ptrofs.zero] Kstop before) world)
    events (gateway_live (Returnstate returned Kstop after) next) ->
  exists status, returned = Vint status /\ clock_sample_ready sample after next.
Proof.
  intros READY RUN.
  destruct (gateway_external_operation_of_run backend ge _ _ _ _ _ before world events returned after next RUN)
    as [pending [suffix [memory [called [changed [primitive [observed
      [EVENTS [PENDING [PREFIX [OPERATION RETURNED]]]]]]]]]]].
  assert (CALLED : clock_sample_ready sample memory called).
  { eapply gateway_pending_run_ready with
      (source := Callstate clock_gettime_definition [Vint Int.one; Vptr sample Ptrofs.zero] Kstop before);
      [apply clock_sample_ready_discipline | exact READY | exact PENDING | exact PREFIX]. }
  assert (RAW : gateway_runtime_operation backend clock_gettime_definition
    [Vint Int.one; Vptr sample Ptrofs.zero] memory called returned changed primitive observed) by exact OPERATION.
  destruct CALLED as [HELD [PRIVATE BUFFER]].
  destruct (gateway_clock_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ HELD PRIVATE
    (clock_sample_ready_pointer sample memory called (conj HELD (conj PRIVATE BUFFER))) RAW)
    as [status [VALUE [SAMPLE [HELD_AFTER [[NATIVE STABLE] [PERMISSIONS [FRAME IO]]]]]]].
  subst returned.
  assert (AFTER_OPERATION : clock_sample_ready sample changed primitive).
  { split; [exact HELD_AFTER |]. split.
    - apply NATIVE; [apply (clock_sample_ready_valid sample memory called); split; [exact HELD | split; assumption] |
        exact PRIVATE].
    - intros position RANGE; apply (proj1 (PERMISSIONS position Cur Freeable ltac:(cbn; exact RANGE))).
      apply BUFFER; exact RANGE. }
  exists status; split; [reflexivity |].
  eapply gateway_readonly_run_side with (source := Returnstate (Vint status) Kstop changed).
  - apply clock_sample_ready_discipline.
  - exact I.
  - exact AFTER_OPERATION.
  - exact RETURNED.
Qed.

Lemma clock_ready_environment sample memory world :
  clock_sample_ready sample memory world ->
  gateway_native_environment native_private world memory (clock_environment sample).
Proof.
  intros READY identifier object ty LOOK; unfold clock_environment in LOOK.
  destruct (peq identifier _sample) as [SAME | DIFFERENT].
  - subst identifier; rewrite PTree.gss in LOOK; inversion LOOK; subst.
    split; [eapply clock_sample_ready_valid; exact READY | exact (proj1 (proj2 READY))].
  - rewrite PTree.gso in LOOK by exact DIFFERENT; rewrite PTree.gempty in LOOK; discriminate.
Qed.

(* §FS-host-boundary.caller: The full actual clock helper retains its thread through the real API. *)
Theorem actual_clock_preserves_thread before world events returned after next symbol :
  sizeof (genv_cenv ge) clock_sample_type = 16 ->
  Genv.find_symbol ge _clock_gettime = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some clock_gettime_definition ->
  discipline None before world ->
  gateway_steps backend ge (gateway_live (Callstate (Internal f_host_now) [] Kstop before) world) events
    (gateway_live (Returnstate returned Kstop after) next) -> discipline None after next.
Proof.
  intros SIZE SYMBOL FUNCTION SIDE RUN.
  destruct (actual_clock_ready_call before world events returned after next symbol SIZE SYMBOL FUNCTION SIDE RUN)
    as [prefix [suffix [sample [memory [called [EVENTS [READY [PREFIX SUFFIX]]]]]]]].
  destruct (gateway_return_cut backend ge clock_gettime_definition [Vint Int.one; Vptr sample Ptrofs.zero]
    (clock_api_cont sample Kstop) memory called suffix (Returnstate returned Kstop after) next
    ltac:(reflexivity) ltac:(cbn [gateway_cont_weight gateway_continuation clock_api_cont]; lia) SUFFIX)
    as [operation [rest [value [returned_memory [returned_world [SPLIT [OPERATION REST]]]]]]].
  destruct (clock_external_retains_ready sample memory called operation value returned_memory returned_world
    READY OPERATION) as [status [VALUE RETURNED_READY]]; subst value.
  eapply actual_clock_after_api_side; [exact (proj1 RETURNED_READY) | | exact REST].
  apply clock_ready_environment; exact RETURNED_READY.
Qed.

End ClockRuntime.
