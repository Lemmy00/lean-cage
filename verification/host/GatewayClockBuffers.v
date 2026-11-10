(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Clock output authority comes from its actual separated local. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayClock GatewayClockRuntime
  GatewayThreadRuntime GatewayStreamInterface GatewayReadContext GatewayReadMemory GatewayReadRegions
  GatewayScopedBufferRuntime GatewayScopeBufferReference GatewayBufferReference GatewayCallPath GatewayReadonly
  GatewayOperations GatewayFrames GatewayPrimitiveCalls GatewayGuardObservation GatewayTransferMath.
Import ListNotations.
Open Scope Z_scope.

Section ClockBuffers.
Context {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (io : Event -> option gateway_native_io)
    (native_private : World -> block -> Prop) (stable_readonly : World -> block -> Z -> Prop)
    (discipline : option val -> mem -> World -> Prop) (thread_errno : World -> int).
Context (runtime : gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).
Context (stream_block : block) (stream_offset : ptrofs) (initial : gateway_stream_values)
    (data_block : block) (data_offset : ptrofs) (amount : Z) (readonly : block -> Z -> Prop).
Variables (reference : mem) (owner : World).
Local Definition region := gateway_buffer_scope stream_block data_block readonly.
Local Definition history := gateway_scoped_buffer_history native_private stable_readonly discipline
  stream_block stream_offset initial data_block data_offset amount readonly reference owner.

Definition clock_buffer_ready sample memory world : Prop :=
  clock_sample_ready native_private discipline sample memory world /\ history memory world /\
    (forall position, ~ region sample position).

Lemma clock_buffer_ambient sample : gateway_runtime_discipline backend (clock_buffer_ready sample).
Proof.
  intros before world after next [SAMPLE [HISTORY SEPARATE]] INTERFERENCE; split.
  - eapply clock_sample_ready_discipline; [exact runtime | exact SAMPLE | exact INTERFERENCE].
  - split; [|exact SEPARATE].
    exact (gateway_owned_buffer_context_ambient backend io native_private stable_readonly discipline thread_errno runtime
      stream_block data_block stream_offset data_offset initial amount readonly reference owner None
      _ _ _ _ HISTORY INTERFERENCE).
Qed.

Lemma clock_buffer_allocated sample before world allocated :
  history before world -> Mem.alloc before 0 16 = (allocated, sample) ->
  clock_buffer_ready sample allocated world.
Proof.
  intros [INPUT [BUFFER NATIVE]] ALLOC.
  pose proof (proj2 (proj2 (proj2 (proj2 INPUT)))) as RAW.
  assert (FRESH : ~ Mem.valid_block before sample) by (eapply Mem.fresh_block_alloc; exact ALLOC).
  assert (SIDE : discipline None allocated world) by
    (eapply gateway_thread_native_alloc; [exact runtime | exact (proj1 INPUT) | exact ALLOC]).
  assert (FRAME : Mem.unchanged_on (fun _ _ => True) before allocated) by
    (eapply Mem.alloc_unchanged_on; exact ALLOC).
  split.
  - split; [exact SIDE |]. split.
    + eapply gateway_thread_fresh_native; [exact runtime | exact (proj1 INPUT) | exact FRESH].
    + intros position RANGE; eapply Mem.perm_alloc_2; eassumption.
  - split.
    + split.
      * eapply gateway_read_context_region_preserved; [exact INPUT | exact SIDE | |].
        -- split; intros; assumption.
        -- eapply Mem.unchanged_on_implies; [exact FRAME |]. intros; exact I.
      * destruct (gateway_scope_alloc_buffer native_private readonly stream_block data_block before allocated world sample
          0 16 ALLOC ltac:(eapply gateway_read_stream_live; exact RAW)
          (gateway_read_data_live _ _ _ _ _ _ _ _ RAW)) as [STEP_BUFFER STEP_NATIVE].
        split; [eapply gateway_buffer_reference_transitive | eapply gateway_native_reference_transitive]; eassumption.
    + intros position [STREAM | [DATA | IMMUTABLE]]; apply FRESH.
      * subst sample; eapply gateway_read_stream_live; exact RAW.
      * subst sample; exact (gateway_read_data_live _ _ _ _ _ _ _ _ RAW).
      * exact (gateway_read_readonly_live _ _ _ _ _ _ _ _ RAW sample position IMMUTABLE).
Qed.

Theorem actual_clock_buffer_call before world events returned after next symbol :
  sizeof (genv_cenv ge) clock_sample_type = 16 ->
  Genv.find_symbol ge _clock_gettime = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some clock_gettime_definition ->
  history before world ->
  gateway_steps backend ge (gateway_live (Callstate (Internal f_host_now) [] Kstop before) world) events
    (gateway_live (Returnstate returned Kstop after) next) ->
  exists prefix suffix sample memory current,
    events = prefix ++ suffix /\ gateway_received_bytes io (stream_descriptor initial) prefix = [] /\
    clock_buffer_ready sample memory current /\
    gateway_steps backend ge (gateway_live (Callstate (Internal f_host_now) [] Kstop before) world) prefix
      (gateway_live (Callstate clock_gettime_definition [Vint Int.one; Vptr sample Ptrofs.zero]
        (clock_api_cont sample Kstop) memory) current) /\
    gateway_steps backend ge
      (gateway_live (Callstate clock_gettime_definition [Vint Int.one; Vptr sample Ptrofs.zero]
        (clock_api_cont sample Kstop) memory) current) suffix
      (gateway_live (Returnstate returned Kstop after) next).
Proof.
  intros SIZE SYMBOL FUNCTION READY RUN.
  destruct (gateway_actual_function_entry_side backend ge history
    (gateway_owned_buffer_context_ambient backend io native_private stable_readonly discipline thread_errno runtime
      stream_block data_block stream_offset data_offset initial amount readonly reference owner None)
    f_host_now [] Kstop before world events returned Kstop after next READY RUN)
    as (entry_prefix & body_events & allocation_before & allocation_world & environment & temporaries & allocated &
      EVENTS & QUIET & PREFIX & ENTRY_CONTEXT & ENTRY & BODY).
  destruct (clock_actual_entry_canonical ge allocation_before environment temporaries allocated ENTRY)
    as (sample & ENV & TEMPS & ALLOC & FRESH & PERMISSION & FRAME); subst environment temporaries.
  rewrite SIZE in ALLOC.
  pose proof (clock_buffer_allocated sample allocation_before allocation_world allocated ENTRY_CONTEXT ALLOC) as ALLOCATED.
  destruct (gateway_retained_call_ready_cut backend ge (clock_buffer_ready sample) (clock_buffer_ambient sample)
    clock_gettime_definition [Vint Int.one; Vptr sample Ptrofs.zero] (clock_api_cont sample Kstop)
    (State f_host_now (fn_body f_host_now) Kstop (clock_environment sample) clock_temporaries allocated)
    allocation_world body_events returned after next
    (clock_body_first_call_retained ge sample allocated Kstop symbol SYMBOL FUNCTION) ALLOCATED BODY)
    as (body_prefix & suffix & memory & current & BODY_EVENTS & BODY_QUIET & CALL & CALLED & REST).
  exists (entry_prefix ++ gateway_source E0 :: body_prefix), suffix, sample, memory, current.
  split; [rewrite EVENTS, BODY_EVENTS; rewrite <- app_assoc; reflexivity |]. split.
  - rewrite gateway_received_bytes_append, gateway_received_source_cons,
      (gateway_quiet_received_empty io (stream_descriptor initial) entry_prefix QUIET),
      (gateway_quiet_received_empty io (stream_descriptor initial) body_prefix BODY_QUIET); reflexivity.
  - split; [exact CALLED |]. split; [|exact REST].
    eapply gateway_steps_append; [exact PREFIX |].
    econstructor; [apply gateway_internal; [exact I | apply step_internal_function; exact ENTRY] | exact CALL].
Qed.

End ClockBuffers.
