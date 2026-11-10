(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Actual readiness entry allocates and owns its real poll record. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewayMachine GatewaySource GatewayReadySource GatewayReadyContext GatewayReadContext
  GatewayReadRegions GatewayReadMemory GatewayThreadRuntime GatewayStreamInterface GatewayBufferReference
  GatewayScopeBufferReference GatewayOperations GatewayReadonly GatewayPrimitiveCalls GatewayGuardObservation
  GatewayTransferMath.
Import ListNotations.
Open Scope Z_scope.

Section ReadyEntry.
Context {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (io : Event -> option gateway_native_io)
    (native_private : World -> block -> Prop) (stable_readonly : World -> block -> Z -> Prop)
    (discipline : option val -> mem -> World -> Prop) (thread_errno : World -> int).
Context (runtime : gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).
Context (stream_block : block) (stream_offset : ptrofs) (initial : gateway_stream_values)
    (data_block : block) (data_offset : ptrofs) (amount : Z) (readonly : block -> Z -> Prop).
Variables (reference : mem) (owner : World).
Local Definition input := gateway_owned_buffer_context native_private stable_readonly discipline
  stream_block data_block stream_offset data_offset initial amount readonly reference owner None.
Local Definition slice := gateway_ready_slice native_private stable_readonly discipline
  stream_block stream_offset initial data_block data_offset amount readonly reference owner.

Lemma actual_ready_allocated_slice before world after item :
  input before world -> Mem.alloc before 0 8 = (after, item) -> slice item None initial after world.
Proof.
  intros [INPUT [BUFFER NATIVE]] ALLOC.
  assert (FRESH : ~ Mem.valid_block before item) by (eapply Mem.fresh_block_alloc; exact ALLOC).
  assert (FRAME : Mem.unchanged_on (fun _ _ => True) before after) by (eapply Mem.alloc_unchanged_on; exact ALLOC).
  assert (RAW : gateway_read_inputs before stream_block stream_offset initial data_block data_offset amount readonly)
    by exact (proj2 (proj2 (proj2 (proj2 INPUT)))).
  split.
  - eapply gateway_read_context_region_preserved; [exact INPUT | | |].
    + eapply gateway_thread_native_alloc; [exact runtime |exact (proj1 INPUT) |exact ALLOC].
    + split; intros; assumption.
    + eapply Mem.unchanged_on_implies; [exact FRAME |]. intros; exact I.
  - split; [apply GatewayCancellationMemory.gateway_stream_transport_reflexive |]. split.
    + eapply gateway_thread_fresh_native; [exact runtime |exact (proj1 INPUT) |exact FRESH].
    + split.
      * intros position RANGE; eapply Mem.perm_alloc_2; eassumption.
      * split.
        -- intros position [FIRST |[SECOND |HERE]].
           ++ subst item; apply FRESH; eapply gateway_read_stream_live; exact RAW.
           ++ subst item; apply FRESH; exact (gateway_read_data_live _ _ _ _ _ _ _ _ RAW).
           ++ apply FRESH; exact (gateway_read_readonly_live _ _ _ _ _ _ _ _ RAW item position HERE).
        -- destruct (gateway_scope_alloc_buffer native_private readonly stream_block data_block before after world item 0 8 ALLOC
             (gateway_read_stream_live _ _ _ _ _ _ _ _ RAW) (gateway_read_data_live _ _ _ _ _ _ _ _ RAW))
             as [FBUFFER FNATIVE].
           split.
           ++ eapply gateway_buffer_reference_transitive; eassumption.
           ++ eapply gateway_native_reference_transitive; eassumption.
Qed.

Theorem actual_ready_entry_slice direction before world events returned after next :
  sizeof (genv_cenv ge) ready_item_type = 8 -> input before world ->
  gateway_steps backend ge
    (gateway_live (Callstate (Internal f_host_ready) [Vptr stream_block stream_offset; Vint direction] Kstop before) world)
    events (gateway_live (Returnstate returned Kstop after) next) ->
  exists prefix suffix memory called_world item,
    events = prefix ++ suffix /\ gateway_received_bytes io (stream_descriptor initial) prefix = [] /\
    slice item None initial memory called_world /\
    gateway_steps backend ge
      (gateway_live (Callstate (Internal f_host_ready) [Vptr stream_block stream_offset; Vint direction] Kstop before) world)
      prefix (gateway_live (State f_host_ready (fn_body f_host_ready) Kstop (ready_environment item)
        (ready_temporaries (Vptr stream_block stream_offset) direction) memory) called_world) /\
    gateway_steps backend ge
      (gateway_live (State f_host_ready (fn_body f_host_ready) Kstop (ready_environment item)
        (ready_temporaries (Vptr stream_block stream_offset) direction) memory) called_world)
      suffix (gateway_live (Returnstate returned Kstop after) next).
Proof.
  intros SIZE READY RUN.
  assert (AMBIENT : gateway_runtime_discipline backend input).
  { apply gateway_owned_buffer_context_ambient with (io := io) (thread_errno := thread_errno); exact runtime. }
  destruct (gateway_actual_function_entry_side backend ge input AMBIENT f_host_ready
    [Vptr stream_block stream_offset; Vint direction] Kstop before world events returned Kstop after next READY RUN)
    as (pending & suffix & entry_memory & called_world & environment & temporaries & allocated & EVENTS & QUIET &
      PREFIX & INPUT & ENTRY & BODY).
  destruct (actual_ready_entry_canonical ge entry_memory (Vptr stream_block stream_offset) direction
    environment temporaries allocated ENTRY) as (item & ENVIRONMENT & TEMPORARIES & ALLOC & FRESH & PERMISSIONS & FRAME).
  subst environment temporaries; rewrite SIZE in ALLOC.
  exists (pending ++ [gateway_source E0]), suffix, allocated, called_world, item.
  split; [rewrite EVENTS, <- app_assoc; reflexivity |]. split.
  - rewrite gateway_received_bytes_append, (gateway_quiet_received_empty io (stream_descriptor initial) pending QUIET); reflexivity.
  - split; [eapply actual_ready_allocated_slice; eassumption |]. split; [|exact BODY].
    eapply gateway_steps_append; [exact PREFIX |].
    econstructor; [apply gateway_internal; [exact I |apply step_internal_function; exact ENTRY] |constructor].
Qed.

End ReadyEntry.
