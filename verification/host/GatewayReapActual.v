(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The real reap call preserves its original caller's received facts. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayThreadRuntime GatewayStreamInterface GatewayReadonly
  GatewayReapRuntime GatewayReapAllocation GatewayReapContext GatewayReapScope GatewayReapStructure GatewayReapState
  GatewayReapComplete GatewayCallerBuffers GatewayCallerFamily GatewayClockModeInterface GatewayFramedRuntime
  GatewayPrimitiveCalls GatewayTransferMath GatewayGuardObservation GatewayLocalRuntime GatewayOperations.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_actual_reap {World Event}(backend:gateway_backend World Event)io observation native stable discipline thread_errno
    (thread:gateway_thread_runtime backend io native stable discipline thread_errno)
    (runtime:gateway_reap_runtime backend io observation native stable discipline thread_errno)saved
    (clock:gateway_clock_mode_operation backend io native stable discipline(Some saved))
    readonly selected reference owner child complete before world events returned after next descriptor:
  0<Int.signed child->discipline(Some saved)before world->
  gateway_caller_family native stable readonly selected reference owner before world->(exists target,selected target)->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_engine_reap)[Vint child;Vint complete]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next)->
  discipline(Some saved)after next /\gateway_caller_family native stable readonly selected reference owner after next /\
    gateway_received_bytes io descriptor events=[].
Proof.
  intros CHILD SIDE FAMILY NONEMPTY RUN.
  set(input:=fun memory world=>discipline(Some saved)memory world /\
    gateway_caller_family native stable readonly selected reference owner memory world).
  assert(CLOSED:gateway_runtime_discipline backend input).
  { intros memory current changed future[HELD HISTORY]INTERFERENCE.
    destruct(gateway_thread_ambient _ _ _ _ _ _ thread(Some saved)memory current changed future HELD INTERFERENCE)
      as[AFTER[ACCESS FRAME]]. split;[exact AFTER|].
    intros target SELECTED;eapply gateway_caller_buffers_no_output;[exact(HISTORY target SELECTED)|exact ACCESS|exact FRAME]. }
  destruct(gateway_actual_function_entry_side backend(Clight.globalenv prog)input CLOSED f_host_engine_reap
    [Vint child;Vint complete]Kstop before world events returned Kstop after next(conj SIDE FAMILY)RUN)
    as(entry_prefix&body_events&allocation_before&allocation_world&environment&temporaries&allocated&
      EVENTS&QUIET&PREFIX&[ENTRY_SIDE ENTRY_FAMILY]&ENTRY&BODY).
  destruct(actual_reap_entry_allocates allocation_before child complete environment temporaries allocated ENTRY)
    as(slots&ENV&TEMPS&ALLOC&STATUS_FRESH&PAUSE_FRESH&SEPARATE&STATUS_PERMISSION&PAUSE_PERMISSION&FRAME).
  subst environment temporaries.
  pose proof(gateway_actual_reap_scope native stable readonly selected reference owner allocation_before allocation_world slots
    ENTRY_FAMILY NONEMPTY STATUS_FRESH PAUSE_FRESH)as SCOPE.
  destruct(reap_allocations_thread backend io native stable discipline thread_errno thread(Some saved)
    allocation_before allocation_world slots allocated readonly selected reference owner ENTRY_SIDE ALLOC ENTRY_FAMILY)
    as[ALLOCATED_SIDE[ENVIRONMENT ALLOCATED_FAMILY]].
  assert(LOCAL_FAMILY:gateway_caller_family native stable readonly(gateway_reap_selected slots)allocated allocation_world allocated allocation_world).
  { apply gateway_caller_family_refl.
    - intros target[STATUS|PAUSE];subst target.
      + apply(ENVIRONMENT _status(reap_status_slot slots)tint);unfold reap_environment;
          rewrite PTree.gso by discriminate;apply PTree.gss.
      + apply(ENVIRONMENT _pause(reap_pause_slot slots)(Tstruct _timespec noattr));apply PTree.gss.
    - destruct NONEMPTY as[target SELECTED];exact(proj1(proj2(proj2(ALLOCATED_FAMILY target SELECTED)))). }
  assert(INITIAL:gateway_reap_assertion native stable discipline saved slots allocated allocation_world
    readonly selected reference owner child
    (State f_host_engine_reap(fn_body f_host_engine_reap)Kstop(reap_environment slots)(reap_parameters child complete)allocated)allocation_world).
  { apply gateway_reap_assertion_context.
    - split;[reflexivity|]. split;[reflexivity|]. split.
      + unfold reap_parameters;rewrite PTree.gso by discriminate;apply PTree.gss.
      + split;[exact actual_reap_statement_profile|exact I].
    - split;[exact ALLOCATED_SIDE|]. split;assumption. }
  destruct(gateway_actual_reap_body_complete backend io observation native stable discipline thread_errno thread runtime saved clock
    slots allocated allocation_world readonly selected reference owner allocation_before child _ allocation_world body_events
    returned after next descriptor ALLOC SCOPE CHILD NONEMPTY INITIAL BODY)as[AFTER[HISTORY EMPTY]].
  split;[exact AFTER|]. split;[exact HISTORY|].
  rewrite EVENTS,gateway_received_bytes_append,gateway_received_source_cons,EMPTY,app_nil_r.
  apply gateway_quiet_received_empty;exact QUIET.
Qed.
