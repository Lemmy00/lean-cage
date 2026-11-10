(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The pending wait derives its exact operands from actual reap entry. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayThreadRuntime GatewayStreamInterface
  GatewayEntryFrontier GatewayReapAllocation GatewayReapContext GatewayReapSource GatewayReapFirstWait
  GatewayCallerBuffers GatewayCallerFamily GatewayClockModeInterface GatewayFramedRuntime GatewayExchangeABI
  GatewayTransferMath GatewayGuardObservation GatewayPrimitiveCalls GatewayReapClockSource.
Import ListNotations.

Theorem gateway_actual_completed_reap_first_wait {World Event}(backend:gateway_backend World Event)
    io native stable discipline thread_errno
    (thread:gateway_thread_runtime backend io native stable discipline thread_errno)saved
    (clock:gateway_clock_mode_operation backend io native stable discipline(Some saved))
    readonly selected reference owner child before world events target_arguments target_environment target_temporaries after next descriptor:
  discipline(Some saved)before world->
  gateway_caller_family native stable readonly selected reference owner before world->(exists target,selected target)->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_engine_reap)[Vint child;Vint Int.one]Kstop before)world)events
    (gateway_live(Callstate gateway_waitpid_definition target_arguments
      (reap_wait_cont target_environment target_temporaries)after)next)->
  exists prefix rest slots allocation_before allocation_world allocated returned memory current,
    events=prefix++rest /\gateway_received_bytes io descriptor prefix=[] /\
    reap_allocations allocation_before slots allocated /\
    gateway_reap_context native stable discipline saved slots allocated allocation_world
      readonly selected reference owner memory current /\
    native current(reap_status_slot slots) /\gateway_native_pointer memory(reap_status_slot slots)Ptrofs.zero 4 Writable /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(Internal f_host_engine_reap)[Vint child;Vint Int.one]Kstop before)world)prefix
      (gateway_live(Callstate gateway_waitpid_definition[Vint child;Vptr(reap_status_slot slots)Ptrofs.zero;Vint Int.one]
        (reap_wait_cont(reap_environment slots)(reap_began_temporaries(reap_parameters child Int.one)returned))memory)current) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate gateway_waitpid_definition[Vint child;Vptr(reap_status_slot slots)Ptrofs.zero;Vint Int.one]
        (reap_wait_cont(reap_environment slots)(reap_began_temporaries(reap_parameters child Int.one)returned))memory)current)rest
      (gateway_live(Callstate gateway_waitpid_definition target_arguments
        (reap_wait_cont target_environment target_temporaries)after)next).
Proof.
  intros SIDE FAMILY NONEMPTY RUN.
  set(input:=fun memory world=>discipline(Some saved)memory world /\
    gateway_caller_family native stable readonly selected reference owner memory world).
  assert(CLOSED:gateway_ambient_closed backend input).
  { intros memory current changed future[HELD HISTORY]INTERFERENCE.
    destruct(gateway_thread_ambient _ _ _ _ _ _ thread(Some saved)memory current changed future HELD INTERFERENCE)
      as[AFTER[ACCESS FRAME]]. split;[exact AFTER|].
    intros target SELECTED;eapply gateway_caller_buffers_no_output;[exact(HISTORY target SELECTED)|exact ACCESS|exact FRAME]. }
  destruct(gateway_actual_entry_before_frontier backend(Clight.globalenv prog)input CLOSED
    f_host_engine_reap[Vint child;Vint Int.one]Kstop before world events
    (Callstate gateway_waitpid_definition target_arguments(reap_wait_cont target_environment target_temporaries)after)next
    ltac:(intros memory BAD;discriminate) (conj SIDE FAMILY)RUN)
    as(entry_prefix&body_events&allocation_before&allocation_world&environment&temporaries&allocated&
      EVENTS1&AMBIENT&PREFIX&[ENTRY_SIDE ENTRY_FAMILY]&ENTRY&BODY).
  destruct(gateway_reap_context_allocated backend io native stable discipline thread_errno thread saved
    allocation_before allocation_world child Int.one environment temporaries allocated readonly selected reference owner
    ENTRY_SIDE ENTRY_FAMILY NONEMPTY ENTRY)as(slots&ENV&TEMPS&ALLOC&CONTEXT);subst environment temporaries.
  assert(COMPLETE:(reap_parameters child Int.one)!_complete=Some(Vint Int.one))by apply PTree.gss.
  assert(CHILD:(reap_parameters child Int.one)!_child=Some(Vint child)).
  { unfold reap_parameters;rewrite PTree.gso by discriminate;apply PTree.gss. }
  destruct(actual_reap_body_first_wait backend io native stable discipline thread_errno thread saved clock
    slots allocated allocation_world readonly selected reference owner(reap_environment slots)(reap_parameters child Int.one)
    child allocated allocation_world body_events target_arguments target_environment target_temporaries after next descriptor
    eq_refl COMPLETE CHILD CONTEXT NONEMPTY BODY)
    as(body_prefix&rest&returned&memory&current&EVENTS2&EMPTY&WAIT_CONTEXT&WAIT_PREFIX&REST).
  destruct(gateway_reap_status_pointer native stable discipline saved slots allocated allocation_world
    readonly selected reference owner memory current allocation_before ALLOC WAIT_CONTEXT)as[PRIVATE POINTER].
  exists(entry_prefix++gateway_source E0::body_prefix),rest,slots,allocation_before,allocation_world,allocated,returned,memory,current.
  split;[rewrite EVENTS1,EVENTS2;rewrite <-app_assoc;reflexivity|]. split.
  - rewrite gateway_received_bytes_append,gateway_received_source_cons,EMPTY.
    rewrite app_nil_r.
    apply gateway_quiet_received_empty;eapply Forall_impl;[|exact AMBIENT];intros event SAME;right;exact SAME.
  - split;[exact ALLOC|]. split;[exact WAIT_CONTEXT|]. split;[exact PRIVATE|]. split;[exact POINTER|]. split;[|exact REST].
    eapply gateway_steps_append;[exact PREFIX|].
    econstructor;[apply gateway_internal;[exact I|apply step_internal_function;exact ENTRY]|exact WAIT_PREFIX].
Qed.
