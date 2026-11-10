(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A pending original wait is reached through the real detached clock. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewayReapABI GatewayExchangeABI
  GatewayThreadRuntime GatewayStreamInterface GatewayReapAllocation GatewayReapContext GatewayClockModeInterface
  GatewayReapSource GatewayReapClockSource GatewayMemoryPrefixes GatewayReturnFrontier GatewayReadonly
  GatewayPrimitiveCalls GatewayFramedRuntime GatewayGuardObservation GatewayContexts GatewayTransferMath.
Import ListNotations.

Theorem actual_reap_body_first_wait {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (thread:gateway_thread_runtime backend io native stable discipline thread_errno)saved
    (clock:gateway_clock_mode_operation backend io native stable discipline(Some saved))
    slots allocated allocation_world readonly selected reference owner environment temporaries child before world events
    target_arguments target_environment target_temporaries after next descriptor:
  environment=reap_environment slots->temporaries!_complete=Some(Vint Int.one)->temporaries!_child=Some(Vint child)->
  gateway_reap_context native stable discipline saved slots allocated allocation_world
    readonly selected reference owner before world->(exists target,selected target)->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_engine_reap(fn_body f_host_engine_reap)Kstop environment temporaries before)world)events
    (gateway_live(Callstate gateway_waitpid_definition target_arguments
      (reap_wait_cont target_environment target_temporaries)after)next)->
  exists prefix rest returned memory current,
    events=prefix++rest /\gateway_received_bytes io descriptor prefix=[] /\
    gateway_reap_context native stable discipline saved slots allocated allocation_world
      readonly selected reference owner memory current /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_engine_reap(fn_body f_host_engine_reap)Kstop environment temporaries before)world)prefix
      (gateway_live(Callstate gateway_waitpid_definition[Vint child;Vptr(reap_status_slot slots)Ptrofs.zero;Vint Int.one]
        (reap_wait_cont environment(reap_began_temporaries temporaries returned))memory)current) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate gateway_waitpid_definition[Vint child;Vptr(reap_status_slot slots)Ptrofs.zero;Vint Int.one]
        (reap_wait_cont environment(reap_began_temporaries temporaries returned))memory)current)rest
      (gateway_live(Callstate gateway_waitpid_definition target_arguments
        (reap_wait_cont target_environment target_temporaries)after)next).
Proof.
  intros ENV COMPLETE CHILD READY NONEMPTY RUN;subst environment.
  set(context:=gateway_reap_context native stable discipline saved slots allocated allocation_world
    readonly selected reference owner).
  assert(CLOSED:gateway_ambient_closed backend context).
  { apply gateway_reap_context_ambient with(io:=io)(thread_errno:=thread_errno);exact thread. }
  assert(CLOCK_BINDING:gateway_function_binding(Clight.globalenv prog)_host_now(Internal f_host_now)).
  { apply gateway_actual_function_binding;vm_compute;reflexivity. }
  assert(WAIT_BINDING:gateway_function_binding(Clight.globalenv prog)_waitpid gateway_waitpid_definition).
  { apply gateway_actual_function_binding;vm_compute;reflexivity. }
  assert(CLOCK_LOCAL:(reap_environment slots)!_host_now=None)by reflexivity.
  assert(WAIT_LOCAL:(reap_environment slots)!_waitpid=None)by reflexivity.
  assert(STATUS_LOCAL:(reap_environment slots)!_status=Some(reap_status_slot slots,tint)).
  { unfold reap_environment;rewrite PTree.gso by discriminate;apply PTree.gss. }
  pose proof(actual_reap_completed_initial_prefix backend(Clight.globalenv prog)context CLOSED
    (reap_environment slots)temporaries before COMPLETE CLOCK_LOCAL CLOCK_BINDING)as SCRIPT.
  destruct(gateway_memory_prefix_cut backend(Clight.globalenv prog)
    (Callstate(Internal f_host_now)[](reap_clock_cont(reap_environment slots)temporaries)before)context context
    (State f_host_engine_reap(fn_body f_host_engine_reap)Kstop(reap_environment slots)temporaries before)
    before world events
    (Callstate gateway_waitpid_definition target_arguments(reap_wait_cont target_environment target_temporaries)after)next
    SCRIPT ltac:(exact I)READY RUN)
    as(clock_prefix&clock_suffix&clock_before&clock_world&EVENTS1&QUIET1&PREFIX1&CALLED1&SUFFIX1).
  destruct(actual_reap_clock_return_before_wait backend(Clight.globalenv prog)(reap_environment slots)temporaries
    clock_before clock_world clock_suffix target_arguments target_environment target_temporaries after next SUFFIX1)
    as(clock_events&return_events&returned&clock_after&return_world&EVENTS2&CLOCK&RETURNED).
  destruct(gateway_reap_clock_context backend io native stable discipline thread_errno thread saved clock
    slots allocated allocation_world readonly selected reference owner clock_before clock_world clock_events returned
    clock_after return_world descriptor CALLED1 NONEMPTY CLOCK)as[AFTER_CLOCK CLOCK_EMPTY].
  destruct(gateway_actual_return_before_call backend(Clight.globalenv prog)context CLOSED returned(Some _t'1)
    f_host_engine_reap(reap_environment slots)temporaries reap_clock_after clock_after return_world return_events
    gateway_waitpid_definition target_arguments(reap_wait_cont target_environment target_temporaries)after next AFTER_CLOCK RETURNED)
    as(pending&caller_events&returned_memory&returned_world&EVENTS3&AMBIENT&RETURN_PREFIX&RETURN_CONTEXT&CALLER).
  pose proof(actual_reap_after_clock_wait_prefix backend(Clight.globalenv prog)context CLOSED(reap_environment slots)
    temporaries returned returned_memory(reap_status_slot slots)child STATUS_LOCAL WAIT_LOCAL WAIT_BINDING CHILD)as WAIT_SCRIPT.
  destruct(gateway_memory_prefix_cut backend(Clight.globalenv prog)
    (Callstate gateway_waitpid_definition[Vint child;Vptr(reap_status_slot slots)Ptrofs.zero;Vint Int.one]
      (reap_wait_cont(reap_environment slots)(reap_began_temporaries temporaries returned))returned_memory)
    context context
    (State f_host_engine_reap Sskip reap_clock_after(reap_environment slots)(reap_clock_returned temporaries returned)returned_memory)
    returned_memory returned_world caller_events
    (Callstate gateway_waitpid_definition target_arguments(reap_wait_cont target_environment target_temporaries)after)next
    WAIT_SCRIPT ltac:(exact I)RETURN_CONTEXT CALLER)
    as(wait_prefix&rest&memory&current&EVENTS4&QUIET4&WAIT_PREFIX&WAIT_CONTEXT&REST).
  exists(clock_prefix++clock_events++pending++gateway_source E0::wait_prefix),rest,returned,memory,current.
  split.
  - rewrite EVENTS1,EVENTS2,EVENTS3,EVENTS4;repeat rewrite <-app_assoc;cbn[app];reflexivity.
  - split.
    + repeat rewrite gateway_received_bytes_append;rewrite gateway_received_source_cons.
      rewrite(gateway_quiet_received_empty io descriptor clock_prefix QUIET1),CLOCK_EMPTY,
        (gateway_quiet_received_empty io descriptor wait_prefix QUIET4).
      assert(EMPTY:gateway_received_bytes io descriptor pending=[]).
      { apply gateway_quiet_received_empty;eapply Forall_impl;[|exact AMBIENT];intros event SAME;right;exact SAME. }
      rewrite EMPTY;reflexivity.
    + split;[exact WAIT_CONTEXT|]. split;[|exact REST].
      eapply gateway_steps_append;[exact PREFIX1|].
      eapply gateway_steps_append.
      * exact(gateway_plug_steps backend(Clight.globalenv prog)_ _ _
          (reap_clock_cont(reap_environment slots)temporaries)I CLOCK).
      * eapply gateway_steps_append;[exact RETURN_PREFIX|].
        econstructor;[apply gateway_internal;[exact I|constructor]|exact WAIT_PREFIX].
Qed.
