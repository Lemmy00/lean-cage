(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Original cleanup reaps and reaches restoration of the SAME token. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewayThreadRuntime GatewayStreamInterface
  GatewayReapRuntime GatewayReapActual GatewayClockModeInterface GatewayCallerBuffers GatewayCallerFamily
  GatewayCleanupThreadSource GatewayCleanupRestoreSource GatewayExchangeSetup GatewaySourcePaths GatewayFramedRuntime
  GatewayContexts GatewayTransferMath GatewayPrimitiveCalls GatewayRuntimeABI.
Import ListNotations.
Open Scope Z_scope.

Theorem actual_exchange_cleanup_reap {World Event}(backend:gateway_backend World Event)io observation native stable discipline thread_errno
    (thread:gateway_thread_runtime backend io native stable discipline thread_errno)
    (runtime:gateway_reap_runtime backend io observation native stable discipline thread_errno)saved_block saved_offset
    (clock:gateway_clock_mode_operation backend io native stable discipline(Some(Vptr saved_block saved_offset)))
    readonly selected reference owner allocation_before allocated environment temporaries child before world events value after next descriptor:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  temporaries!_saved=Some(Vptr saved_block saved_offset)->0<Int.signed child->
  discipline(Some(Vptr saved_block saved_offset))before world->
  gateway_caller_family native stable readonly selected reference owner before world->(exists target,selected target)->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_engine_reap)[Vint child;Vint Int.one](cleanup_reap_cont environment temporaries)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists prefix suffix memory current,
    events=prefix++suffix /\gateway_received_bytes io descriptor prefix=[] /\
    discipline(Some(Vptr saved_block saved_offset))memory current /\
    gateway_caller_family native stable readonly selected reference owner memory current /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(Internal f_host_engine_reap)[Vint child;Vint Int.one](cleanup_reap_cont environment temporaries)before)world)prefix
      (gateway_live(Callstate gateway_restore_thread_definition[Vptr saved_block saved_offset]
        (cleanup_restore_cont environment temporaries)memory)current) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate gateway_restore_thread_definition[Vptr saved_block saved_offset]
        (cleanup_restore_cont environment temporaries)memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros ALLOC SAVED CHILD SIDE FAMILY NONEMPTY RUN.
  set(property:=fun memory world=>discipline(Some(Vptr saved_block saved_offset))memory world /\
    gateway_caller_family native stable readonly selected reference owner memory world).
  assert(CLOSED:gateway_ambient_closed backend property).
  { intros memory current changed future[HELD HISTORY]INTERFERENCE.
    destruct(gateway_thread_ambient _ _ _ _ _ _ thread(Some(Vptr saved_block saved_offset))memory current changed future HELD INTERFERENCE)
      as[AFTER[ACCESS FRAME]]. split;[exact AFTER|].
    intros target SELECTED;eapply gateway_caller_buffers_no_output;[exact(HISTORY target SELECTED)|exact ACCESS|exact FRAME]. }
  destruct(gateway_return_cut backend(Clight.globalenv prog)(Internal f_host_engine_reap)[Vint child;Vint Int.one]
    (cleanup_reap_cont environment temporaries)before world events(Returnstate value Kstop after)next I
    ltac:(cbn[gateway_continuation gateway_cont_weight cleanup_reap_cont];lia)RUN)
    as(body&caller_events&returned&changed&changed_world&EVENTS1&REAP&CALLER).
  destruct(gateway_actual_reap backend io observation native stable discipline thread_errno thread runtime
    (Vptr saved_block saved_offset)clock readonly selected reference owner child Int.one before world body returned changed changed_world descriptor
    CHILD SIDE FAMILY NONEMPTY REAP)as[RELEASED[HISTORY EMPTY]].
  assert(LOCAL:environment!_PyEval_RestoreThread=None).
  { eapply actual_exchange_setup_unshadowed;[exact ALLOC|cbn;intuition discriminate]. }
  assert(FUNCTION:gateway_function_binding(Clight.globalenv prog)_PyEval_RestoreThread gateway_restore_thread_definition).
  { apply gateway_actual_function_binding;vm_compute;reflexivity. }
  destruct(gateway_source_path_cut backend(Clight.globalenv prog)_ _ _ property _ property
    (actual_cleanup_reap_restore_path backend(Clight.globalenv prog)property CLOSED environment temporaries changed
      returned saved_block saved_offset LOCAL FUNCTION SAVED)
    changed changed_world caller_events value after next(conj RELEASED HISTORY)CALLER)
    as(prefix&suffix&memory&current&EVENTS2&QUIET&PREFIX&[CURRENT FINAL]&SUFFIX).
  exists(body++prefix),suffix,memory,current.
  split;[rewrite EVENTS1,EVENTS2;rewrite <-app_assoc;reflexivity|]. split.
  - rewrite gateway_received_bytes_append,EMPTY;apply gateway_quiet_received_empty;exact QUIET.
  - split;[exact CURRENT|]. split;[exact FINAL|]. split;[|exact SUFFIX].
    eapply gateway_steps_append;
      [exact(gateway_plug_steps backend(Clight.globalenv prog)_ _ _(cleanup_reap_cont environment temporaries)I REAP)|exact PREFIX].
Qed.
