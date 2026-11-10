(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: Reaping clocks preserve the caller's actual saved thread token. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Events Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewayThreadRuntime GatewayStreamInterface
  GatewayCallerBuffers GatewayCallerFamily GatewayClock GatewayClockModeInterface GatewayClockModeRuntime GatewayCallerModeClock.
Import ListNotations.

Theorem gateway_actual_detached_clock {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (thread:gateway_thread_runtime backend io native stable discipline thread_errno)saved
    (clock_operation:gateway_clock_mode_operation backend io native stable discipline(Some saved))
    readonly selected reference owner before world events returned after next descriptor:
  discipline(Some saved)before world->
  gateway_caller_family native stable readonly selected reference owner before world->(exists target,selected target)->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_now)[]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next)->
  discipline(Some saved)after next /\
  gateway_caller_family native stable readonly selected reference owner after next /\gateway_received_bytes io descriptor events=[].
Proof.
  intros SIDE HISTORY NONEMPTY RUN.
  assert(BINDING:gateway_function_binding(Clight.globalenv prog)_clock_gettime clock_gettime_definition).
  { apply gateway_actual_function_binding;vm_compute;reflexivity. }
  destruct BINDING as[symbol[SYMBOL FUNCTION]].
  assert(AFTER:discipline(Some saved)after next).
  { eapply mode_actual_clock_preserves_thread;
      [exact thread|exact clock_operation|exact actual_clock_sample_size|exact SYMBOL|exact FUNCTION|exact SIDE|exact RUN]. }
  split;[exact AFTER|]. split.
  - intros target SELECTED.
    destruct(actual_caller_mode_clock_complete backend(Clight.globalenv prog)io native stable discipline thread_errno thread
      (Some saved)clock_operation readonly target reference owner before world events returned after next symbol descriptor
      actual_clock_sample_size SYMBOL FUNCTION(conj SIDE(HISTORY target SELECTED))RUN)as[FINAL EMPTY].
    exact(proj2 FINAL).
  - destruct NONEMPTY as[target SELECTED].
    destruct(actual_caller_mode_clock_complete backend(Clight.globalenv prog)io native stable discipline thread_errno thread
      (Some saved)clock_operation readonly target reference owner before world events returned after next symbol descriptor
      actual_clock_sample_size SYMBOL FUNCTION(conj SIDE(HISTORY target SELECTED))RUN)as[FINAL EMPTY].
    exact EMPTY.
Qed.
