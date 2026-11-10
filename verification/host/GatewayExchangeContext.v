(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: One launch prefix retains its actual local storage and FD leases. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Ctypes Clight.
From HostGateway Require Import GatewayMachine GatewayThreadRuntime GatewayStreamInterface GatewayFramedRuntime
  GatewayCallerBuffers GatewayCallerFamily GatewayCallerClockResources GatewaySpawnResources GatewaySpawnRuntime
  GatewayPassiveResources GatewayClock GatewayBindings GatewayRuntimeABI GatewaySource.
Import ListNotations.

Section ExchangeContext.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
    (native_private:World->block->Prop)(stable_readonly:World->block->Z->Prop)
    (discipline:option val->mem->World->Prop)(thread_errno:World->int)
    (resources:World->gateway_resource_state)(ipc:nat->Prop).
Context(thread:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno)
    (descriptors:gateway_spawn_descriptor_runtime backend io native_private stable_readonly discipline resources ipc)
    (passive:gateway_passive_resource_runtime backend resources).
Variables(readonly:block->Z->Prop)(selected:block->Prop)(reference:mem)(owner:World)(original:gateway_resource_state).

Definition gateway_exchange_context memory world:Prop:=
  discipline None memory world /\
  gateway_caller_resource_state resources original world /\
  gateway_caller_family native_private stable_readonly readonly selected reference owner memory world.

Lemma gateway_exchange_context_ambient:gateway_ambient_closed backend gateway_exchange_context.
Proof.
  intros before world after next[SIDE[RESOURCES FAMILY]]INTERFERENCE.
  destruct(gateway_thread_ambient _ _ _ _ _ _ thread None before world after next SIDE INTERFERENCE)
    as[NORMAL[ACCESS FRAME]].
  split;[exact NORMAL|]. split.
  - eapply gateway_caller_resource_ambient;[exact descriptors|exact SIDE|exact RESOURCES|exact INTERFERENCE].
  - intros target SELECTED;eapply gateway_caller_buffers_no_output;
      [exact(FAMILY target SELECTED)|exact ACCESS|exact FRAME].
Qed.

Theorem actual_exchange_clock_context before world events returned after next descriptor:
  (exists target,selected target)->gateway_exchange_context before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_now)[]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next)->
  gateway_exchange_context after next /\gateway_received_bytes io descriptor events=[].
Proof.
  intros NONEMPTY[SIDE[RESOURCES FAMILY]]RUN.
  destruct(gateway_actual_function_binding _clock_gettime gateway_clock_gettime_definition
    ltac:(vm_compute;reflexivity))as[symbol[SYMBOL FUNCTION]].
  destruct(actual_clock_array_resources backend io native_private stable_readonly discipline thread_errno
    resources ipc thread descriptors passive original(Clight.globalenv prog)readonly selected reference owner
    before world events returned after next symbol descriptor actual_clock_sample_size SYMBOL FUNCTION
    SIDE RESOURCES FAMILY NONEMPTY RUN)as[NORMAL[HISTORY[BUFFERS EMPTY]]].
  split;[split;[exact NORMAL|split;assumption]|exact EMPTY].
Qed.
End ExchangeContext.
