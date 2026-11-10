(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: Clock setup retains earlier physical IPC owners and caller arrays. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayClock GatewayThreadRuntime GatewayCallerBuffers
  GatewayCallerFamily GatewayClockWorld GatewaySpawnResources GatewaySpawnRuntime GatewayPairHistory
  GatewayPassiveResources GatewayStreamInterface.
Import ListNotations.

Section ClockResources.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
    (native_private:World->block->Prop)(stable_readonly:World->block->Z->Prop)
    (discipline:option val->mem->World->Prop)(thread_errno:World->int)
    (resources:World->gateway_resource_state)(ipc:nat->Prop).
Context(thread:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno)
    (descriptors:gateway_spawn_descriptor_runtime backend io native_private stable_readonly discipline resources ipc)
    (passive:gateway_passive_resource_runtime backend resources).
Variable original:gateway_resource_state.

Definition gateway_caller_resource_state world:Prop:=
  gateway_resource_valid(resources world) /\gateway_resource_reference original(resources world).

Lemma gateway_caller_resource_ambient before world after next:
  discipline None before world->gateway_caller_resource_state world->
  gateway_interference backend before world after next->gateway_caller_resource_state next.
Proof.
  intros SIDE[VALID HISTORY]INTERFERENCE.
  destruct(gateway_spawn_ambient _ _ _ _ _ _ _ descriptors before world after next SIDE VALID INTERFERENCE)
    as[AFTER[FRAME[STATUS EXCLUSIVE]]]. split;[exact AFTER|].
  eapply gateway_resource_reference_step;
    [exact HISTORY|exact FRAME|intros;tauto|exact STATUS|exact EXCLUSIVE].
Qed.

Theorem actual_clock_resources_complete(ge:Clight.genv)before world events returned after next symbol:
  sizeof(genv_cenv ge)clock_sample_type=16%Z->
  Genv.find_symbol ge _clock_gettime=Some symbol->
  Genv.find_funct_ptr ge symbol=Some clock_gettime_definition->
  discipline None before world->gateway_caller_resource_state world->
  gateway_steps backend ge(gateway_live(Callstate(Internal f_host_now)[]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next)->
  discipline None after next /\gateway_caller_resource_state next.
Proof.
  intros SIZE SYMBOL FUNCTION SIDE STATE RUN.
  eapply actual_clock_world_complete;
    [exact thread|exact gateway_caller_resource_ambient| |exact SIZE|exact SYMBOL|exact FUNCTION|
     exact SIDE|exact STATE|exact RUN].
  intros memory current sample value changed later observed[VALID HISTORY]OPERATION.
  destruct(gateway_clock_resources backend resources passive[Vint Int.one;Vptr sample Ptrofs.zero]
    memory current value changed later observed VALID OPERATION)as[AFTER STEP].
  split;[exact AFTER|]. eapply gateway_resource_reference_transitive;[exact HISTORY|exact STEP].
Qed.

Theorem actual_clock_array_resources(ge:Clight.genv)readonly selected reference owner
    before world events returned after next symbol descriptor:
  sizeof(genv_cenv ge)clock_sample_type=16%Z->
  Genv.find_symbol ge _clock_gettime=Some symbol->
  Genv.find_funct_ptr ge symbol=Some clock_gettime_definition->
  discipline None before world->gateway_caller_resource_state world->
  gateway_caller_family native_private stable_readonly readonly selected reference owner before world->
  (exists target,selected target)->
  gateway_steps backend ge(gateway_live(Callstate(Internal f_host_now)[]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next)->
  discipline None after next /\gateway_caller_resource_state next /\
  gateway_caller_family native_private stable_readonly readonly selected reference owner after next /\
  gateway_received_bytes io descriptor events=[].
Proof.
  intros SIZE SYMBOL FUNCTION SIDE STATE HISTORY NONEMPTY RUN.
  destruct(actual_clock_resources_complete ge before world events returned after next symbol
    SIZE SYMBOL FUNCTION SIDE STATE RUN)as[AFTER RESOURCES].
  destruct(actual_caller_clock_family backend ge io native_private stable_readonly discipline thread_errno thread
    readonly selected reference owner before world events returned after next symbol descriptor
    SIZE SYMBOL FUNCTION SIDE HISTORY NONEMPTY RUN)as[SAME[BUFFERS EMPTY]].
  split;[exact AFTER|]. split;[exact RESOURCES|]. split;assumption.
Qed.
End ClockResources.
