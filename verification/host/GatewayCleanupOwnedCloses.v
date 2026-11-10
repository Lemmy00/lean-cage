(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: Actual cleanup closes consume the two selected invocation
   leases and retain the already received graph and caller storage. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayRuntime GatewayThreadRuntime GatewayStreamInterface
  GatewayPython GatewayObjects GatewayObjectThreads
  GatewayStreamMemory GatewaySpawnABI GatewaySpawnResources GatewaySpawnRuntime GatewayCallerBuffers GatewayCallerFamily
  GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceHeld GatewayReferenceThreads GatewayCleanupReferences
  GatewayExchangeTransport GatewayCleanupSource GatewayCleanupClose GatewayReadonly GatewayFramedRuntime GatewayErrnoFragment GatewayTransferMath.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Section OwnedCloses.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
  (native:World->block->Prop)(stable:World->block->Z->Prop)(base:option val->mem->World->Prop)(thread_errno:World->int)
  (resources:World->gateway_resource_state)(ipc:nat->Prop)(heap_allocation:block->Z->Prop)
  (python:World->python_world)(objects:World->gateway_object_heap)(decimal_float:list Z->Floats.float->Prop).
Context(thread:gateway_thread_runtime backend io native stable base thread_errno)
  (descriptors:gateway_spawn_descriptor_runtime backend io native stable base resources ipc)
  (references:gateway_reference_thread_contract backend native stable base heap_allocation python objects)
  (cleanup:gateway_cleanup_reference_runtime backend native base python objects).
Variables(ledger:gateway_reference_ledger)(held:list gateway_held_value)
  (readonly:block->Z->Prop)(selected:block->Prop)(reference:mem)(owner:World).

Definition gateway_cleanup_close_context(remaining:list(Z*gateway_resource_descriptor))memory world:Prop:=
  base None memory world /\gateway_reference_scope python objects decimal_float ledger held world /\
  gateway_caller_family native stable readonly selected reference owner memory world /\
  gateway_resource_valid(resources world) /\
  Forall(fun entry=>gateway_owned_descriptor(resources world)(fst entry)(snd entry))remaining.

Lemma gateway_cleanup_close_context_ambient remaining:
  gateway_ambient_closed backend(gateway_cleanup_close_context remaining).
Proof.
  intros before world after next[SIDE[SCOPE[FAMILY[VALID OWNED]]]]AMBIENT.
  destruct(gateway_thread_ambient _ _ _ _ _ _ thread None before world after next SIDE AMBIENT)as[AFTER[ACCESS FRAME]].
  destruct(gateway_spawn_ambient _ _ _ _ _ _ _ descriptors before world after next SIDE VALID AMBIENT)
    as[CURRENT[RESOURCES REST]].
  split;[exact AFTER|]. split.
  - eapply gateway_reference_scope_thread_effect;[exact SCOPE|].
    eapply gateway_reference_thread_ambient;[exact references|exact SIDE|exact AMBIENT].
  - split.
    + intros target HERE;eapply gateway_caller_buffers_no_output;[exact(FAMILY target HERE)|exact ACCESS|exact FRAME].
    + split;[exact CURRENT|]. eapply Forall_impl;[|exact OWNED].
      intros[fd entry]ENTRY;cbn in *;eapply(proj1 RESOURCES);[exact ENTRY|tauto].
Qed.

Lemma gateway_cleanup_close_context_step descriptor entry remaining before world result after next observed:
  gateway_cleanup_close_context((Int.signed descriptor,entry)::remaining)before world->
  (forall fd value,In(fd,value)remaining->fd<>Int.signed descriptor)->
  gateway_runtime_operation backend(gateway_spawn_signature gateway_close_api)[Vint descriptor]
    before world result after next observed->
  gateway_cleanup_close_context remaining after next /\io observed=None.
Proof.
  intros[SIDE[SCOPE[FAMILY[VALID OWNED]]]]DISTINCT API.
  inversion OWNED as[|? ? ENTRY REMAINING];subst.
  assert(OPERATION:gateway_spawn_operation backend gateway_close_api[Vint(Int.repr(Int.signed descriptor))]
    before world result after next observed).
  { exists(gateway_spawn_signature gateway_close_api);split;[reflexivity|]. rewrite Int.repr_signed;exact API. }
  destruct(gateway_close_operation _ _ _ _ _ _ _ descriptors before world(Int.signed descriptor)entry result after next observed
    SIDE VALID ENTRY OPERATION)as[RESULT[AFTER[CURRENT[ACCESS[FRAME[RELEASED[RESOURCES[STATUS[EXCLUSIVE IO]]]]]]]]].
  split;[|exact IO]. split;[exact AFTER|]. split.
  - eapply gateway_reference_scope_thread_effect;[exact SCOPE|].
    eapply gateway_cleanup_reference_effect;[exact cleanup|]. eapply gateway_cleanup_graph_close;
      [exact SIDE|exact AFTER|rewrite Int.repr_signed in OPERATION;exact OPERATION].
  - split.
    + intros target HERE;eapply gateway_caller_buffers_no_output;[exact(FAMILY target HERE)|exact ACCESS|exact FRAME].
    + split;[exact CURRENT|]. apply Forall_forall;intros[fd value]MEMBER;cbn.
      eapply(proj1 RESOURCES).
      * exact(proj1(Forall_forall _ _)REMAINING(fd,value)MEMBER).
      * cbn;apply DISTINCT with(value:=value);exact MEMBER.
Qed.

Theorem actual_exchange_closes_owned_endpoints allocation_before allocated environment temporaries stream initial
    data control before world events value after next:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  environment!_stream=Some(stream,Tstruct _host_stream noattr)->selected stream->
  (forall position,0<=position<48->readonly stream position)->
  gateway_stream_memory reference stream Ptrofs.zero initial->stream_descriptor initial<>stream_control initial->
  gateway_cleanup_close_context[(Int.signed(stream_descriptor initial),data);(Int.signed(stream_control initial),control)]before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_exchange exchange_cleanup_phase Kstop environment temporaries before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists prefix suffix memory current final_temps,
    events=prefix++suffix /\gateway_received_bytes io(stream_descriptor initial)prefix=[] /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange exchange_cleanup_phase Kstop environment temporaries before)world)prefix
      (gateway_live(State f_host_exchange(exchange_cleanup_after 2)Kstop environment final_temps memory)current) /\
    final_temps=cleanup_close_temps gateway_cleanup_control(stream_control initial)
      (cleanup_close_temps gateway_cleanup_data(stream_descriptor initial)temporaries) /\
    gateway_cleanup_close_context[]memory current /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange(exchange_cleanup_after 2)Kstop environment final_temps memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros ALLOC STREAM SELECTED READONLY CELLS DISTINCT READY RUN.
  assert(CURRENT_CELLS:forall remaining memory current,gateway_cleanup_close_context remaining memory current->
    gateway_stream_memory memory stream Ptrofs.zero initial).
  { intros remaining memory current[SIDE[SCOPE[FAMILY REST]]].
    pose proof(FAMILY stream SELECTED)as[LIVE[NATIVE[READABLE[[FRAME PERMISSIONS]HISTORY]]]].
    eapply gateway_stream_memory_closed;[change(0+48<=18446744073709551616);lia|exact CELLS|].
    eapply Mem.unchanged_on_implies;[exact FRAME|intros object position[SAME RANGE]VALID;subst object;apply READONLY;exact RANGE]. }
  destruct(actual_exchange_cleanup_close backend io _ _
    (gateway_cleanup_close_context_ambient[(Int.signed(stream_descriptor initial),data);(Int.signed(stream_control initial),control)])
    (gateway_cleanup_close_context_ambient[(Int.signed(stream_control initial),control)])gateway_cleanup_data stream initial
    allocation_before allocated environment temporaries before world events value after next ALLOC STREAM
    (CURRENT_CELLS _)
    ltac:(intros;eapply gateway_cleanup_close_context_step;[eassumption| |eassumption];
      intros fd entry[PAIR|MEMBER];[inversion PAIR;subst;intro SAME;apply DISTINCT;
        apply(f_equal Int.repr)in SAME;repeat rewrite Int.repr_signed in SAME;congruence|contradiction])READY RUN)
    as(p1&r1&m1&w1&E1&EMPTY1&P1&C1&S1).
  destruct(actual_exchange_cleanup_close backend io _ _
    (gateway_cleanup_close_context_ambient[(Int.signed(stream_control initial),control)])(gateway_cleanup_close_context_ambient[])
    gateway_cleanup_control stream initial allocation_before allocated environment
    (cleanup_close_temps gateway_cleanup_data(stream_descriptor initial)temporaries)m1 w1 r1 value after next ALLOC STREAM
    (CURRENT_CELLS _)
    ltac:(intros;eapply gateway_cleanup_close_context_step;[eassumption|intros;contradiction|eassumption])C1 S1)
    as(p2&suffix&memory&current&E2&EMPTY2&P2&FINAL&SUFFIX).
  exists(p1++p2),suffix,memory,current,
    (cleanup_close_temps gateway_cleanup_control(stream_control initial)
      (cleanup_close_temps gateway_cleanup_data(stream_descriptor initial)temporaries)).
  split;[rewrite E1,E2,app_assoc;reflexivity|]. split.
  - rewrite gateway_received_bytes_append,(proj1(EMPTY1(stream_descriptor initial))),(proj1(EMPTY2(stream_descriptor initial)));reflexivity.
  - split;[eapply gateway_steps_append;[exact P1|exact P2]|]. split;[reflexivity|]. split;assumption.
Qed.
End OwnedCloses.
