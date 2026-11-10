(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A retained source-created class supplies the allocator's current metadata. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayObjectDiscipline
  GatewayRootLeases GatewayObjectThreads GatewayTypeRuntime GatewayTypeDescriptors GatewayGetsets GatewayOutcomeType
  GatewayOutcomeDispatch GatewayOutcomeAllocation GatewayOutcomeConstruction GatewayOutcomeReturn GatewayOutcomeFactory
  GatewayLocalRuntime GatewayObjectEvents GatewayThreadRuntime GatewayStreamInterface.
Import ListNotations.

Theorem gateway_actual_source_class_outcome {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects types allocator instances leases owned decimal_float detached io stable thread_errno heap_allocation
    immutable_binding attribute_target
    (runtime:gateway_thread_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (allocations:gateway_outcome_allocation_runtime backend python objects types allocator instances leases owned io
      (fun current candidate=>gateway_native_private(python current)candidate)stable)
    (roots:gateway_root_lease_runtime backend python objects decimal_float leases)
    (object_threads:gateway_object_thread_contract backend(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects leases)
    (descriptors:gateway_descriptor_runtime backend python objects types allocator instances immutable_binding attribute_target)
    environment parameters class class_ticket held data_block data_offset new initialize destroy traverse clear methods properties entries
    before world events value after next descriptor:
  gateway_direct_io_projection backend io ->GatewayOutcome.gateway_outcome_member_layout ge ->
  parameters!_copy=Some(Vptr data_block data_offset) ->gateway_objects_ready(python world)(objects world)before ->
  leases world class_ticket class ->gateway_held_values python objects decimal_float leases held world ->
  gateway_native_environment(fun current candidate=>gateway_native_private(python current)candidate)world before environment ->
  immutable_binding class(gateway_outcome_description new initialize destroy traverse clear methods properties)entries ->
  gateway_steps backend ge
    (gateway_live(Callstate(External(EF_external "PyType_GenericAlloc"(mksignature[Xptr;Xlong]Xptr cc_default))
      [tptr(Tstruct __typeobject noattr);tlong](tptr(Tstruct __object noattr))cc_default)
      [class;Vlong Int64.zero](gateway_outcome_allocation_cont environment parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value<>Vnullptr ->
  exists object ticket,value=Vptr object Ptrofs.zero /\
    gateway_outcome_return_context python objects instances leases owned decimal_float
      object(Vptr data_block data_offset)class ticket held after next /\gateway_received_bytes io descriptor events=[].
Proof.
  intros PROJECTION LAYOUT COPY READY CLASS_LEASE HELD ENVIRONMENT BINDING RUN NONNULL.
  pose proof(gateway_lease_rooted backend python objects decimal_float leases roots world class_ticket class CLASS_LEASE)as ROOT.
  destruct(gateway_current_outcome_class backend python objects types allocator instances immutable_binding attribute_target descriptors
    before world class new initialize destroy traverse clear methods properties entries READY ROOT BINDING)as[TYPE ALLOCATOR].
  eapply(gateway_actual_outcome_allocation backend ge python objects types allocator instances leases owned decimal_float detached io stable
    thread_errno heap_allocation runtime allocations roots object_threads environment parameters class
    (gateway_outcome_description new initialize destroy traverse clear methods properties)class_ticket held data_block data_offset before world
    events value after next descriptor);[exact PROJECTION|exact LAYOUT|exact COPY|reflexivity|reflexivity|reflexivity| |exact RUN|exact NONNULL].
  exact(conj READY(conj TYPE(conj ALLOCATOR(conj CLASS_LEASE(conj HELD ENVIRONMENT))))).
Qed.
