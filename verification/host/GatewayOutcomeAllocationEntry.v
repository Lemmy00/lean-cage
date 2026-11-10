(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Allocation uses the class loaded by this actual constructor source. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayOutcomeConstruction GatewayOutcomeOutputSource
  GatewaySourcePaths GatewaySourceBoundCalls GatewaySourceSegmentAutomation GatewayFramedRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_outcome_allocator_definition:Ctypes.fundef Clight.function:=External
  (EF_external "PyType_GenericAlloc"(mksignature[Xptr;Xlong]Xptr cc_default))
  [tptr(Tstruct __typeobject noattr);tlong](tptr(Tstruct __object noattr))cc_default.

Theorem gateway_outcome_allocation_source {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)environment parameters class class_offset before global function:
  gateway_ambient_closed backend property->environment!_host_outcome_class=None->environment!_PyType_GenericAlloc=None->
  Genv.find_symbol ge _host_outcome_class=Some global->Genv.find_symbol ge _PyType_GenericAlloc=Some function->
  Genv.find_funct_ptr ge function=Some gateway_outcome_allocator_definition->
  (forall memory current,property memory current->Mem.loadv Mptr memory(Vptr global Ptrofs.zero)=Some(Vptr class class_offset))->
  exists selected,
    gateway_source_path backend ge gateway_outcome_allocator_definition[Vptr class class_offset;Vlong Int64.zero]
      (gateway_outcome_allocation_cont environment selected)property
      (State f_host_outcome_from gateway_outcome_allocation_tail Kstop environment parameters before)property /\
    selected!_copy=parameters!_copy /\selected!_data=parameters!_data /\selected!_t'25=Some(Vptr class class_offset).
Proof.
  intros CLOSED CLASS_LOCAL ALLOCATOR_LOCAL CLASS_SYMBOL ALLOCATOR_SYMBOL ALLOCATOR_FUNCTION CLASS_LOAD;eexists;split.
  - gateway_bound_source_call CLOSED
      ltac:(fun _=>eapply location_read_value;
        [apply global_location_value;[exact CLASS_LOCAL|exact CLASS_SYMBOL]|
         eapply deref_loc_value;[reflexivity|eapply CLASS_LOAD;eassumption]])
      ltac:(fun _=>reflexivity).
    eapply gateway_source_same with(target:=Callstate gateway_outcome_allocator_definition
      [Vptr class class_offset;Vlong Int64.zero](gateway_outcome_allocation_cont environment _)before).
    + exact CLOSED.
    + cbn;tauto.
    + intros;eapply certified_call_edge with(vf:=Vptr function Ptrofs.zero).
      * reflexivity.
      * apply old_expression_value;eapply value_function;[exact ALLOCATOR_LOCAL|exact ALLOCATOR_SYMBOL|reflexivity].
      * apply cons_argument_values with(v:=Vptr class class_offset).
        -- gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
        -- reflexivity.
        -- apply cons_argument_values with(v:=Vint Int.zero);
             [apply old_expression_value;constructor|reflexivity|apply no_argument_values].
      * change(Genv.find_funct_ptr ge function=Some gateway_outcome_allocator_definition);exact ALLOCATOR_FUNCTION.
      * reflexivity.
    + apply gateway_source_reached;auto.
  - unfold set_opttemp;repeat split;repeat rewrite PTree.gso by discriminate;
      first[reflexivity|apply PTree.gss].
Qed.
