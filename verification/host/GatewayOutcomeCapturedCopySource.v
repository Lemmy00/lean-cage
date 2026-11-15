(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual owned copy is captured before its checked output lookup. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayOutcomeConstruction GatewaySourceCuts GatewaySourcePaths
  GatewaySourceBoundCalls GatewaySourceSegmentAutomation GatewayUnaryExpressions GatewayFailurePaths GatewayFramedRuntime GatewaySourceSegments GatewayOutcomeCopySource.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_outcome_captured_copy_output_source {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)environment parameters copy offset before function definition name:
  gateway_ambient_closed backend property->parameters!_copy=Some(Vptr copy offset)->
  (forall memory current,property memory current->Mem.weak_valid_pointer memory copy(Ptrofs.unsigned offset)=true)->
  environment!_PyDict_GetItemString=None->environment!___stringlit_40=None->
  Genv.find_symbol ge _PyDict_GetItemString=Some function->Genv.find_funct_ptr ge function=Some definition->
  Genv.find_symbol ge ___stringlit_40=Some name->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr);tptr tschar](tptr(Tstruct __object noattr))cc_default->
  exists selected,
    gateway_source_path backend ge definition[Vptr copy offset;Vptr name Ptrofs.zero]
      (gateway_outcome_output_lookup_cont environment selected)property
      (State f_host_outcome_from Sskip(Kseq gateway_outcome_after_copy Kstop)environment parameters before)property /\
    selected!_copy=Some(Vptr copy offset) /\selected!_data=parameters!_data.
Proof.
  intros CLOSED COPY POINTER LOCAL NAME_LOCAL SYMBOL FUNCTION NAME TYPE;eexists;split.
  - gateway_bound_source_call CLOSED
      ltac:(fun _=>eapply gateway_unary_expression_value with(value:=Vptr copy offset)(result:=Vint Int.zero);
        [gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|
         match goal with GOOD:property ?memory ?current|-_=>
           change(option_map(fun flag=>Val.of_bool(negb flag))
             (if Mem.weak_valid_pointer memory copy(Ptrofs.unsigned offset)then Some true else None)=Some(Vint Int.zero));
           rewrite(POINTER memory current GOOD);reflexivity end])ltac:(fun _=>reflexivity).
    eapply gateway_source_same with(target:=Callstate definition[Vptr copy offset;Vptr name Ptrofs.zero]
      (gateway_outcome_output_lookup_cont environment _)before).
    + exact CLOSED.
    + cbn;tauto.
    + intros;eapply certified_call_edge with(vf:=Vptr function Ptrofs.zero).
      * reflexivity.
      * apply old_expression_value;eapply value_function;[exact LOCAL|exact SYMBOL|reflexivity].
      * apply cons_argument_values with(v:=Vptr copy offset).
        -- gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
        -- reflexivity.
        -- apply cons_argument_values with(v:=Vptr name Ptrofs.zero).
           ++ apply old_expression_value;eapply value_function;[exact NAME_LOCAL|exact NAME|reflexivity].
           ++ reflexivity.
           ++ apply no_argument_values.
      * change(Genv.find_funct_ptr ge function=Some definition);exact FUNCTION.
      * exact TYPE.
    + apply gateway_source_reached;auto.
  - unfold set_opttemp;split;[repeat rewrite PTree.gso by discriminate;exact COPY|repeat rewrite PTree.gso by discriminate;reflexivity].
Qed.
