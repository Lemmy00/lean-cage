(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Presentation receives the original checked output slot and the actual captured callable. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayOutcomeConstruction GatewayOutcomeCopySource GatewayObjectAddresses
  GatewaySourceSegments GatewaySourcePaths GatewaySourceBoundCalls GatewaySourceSegmentAutomation GatewayFramedRuntime GatewayUnaryExpressions GatewayValueReturns.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_outcome_output_parameters parameters output:=set_opttemp(Some _t'21)output parameters.
Definition gateway_outcome_output_stored environment parameters output memory:=
  State f_host_outcome_from Sskip(Kseq gateway_outcome_after_output_lookup Kstop)environment
    (gateway_outcome_output_parameters parameters output)memory.
Definition gateway_outcome_presentation_tail:=gateway_outcome_right_suffix 12(fn_body f_host_outcome_from).
Definition gateway_outcome_path_body:=match gateway_outcome_presentation_tail with
  Ssequence(Ssequence _ (Sifthenelse _ body _))_=>body|_=>Sskip end.
Definition gateway_outcome_path_after_call:=match gateway_outcome_path_body with Ssequence _ rest=>rest|_=>Sskip end.
Definition gateway_outcome_path_cont environment parameters:=Kcall(Some _t'22)f_host_outcome_from environment parameters
  (Kseq(Sset _path(Etempvar _t'22(tptr(Tstruct __object noattr))))
    (Kseq gateway_outcome_path_after_call(Kseq gateway_outcome_allocation_tail Kstop))).

Lemma gateway_outcome_output_load(ge:Clight.genv) environment parameters memory slot value:
  environment!_output=Some(slot,tptr(Tstruct __object noattr))->Mem.loadv Mptr memory(Vptr slot Ptrofs.zero)=Some value->
  expression_value ge environment parameters memory(Evar _output(tptr(Tstruct __object noattr)))value.
Proof.
  intros LOCAL LOAD;eapply location_read_value;
    [apply local_location_value;exact LOCAL|eapply deref_loc_value;[reflexivity|exact LOAD]].
Qed.

Lemma gateway_outcome_class_load(ge:Clight.genv) environment parameters memory global value:
  environment!_host_path_class=None->Genv.find_symbol ge _host_path_class=Some global->
  Mem.loadv Mptr memory(Vptr global Ptrofs.zero)=Some value->
  expression_value ge environment parameters memory(Evar _host_path_class(tptr(Tstruct __object noattr)))value.
Proof.
  intros LOCAL SYMBOL LOAD;eapply location_read_value;
    [apply global_location_value;[exact LOCAL|exact SYMBOL]|eapply deref_loc_value;[reflexivity|exact LOAD]].
Qed.

Theorem gateway_outcome_output_store_segment {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property result:mem->World->Prop)environment parameters slot output before:
  gateway_ambient_closed backend property->environment!_output=Some(slot,tptr(Tstruct __object noattr))->
  gateway_object_pointer_value output->
  (forall memory current,property memory current->exists changed,
    Mem.storev Mptr memory(Vptr slot Ptrofs.zero)output=Some changed /\result changed current)->
  gateway_source_segment backend ge property
    (Returnstate output(gateway_outcome_output_lookup_cont environment parameters)before)
    (gateway_outcome_output_stored environment parameters output before)result.
Proof.
  intros CLOSED LOCAL POINTER STORE.
  eapply gateway_segment_same with(next:=State f_host_outcome_from Sskip
    (Kseq gateway_outcome_output_assignment(Kseq gateway_outcome_after_output_lookup Kstop))environment
    (gateway_outcome_output_parameters parameters output)before).
  - exact CLOSED.
  - cbn;tauto.
  - intros;apply unchanged_store_edge,edge_returnstate.
  - eapply gateway_segment_same with(next:=State f_host_outcome_from gateway_outcome_output_assignment
      (Kseq gateway_outcome_after_output_lookup Kstop)environment(gateway_outcome_output_parameters parameters output)before).
    + exact CLOSED.
    + cbn;tauto.
    + intros;apply unchanged_store_edge,edge_skip_seq.
    + eapply gateway_segment_next with(next:=gateway_outcome_output_stored environment parameters output before)(middle:=result).
      * exact CLOSED.
      * cbn;tauto.
      * intros memory current GOOD;destruct(STORE memory current GOOD)as[changed[WRITE POST]];exists changed;split;[|exact POST].
        eapply assignment_source_edge with(b:=slot)(ofs:=Ptrofs.zero)(v:=output)(w:=output).
        -- apply local_location_value;exact LOCAL.
        -- apply old_expression_value,value_temp;apply PTree.gss.
        -- destruct POINTER as[NULL|[object[offset SAME]]];subst output;reflexivity.
        -- eapply assign_loc_value;[reflexivity|exact WRITE].
      * apply gateway_segment_here.
Qed.

Theorem gateway_outcome_output_path_source {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)environment parameters slot output_block output_offset callable callable_offset
    none_symbol class_symbol helper_symbol before:
  gateway_ambient_closed backend property->environment!_output=Some(slot,tptr(Tstruct __object noattr))->
  environment!_host_path_class=None->environment!__Py_NoneStruct=None->environment!_host_call_objects=None->
  Genv.find_symbol ge __Py_NoneStruct=Some none_symbol->Genv.find_symbol ge _host_path_class=Some class_symbol->
  Genv.find_symbol ge _host_call_objects=Some helper_symbol->Genv.find_funct_ptr ge helper_symbol=Some(Internal f_host_call_objects)->
  (forall memory current,property memory current->Mem.loadv Mptr memory(Vptr slot Ptrofs.zero)=Some(Vptr output_block output_offset))->
  (forall memory current,property memory current->Mem.weak_valid_pointer memory output_block(Ptrofs.unsigned output_offset)=true)->
  (forall memory current,property memory current->Mem.loadv Mptr memory(Vptr class_symbol Ptrofs.zero)=Some(Vptr callable callable_offset))->
  (forall memory current,property memory current->sem_binary_operation ge One(Vptr output_block output_offset)
    (tptr(Tstruct __object noattr))(Vptr none_symbol Ptrofs.zero)(tptr(Tstruct __object noattr))memory=Some(Vint Int.one))->
  exists selected,
    gateway_source_path backend ge(Internal f_host_call_objects)[Vptr callable callable_offset;Vptr slot Ptrofs.zero;Vint Int.one]
      (gateway_outcome_path_cont environment selected)property
      (gateway_outcome_output_stored environment parameters(Vptr output_block output_offset)before)property /\
    selected!_copy=parameters!_copy /\selected!_data=parameters!_data /\selected!_t'27=Some(Vptr callable callable_offset).
Proof.
  intros CLOSED OUTPUT_LOCAL CLASS_LOCAL NONE_LOCAL HELPER_LOCAL NONE_SYMBOL CLASS_SYMBOL HELPER_SYMBOL HELPER_FUNCTION
    OUTPUT_LOAD OUTPUT_POINTER CLASS_LOAD DIFFERENT;eexists;split.
  - unfold gateway_outcome_output_stored.
    gateway_bound_source_call CLOSED
      ltac:(fun _=>first[
        eapply gateway_outcome_output_load;[exact OUTPUT_LOCAL|eapply OUTPUT_LOAD;eassumption]|
        eapply gateway_outcome_class_load;[exact CLASS_LOCAL|exact CLASS_SYMBOL|eapply CLASS_LOAD;eassumption]|
        eapply gateway_unary_expression_value with(value:=Vptr output_block output_offset)(result:=Vint Int.zero);
          [gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|
           match goal with GOOD:property ?memory ?current|-_=>
             change(option_map(fun flag=>Val.of_bool(negb flag))
               (if Mem.weak_valid_pointer memory output_block(Ptrofs.unsigned output_offset)then Some true else None)=Some(Vint Int.zero));
             rewrite(OUTPUT_POINTER memory current GOOD);reflexivity end]|
        apply gateway_global_address_expression;[exact NONE_LOCAL|exact NONE_SYMBOL]])
      ltac:(fun _=>first[eapply DIFFERENT;eassumption|reflexivity]).
    eapply gateway_source_same with(target:=Callstate(Internal f_host_call_objects)
      [Vptr callable callable_offset;Vptr slot Ptrofs.zero;Vint Int.one](gateway_outcome_path_cont environment _)before).
    + exact CLOSED.
    + cbn;tauto.
    + intros;eapply certified_call_edge with(vf:=Vptr helper_symbol Ptrofs.zero).
      * reflexivity.
      * apply old_expression_value;eapply value_function;[exact HELPER_LOCAL|exact HELPER_SYMBOL|reflexivity].
      * apply cons_argument_values with(v:=Vptr callable callable_offset).
        -- gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
        -- reflexivity.
        -- apply cons_argument_values with(v:=Vptr slot Ptrofs.zero).
           ++ match goal with |-expression_value _ _ ?current_parameters ?current_memory _ _=>
                destruct(local_location_value ge environment current_parameters current_memory _output(tptr(Tstruct __object noattr))slot OUTPUT_LOCAL)as[LOCATION UNIQUE]end.
              split;[econstructor;exact LOCATION|]. intros other EVALUATION;inversion EVALUATION;subst.
              ** match goal with LOCATION_OTHER:eval_lvalue _ _ _ _ _ _ _ _|-_=>
                   destruct(UNIQUE _ _ _ LOCATION_OTHER)as[BLOCK[OFFSET FIELD]];subst;reflexivity end.
              ** match goal with BAD:eval_lvalue _ _ _ _ (Eaddrof _ _)_ _ _|-_=>inversion BAD end.
           ++ reflexivity.
           ++ apply cons_argument_values with(v:=Vint Int.one);
                [apply old_expression_value;constructor|reflexivity|apply no_argument_values].
      * cbn;exact HELPER_FUNCTION.
      * reflexivity.
    + apply gateway_source_reached;auto.
  - unfold gateway_outcome_output_parameters,set_opttemp;repeat split;repeat rewrite PTree.gso by discriminate;
      first[reflexivity|apply PTree.gss].
Qed.
