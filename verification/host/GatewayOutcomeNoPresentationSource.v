(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: An actual None output skips presentation and reaches allocation
   on the same source run. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayOutcomeConstruction GatewayOutcomeOutputSource
  GatewayObjectAddresses GatewaySourceSegments GatewaySourceSegmentAutomation GatewayFramedRuntime GatewayUnaryExpressions.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_outcome_output_none_source {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)environment parameters slot none before:
  gateway_ambient_closed backend property ->environment!_output=Some(slot,tptr(Tstruct __object noattr)) ->
  environment!__Py_NoneStruct=None ->Genv.find_symbol ge __Py_NoneStruct=Some none ->
  (forall memory current,property memory current->Mem.loadv Mptr memory(Vptr slot Ptrofs.zero)=Some(Vptr none Ptrofs.zero)) ->
  (forall memory current,property memory current->Mem.weak_valid_pointer memory none 0=true) ->
  (forall memory current,property memory current->sem_binary_operation ge One(Vptr none Ptrofs.zero)
    (tptr(Tstruct __object noattr))(Vptr none Ptrofs.zero)(tptr(Tstruct __object noattr))memory=Some(Vint Int.zero)) ->
  exists selected,
    gateway_source_segment backend ge property
      (gateway_outcome_output_stored environment parameters(Vptr none Ptrofs.zero)before)
      (State f_host_outcome_from gateway_outcome_allocation_tail Kstop environment selected before)property /\
    selected!_copy=parameters!_copy /\selected!_data=parameters!_data.
Proof.
  intros CLOSED LOCAL NONE_LOCAL NONE_SYMBOL LOAD POINTER EQUAL;eexists;split.
  - unfold gateway_outcome_output_stored.
    gateway_segment_dynamic CLOSED
      ltac:(fun _=>first[
        eapply gateway_outcome_output_load;[exact LOCAL|eapply LOAD;eassumption]|
        eapply gateway_unary_expression_value with(value:=Vptr none Ptrofs.zero)(result:=Vint Int.zero);
          [gateway_segment_expression ltac:(fun _=>eapply gateway_outcome_output_load;[exact LOCAL|eapply LOAD;eassumption])ltac:(fun _=>reflexivity)|
           match goal with GOOD:property ?memory ?current|-_=>
             change(option_map(fun flag=>Val.of_bool(negb flag))
               (if Mem.weak_valid_pointer memory none 0 then Some true else None)=Some(Vint Int.zero));
             rewrite(POINTER memory current GOOD);reflexivity end]|
        apply gateway_global_address_expression;[exact NONE_LOCAL|exact NONE_SYMBOL]])
      ltac:(fun _=>first[eapply EQUAL;eassumption|reflexivity]).
  - unfold gateway_outcome_output_parameters,set_opttemp;split;repeat rewrite PTree.gso by discriminate;reflexivity.
Qed.

Lemma gateway_outcome_none_compare(ge:Clight.genv)memory object:
  Mem.weak_valid_pointer memory object 0=true ->
  sem_binary_operation ge One(Vptr object Ptrofs.zero)(tptr(Tstruct __object noattr))
    (Vptr object Ptrofs.zero)(tptr(Tstruct __object noattr))memory=Some(Vint Int.zero).
Proof.
  intro WEAK;unfold sem_binary_operation,sem_cmp,cmp_ptr.
  cbn[classify_cmp typeconv Val.cmplu_bool].
  rewrite peq_true.
  change(option_map Val.of_bool
    (if Mem.weak_valid_pointer memory object 0&&Mem.weak_valid_pointer memory object 0
     then Some false else None)=Some(Vint Int.zero)).
  rewrite WEAK;reflexivity.
Qed.
