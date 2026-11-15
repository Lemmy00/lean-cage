(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Source-owned tuple and callback-result captures precede the
   next actual call. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPresentationSource GatewaySourcePaths
  GatewaySourceSegmentAutomation GatewayFramedRuntime GatewayObjectAddresses GatewayUnaryExpressions GatewayReferenceCapture
  GatewayReturns GatewayReturnIdentity GatewayContexts GatewaySourceSDKReceipt GatewayPresentationTrace GatewaySourceSegments.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_presentation_captured_incref_source {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)parameters array offset tuple tuple_offset child child_offset before symbol definition:
  gateway_ambient_closed backend property->parameters!_count=Some(Vint Int.one)->
  parameters!_values=Some(Vptr array offset)->parameters!_arguments=Some(Vptr tuple tuple_offset)->
  Ptrofs.unsigned offset+8<=Ptrofs.modulus->
  (forall memory current,property memory current->Mem.weak_valid_pointer memory tuple(Ptrofs.unsigned tuple_offset)=true)->
  (forall memory current,property memory current->Mem.load Mptr memory array(Ptrofs.unsigned offset)=Some(Vptr child child_offset))->
  Genv.find_symbol ge _Py_IncRef=Some symbol->Genv.find_funct_ptr ge symbol=Some definition->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr)]tvoid cc_default->
  exists selected,
    gateway_source_path backend ge definition[Vptr child child_offset](gateway_presentation_incref_cont selected)property
      (State f_host_call_objects Sskip(Kseq gateway_presentation_after_new Kstop)empty_env parameters before)property /\
    selected!_arguments=Some(Vptr tuple tuple_offset) /\selected!_values=parameters!_values /\
    selected!_count=parameters!_count /\selected!_index=Some(Vint Int.zero) /\selected!_callable=parameters!_callable.
Proof.
  intros CLOSED COUNT ARRAY TUPLE NOWRAP POINTER LOAD SYMBOL FUNCTION TYPE;eexists;split.
  - gateway_presentation_source_call CLOSED
      ltac:(fun _=>first[
        eapply gateway_unary_expression_value with(value:=Vptr tuple tuple_offset)(result:=Vint Int.zero);
          [gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|
           match goal with GOOD:property ?memory ?current|-_=>
             change(option_map(fun flag=>Val.of_bool(negb flag))
               (if Mem.weak_valid_pointer memory tuple(Ptrofs.unsigned tuple_offset)then Some true else None)=Some(Vint Int.zero));
             rewrite(POINTER memory current GOOD);reflexivity end]|
        eapply gateway_presentation_zero_element;
          [unfold set_opttemp;repeat rewrite PTree.gso by discriminate;exact ARRAY|
           unfold set_opttemp;repeat rewrite PTree.gso by discriminate;apply PTree.gss|exact NOWRAP|
           match goal with GOOD:property ?memory ?current|-_=>exact(LOAD memory current GOOD)end]])
      ltac:(fun _=>first[exact TUPLE|reflexivity]).
    eapply gateway_source_same with(target:=Callstate definition[Vptr child child_offset]
      (gateway_presentation_incref_cont _)before).
    + exact CLOSED.
    + cbn;tauto.
    + intros;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
      * reflexivity.
      * apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
      * apply cons_argument_values with(v:=Vptr child child_offset);
          [gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|reflexivity|apply no_argument_values].
      * change(Genv.find_funct_ptr ge symbol=Some definition);exact FUNCTION.
      * exact TYPE.
    + apply gateway_source_reached;auto.
  - unfold set_opttemp;repeat split;repeat rewrite PTree.gso by discriminate;first[apply PTree.gss|exact TUPLE|reflexivity].
Qed.

Theorem gateway_presentation_released_return_source {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)parameters ignored before:
  gateway_ambient_closed backend property ->
  gateway_source_segment backend ge property(Returnstate ignored(gateway_presentation_release_cont parameters)before)
    (State f_host_call_objects gateway_presentation_return Kstop empty_env parameters before)property.
Proof.
  intro CLOSED;gateway_segment_dynamic CLOSED ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
Qed.

Theorem gateway_presentation_captured_release_source {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)parameters tuple tuple_offset returned before symbol definition:
  gateway_ambient_closed backend property->parameters!_arguments=Some(Vptr tuple tuple_offset)->parameters!_result=Some returned->
  Genv.find_symbol ge _Py_DecRef=Some symbol->Genv.find_funct_ptr ge symbol=Some definition->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr)]tvoid cc_default->
  exists selected,
    gateway_source_path backend ge definition[Vptr tuple tuple_offset]
      (gateway_presentation_release_cont selected)property
      (State f_host_call_objects Sskip(Kseq gateway_presentation_after_call Kstop)empty_env parameters before)property /\
    selected!_arguments=parameters!_arguments /\selected!_result=Some returned /\selected!_callable=parameters!_callable.
Proof.
  intros CLOSED TUPLE RESULT SYMBOL FUNCTION TYPE;eexists;split.
  - gateway_presentation_source_call CLOSED ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
    eapply gateway_source_same with(target:=Callstate definition[Vptr tuple tuple_offset]
      (gateway_presentation_release_cont _)before).
    + exact CLOSED.
    + cbn;tauto.
    + intros;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
      * reflexivity.
      * apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
      * apply cons_argument_values with(v:=Vptr tuple tuple_offset);
          [gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|reflexivity|apply no_argument_values].
      * change(Genv.find_funct_ptr ge symbol=Some definition);exact FUNCTION.
      * exact TYPE.
    + apply gateway_source_reached;auto.
  - unfold set_opttemp;repeat split;repeat rewrite PTree.gso by discriminate;first[apply PTree.gss|exact RESULT|reflexivity].
Qed.

Theorem gateway_presentation_call_failed {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    parameters tuple tuple_offset before world events value after next symbol:
  parameters!_arguments=Some(Vptr tuple tuple_offset) ->
  Genv.find_symbol ge _Py_DecRef=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some gateway_presentation_release_definition ->
  gateway_steps backend ge(gateway_live(Returnstate Vnullptr(gateway_presentation_call_cont parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value=Vnullptr.
Proof.
  intros TUPLE SYMBOL FUNCTION RUN.
  assert(CLOSED:gateway_ambient_closed backend(fun _ _=>True))by(unfold gateway_ambient_closed;intros;exact I).
  destruct(gateway_presentation_release_source backend ge(fun _ _=>True)parameters tuple tuple_offset Vnullptr before
    symbol gateway_presentation_release_definition CLOSED TUPLE SYMBOL FUNCTION eq_refl)
    as(selected &PATH &ARGUMENTS &RESULT &CALLABLE).
  destruct(gateway_source_path_cut backend ge _ _ _ _ _ _ PATH before world events value after next I RUN)
    as(prefix &rest &memory &current &EVENTS &QUIET &PREFIX &READY &REST).
  destruct(gateway_return_cut backend ge gateway_presentation_release_definition[Vptr tuple tuple_offset]
    (gateway_presentation_release_cont selected)memory current rest(Returnstate value Kstop after)next I ltac:(cbn;lia)REST)
    as(reading &suffix &ignored &changed &following &TAIL &CALLEE &SUFFIX).
  eapply gateway_constant_path_actual;[|exact SUFFIX].
  eapply gateway_presentation_return_source;[exact RESULT|left;reflexivity].
Qed.
