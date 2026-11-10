(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Each arithmetic operation follows the real source guard and
   uses the retained operand temporaries from that same integer-helper iteration. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayNumberIntegerStructure GatewayNumberConstruction
  GatewaySourcePaths GatewaySourceBoundCalls GatewaySourceSegmentAutomation GatewayUnaryExpressions GatewayValueReturns GatewayFramedRuntime.
Import ListNotations.

Ltac number_sdk_reached closed symbol function_name symbol_fact function_fact type_fact arguments :=
  lazymatch goal with
  | |-gateway_source_path _ _ ?definition ?values ?continuation _
      (State ?function ?body ?saved ?environment ?parameters ?memory) _=>
    eapply gateway_source_same with(target:=Callstate definition values continuation memory);
    [exact closed|cbn;tauto|intros;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero);
      [reflexivity|apply old_expression_value;eapply value_function;[reflexivity|exact symbol_fact|reflexivity]|
       arguments ()|exact function_fact|exact type_fact]|apply gateway_source_reached;auto]
  end.

Ltac number_nonnull_expression property pointer offset valid :=
  eapply gateway_unary_expression_value with(value:=Vptr pointer offset)(result:=Vint Int.zero);
  [gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|
   match goal with GOOD:property ?current ?world|-_=>
     change(option_map(fun flag=>Val.of_bool(negb flag))
       (if Mem.weak_valid_pointer current pointer(Ptrofs.unsigned offset)then Some true else None)=Some(Vint Int.zero));
     rewrite(valid current world GOOD);reflexivity end].

Theorem gateway_number_multiply_source_path {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)parameters part part_offset current base memory symbol definition:
  gateway_ambient_closed backend property->
  (forall memory world,property memory world->Mem.weak_valid_pointer memory part(Ptrofs.unsigned part_offset)=true)->
  parameters!_value__1=Some current->parameters!_base=Some base->
  gateway_object_pointer_value current->gateway_object_pointer_value base->
  Genv.find_symbol ge _PyNumber_Multiply=Some symbol->Genv.find_funct_ptr ge symbol=Some definition->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr);tptr(Tstruct __object noattr)](tptr(Tstruct __object noattr))cc_default->
  exists called_parameters,
    gateway_source_path backend ge definition[current;base](number_integer_multiply_cont called_parameters)property
      (Returnstate(Vptr part part_offset)(number_integer_part_cont parameters)memory)property /\
    called_parameters!_part=Some(Vptr part part_offset) /\
    (forall identifier,identifier<>_part->identifier<>_t'18->called_parameters!identifier=parameters!identifier).
Proof.
  intros CLOSED VALID CURRENT BASE CURRENT_POINTER BASE_POINTER SYMBOL FUNCTION TYPE;eexists;split.
  - gateway_bound_source_call CLOSED ltac:(fun _=>number_nonnull_expression property part part_offset VALID)ltac:(fun _=>reflexivity).
    number_sdk_reached CLOSED symbol _PyNumber_Multiply SYMBOL FUNCTION TYPE
      ltac:(fun _=>apply cons_argument_values with(v:=current);
        [gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|
         destruct CURRENT_POINTER as[NULL|[object[offset SAME]]];subst current;reflexivity|
         apply cons_argument_values with(v:=base);
         [gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|
          destruct BASE_POINTER as[NULL|[object[offset SAME]]];subst base;reflexivity|apply no_argument_values]]).
  - split;[apply PTree.gss|]. intros identifier A B;unfold set_opttemp;repeat rewrite PTree.gso by congruence;reflexivity.
Qed.

Theorem gateway_number_old_value_release_path {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)parameters current returned memory symbol definition:
  gateway_ambient_closed backend property->parameters!_value__1=Some current->gateway_object_pointer_value current->
  Genv.find_symbol ge _Py_DecRef=Some symbol->Genv.find_funct_ptr ge symbol=Some definition->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr)]tvoid cc_default->
  exists called_parameters,
    gateway_source_path backend ge definition[current](number_integer_release_value_cont called_parameters)property
      (Returnstate returned(number_integer_multiply_cont parameters)memory)property /\
    called_parameters!_scaled=Some returned /\
    (forall identifier,identifier<>_scaled->identifier<>_t'19->called_parameters!identifier=parameters!identifier).
Proof.
  intros CLOSED CURRENT POINTER SYMBOL FUNCTION TYPE;eexists;split.
  - gateway_bound_source_call CLOSED ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
    number_sdk_reached CLOSED symbol _Py_DecRef SYMBOL FUNCTION TYPE
      ltac:(fun _=>apply cons_argument_values with(v:=current);
        [gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|
         destruct POINTER as[NULL|[object[offset SAME]]];subst current;reflexivity|apply no_argument_values]).
  - split;[apply PTree.gss|]. intros identifier A B;unfold set_opttemp;repeat rewrite PTree.gso by congruence;reflexivity.
Qed.

Theorem gateway_number_add_source_path {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)parameters scaled scaled_offset part ignored memory symbol definition:
  gateway_ambient_closed backend property->
  (forall memory world,property memory world->Mem.weak_valid_pointer memory scaled(Ptrofs.unsigned scaled_offset)=true)->
  parameters!_scaled=Some(Vptr scaled scaled_offset)->parameters!_part=Some part->gateway_object_pointer_value part->
  Genv.find_symbol ge _PyNumber_Add=Some symbol->Genv.find_funct_ptr ge symbol=Some definition->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr);tptr(Tstruct __object noattr)](tptr(Tstruct __object noattr))cc_default->
  exists called_parameters,
    gateway_source_path backend ge definition[Vptr scaled scaled_offset;part](number_integer_add_cont called_parameters)property
      (Returnstate ignored(number_integer_release_value_cont parameters)memory)property /\
    (forall identifier,called_parameters!identifier=parameters!identifier).
Proof.
  intros CLOSED VALID SCALED PART POINTER SYMBOL FUNCTION TYPE;eexists;split.
  - gateway_bound_source_call CLOSED ltac:(fun _=>number_nonnull_expression property scaled scaled_offset VALID)ltac:(fun _=>reflexivity).
    number_sdk_reached CLOSED symbol _PyNumber_Add SYMBOL FUNCTION TYPE
      ltac:(fun _=>apply cons_argument_values with(v:=Vptr scaled scaled_offset);
        [gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|reflexivity|
         apply cons_argument_values with(v:=part);
         [gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|
          destruct POINTER as[NULL|[object[offset SAME]]];subst part;reflexivity|apply no_argument_values]]).
  - intro identifier;reflexivity.
Qed.

Theorem gateway_number_scaled_release_path {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)parameters scaled returned memory symbol definition:
  gateway_ambient_closed backend property->parameters!_scaled=Some scaled->gateway_object_pointer_value scaled->
  Genv.find_symbol ge _Py_DecRef=Some symbol->Genv.find_funct_ptr ge symbol=Some definition->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr)]tvoid cc_default->
  exists called_parameters,
    gateway_source_path backend ge definition[scaled](number_integer_release_scaled_cont called_parameters)property
      (Returnstate returned(number_integer_add_cont parameters)memory)property /\
    called_parameters!_value__1=Some returned /\
    (forall identifier,identifier<>_value__1->identifier<>_t'20->called_parameters!identifier=parameters!identifier).
Proof.
  intros CLOSED SCALED POINTER SYMBOL FUNCTION TYPE;eexists;split.
  - gateway_bound_source_call CLOSED ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
    number_sdk_reached CLOSED symbol _Py_DecRef SYMBOL FUNCTION TYPE
      ltac:(fun _=>apply cons_argument_values with(v:=scaled);
        [gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|
         destruct POINTER as[NULL|[object[offset SAME]]];subst scaled;reflexivity|apply no_argument_values]).
  - split;[apply PTree.gss|]. intros identifier A B;unfold set_opttemp;repeat rewrite PTree.gso by congruence;reflexivity.
Qed.

Theorem gateway_number_part_release_path {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)parameters part ignored memory symbol definition:
  gateway_ambient_closed backend property->parameters!_part=Some part->gateway_object_pointer_value part->
  Genv.find_symbol ge _Py_DecRef=Some symbol->Genv.find_funct_ptr ge symbol=Some definition->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr)]tvoid cc_default->
  gateway_source_path backend ge definition[part](number_integer_release_part_cont parameters)property
    (Returnstate ignored(number_integer_release_scaled_cont parameters)memory)property.
Proof.
  intros CLOSED PART POINTER SYMBOL FUNCTION TYPE.
  gateway_bound_source_call CLOSED ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
  number_sdk_reached CLOSED symbol _Py_DecRef SYMBOL FUNCTION TYPE
    ltac:(fun _=>apply cons_argument_values with(v:=part);
      [gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|
       destruct POINTER as[NULL|[object[offset SAME]]];subst part;reflexivity|apply no_argument_values]).
Qed.
