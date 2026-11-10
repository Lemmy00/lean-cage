(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The one-argument callback follows the same actual helper execution. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine CallContexts.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayRuntime GatewayBindings GatewayContexts
  GatewayPresentationRuntime GatewayPresentationSource GatewaySourcePaths GatewaySourceSDKReceipt GatewayFramedRuntime
  GatewayReadonly GatewayPure GatewayValueReturns.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_presentation_new_definition:Ctypes.fundef Clight.function:=External(EF_external "PyTuple_New"(mksignature[Xlong]Xptr cc_default))
  [tlong](tptr(Tstruct __object noattr))cc_default.
Definition gateway_presentation_set_definition:Ctypes.fundef Clight.function:=External(EF_external "PyTuple_SetItem"(mksignature[Xptr;Xlong;Xptr]Xint cc_default))
  [tptr(Tstruct __object noattr);tlong;tptr(Tstruct __object noattr)]tint cc_default.
Definition gateway_presentation_call_definition:Ctypes.fundef Clight.function:=External(EF_external "PyObject_CallObject"(mksignature[Xptr;Xptr]Xptr cc_default))
  [tptr(Tstruct __object noattr);tptr(Tstruct __object noattr)](tptr(Tstruct __object noattr))cc_default.
Definition gateway_presentation_release_definition:Ctypes.fundef Clight.function:=External(EF_external "Py_DecRef"(mksignature[Xptr]Xvoid cc_default))
  [tptr(Tstruct __object noattr)]tvoid cc_default.

Definition gateway_presentation_bindings ge:Prop:=
  gateway_function_binding ge _PyTuple_New gateway_presentation_new_definition /\
  gateway_function_binding ge _Py_IncRef python_incref_definition /\
  gateway_function_binding ge _PyTuple_SetItem gateway_presentation_set_definition /\
  gateway_function_binding ge _PyObject_CallObject gateway_presentation_call_definition /\
  gateway_function_binding ge _Py_DecRef gateway_presentation_release_definition.

Theorem gateway_actual_presentation_bindings:gateway_presentation_bindings(Clight.globalenv prog).
Proof. unfold gateway_presentation_bindings;repeat split;apply gateway_actual_function_binding;vm_compute;reflexivity. Qed.

(* Every transition below is an individual SDK occurrence selected from this
   run. The properties can carry the current source ledger and reserved roots. *)
Theorem gateway_actual_presentation_body {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (initial:mem->World->Prop)(new_ready incremented installed:Values.val->mem->World->Prop)
    (called:Values.val->Values.val->mem->World->Prop)(released:Values.val->mem->World->Prop)
    parameters array offset child child_offset callable callable_offset before world events value after next:
  gateway_presentation_bindings ge->
  parameters!_count=Some(Vint Int.one)->parameters!_values=Some(Vptr array offset)->
  parameters!_callable=Some(Vptr callable callable_offset)->Ptrofs.unsigned offset+8<=Ptrofs.modulus->
  gateway_ambient_closed backend initial->
  (forall tuple,gateway_ambient_closed backend(new_ready tuple))->
  (forall tuple,gateway_ambient_closed backend(incremented tuple))->
  (forall tuple,gateway_ambient_closed backend(installed tuple))->
  (forall tuple returned,gateway_ambient_closed backend(called tuple returned))->
  (forall returned,gateway_ambient_closed backend(released returned))->
  (forall tuple memory current,new_ready tuple memory current->
    exists object displacement,tuple=Vptr object displacement /\
      Mem.weak_valid_pointer memory object(Ptrofs.unsigned displacement)=true /\
      Mem.load Mptr memory array(Ptrofs.unsigned offset)=Some(Vptr child child_offset))->
  (forall tuple memory current,incremented tuple memory current->
    Mem.load Mptr memory array(Ptrofs.unsigned offset)=Some(Vptr child child_offset))->
  (forall memory current returned changed following observed,initial memory current->
    gateway_presentation_operation backend gateway_presentation_tuple_new[Vlong Int64.one]
      memory current returned changed following observed->
    returned=Vnullptr \/exists object displacement,returned=Vptr object displacement /\new_ready returned changed following)->
  (forall tuple memory current returned changed following observed,new_ready tuple memory current->
    gateway_runtime_operation backend python_incref_definition[Vptr child child_offset]
      memory current returned changed following observed->incremented tuple changed following)->
  (forall tuple memory current returned changed following observed,incremented tuple memory current->
    gateway_presentation_operation backend gateway_presentation_tuple_set[tuple;Vlong Int64.zero;Vptr child child_offset]
      memory current returned changed following observed->returned=Vint Int.zero /\installed tuple changed following)->
  (forall tuple memory current returned changed following observed,installed tuple memory current->
    gateway_presentation_operation backend gateway_presentation_call[Vptr callable callable_offset;tuple]
      memory current returned changed following observed->gateway_object_pointer_value returned /\called tuple returned changed following)->
  (forall tuple selected memory current returned changed following observed,called tuple selected memory current->
    gateway_presentation_operation backend gateway_presentation_tuple_release[tuple]
      memory current returned changed following observed->released selected changed following)->
  initial before world->
  gateway_steps backend ge(gateway_live(State f_host_call_objects(fn_body f_host_call_objects)Kstop empty_env parameters before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  exists tuple prefix suffix called_memory called_world returned_memory returned_world observed,
    events=prefix++gateway_primitive observed::suffix /\
    gateway_presentation_operation backend gateway_presentation_call[Vptr callable callable_offset;tuple]
      called_memory called_world value returned_memory returned_world observed /\
    installed tuple called_memory called_world /\called tuple value returned_memory returned_world /\released value after next.
Proof.
  intros [NEW_BIND [INC_BIND [SET_BIND [CALL_BIND RELEASE_BIND]]]] COUNT ARRAY CALLABLE NOWRAP
    CLOSED NEW_CLOSED INC_CLOSED SET_CLOSED CALL_CLOSED RELEASE_CLOSED NEW_INPUT INC_INPUT
    NEW_EFFECT INC_EFFECT SET_EFFECT CALL_EFFECT RELEASE_EFFECT INPUT RUN NONNULL.
  destruct NEW_BIND as[new_symbol[NEW_SYMBOL NEW_FUNCTION]].
  destruct INC_BIND as[inc_symbol[INC_SYMBOL INC_FUNCTION]].
  destruct SET_BIND as[set_symbol[SET_SYMBOL SET_FUNCTION]].
  destruct CALL_BIND as[call_symbol[CALL_SYMBOL CALL_FUNCTION]].
  destruct RELEASE_BIND as[release_symbol[RELEASE_SYMBOL RELEASE_FUNCTION]].
  pose proof(gateway_presentation_new_source backend ge initial parameters before new_symbol gateway_presentation_new_definition
    CLOSED COUNT NEW_SYMBOL NEW_FUNCTION eq_refl)as NEW_SOURCE.
  destruct(gateway_source_sdk_receipt backend ge _ _ _ _ [Vlong Int64.one](gateway_presentation_new_cont parameters)
    initial(State f_host_call_objects(fn_body f_host_call_objects)Kstop empty_env parameters before)
    before world events value after next ltac:(exact I)ltac:(cbn;lia)CLOSED NEW_SOURCE INPUT RUN)
    as(p0 &r0 &m0 &w0 &tuple &m1 &w1 &e0 &EVENTS0 &READY0 &PREFIX0 &OP0 &REST0).
  assert(NEW_OP:gateway_presentation_operation backend gateway_presentation_tuple_new[Vlong Int64.one]m0 w0 tuple m1 w1 e0).
  { exists gateway_presentation_new_definition;split;[reflexivity|exact OP0]. }
  destruct(NEW_EFFECT m0 w0 tuple m1 w1 e0 READY0 NEW_OP)as[NULL|[tuple_block[tuple_offset[TUPLE READY1]]]].
  { subst tuple;exfalso;apply NONNULL;eapply gateway_presentation_new_failed;exact REST0. }
  subst tuple.
  assert(TUPLE_POINTER:forall memory current,new_ready(Vptr tuple_block tuple_offset)memory current->
    Mem.weak_valid_pointer memory tuple_block(Ptrofs.unsigned tuple_offset)=true).
  { intros memory current GOOD;destruct(NEW_INPUT _ memory current GOOD)as[object[displacement[SAME[POINTER LOAD]]]];
      injection SAME as SAME OFFSET;subst object displacement;exact POINTER. }
  assert(TUPLE_LOAD:forall memory current,new_ready(Vptr tuple_block tuple_offset)memory current->
    Mem.load Mptr memory array(Ptrofs.unsigned offset)=Some(Vptr child child_offset)).
  { intros memory current GOOD;destruct(NEW_INPUT _ memory current GOOD)as[object[displacement[SAME[POINTER LOAD]]]];exact LOAD. }
  destruct(gateway_presentation_incref_source backend ge(new_ready(Vptr tuple_block tuple_offset))parameters array offset tuple_block tuple_offset
    child child_offset m1 inc_symbol python_incref_definition(NEW_CLOSED _)COUNT ARRAY NOWRAP TUPLE_POINTER TUPLE_LOAD
    INC_SYMBOL INC_FUNCTION eq_refl)
    as[inc_parameters[INC_SOURCE[INC_TUPLE[INC_ARRAY[INC_COUNT[INC_INDEX INC_CALLABLE]]]]]].
  destruct(gateway_source_sdk_receipt backend ge _ _ _ _ [Vptr child child_offset](gateway_presentation_incref_cont inc_parameters)
    (new_ready(Vptr tuple_block tuple_offset))(Returnstate(Vptr tuple_block tuple_offset)(gateway_presentation_new_cont parameters)m1)
    m1 w1 r0 value after next ltac:(exact I)ltac:(cbn;lia)(NEW_CLOSED _)INC_SOURCE READY1 REST0)
    as(p1 &r1 &m2 &w2 &ignored &m3 &w3 &e1 &EVENTS1 &READY2 &PREFIX1 &OP1 &REST1).
  pose proof(INC_EFFECT _ m2 w2 ignored m3 w3 e1 READY2 OP1)as READY3.
  destruct(gateway_presentation_set_source backend ge(incremented(Vptr tuple_block tuple_offset))inc_parameters array offset tuple_block tuple_offset
    child child_offset ignored m3 set_symbol gateway_presentation_set_definition(INC_CLOSED _)INC_INDEX
    ltac:(rewrite INC_ARRAY;exact ARRAY)INC_TUPLE NOWRAP(INC_INPUT _)SET_SYMBOL SET_FUNCTION eq_refl)
    as[set_parameters[SET_SOURCE[SET_TUPLE[SET_ARRAY[SET_COUNT[SET_INDEX SET_CALLABLE]]]]]].
  destruct(gateway_source_sdk_receipt backend ge _ _ _ _ [Vptr tuple_block tuple_offset;Vlong Int64.zero;Vptr child child_offset]
    (gateway_presentation_set_cont set_parameters)(incremented(Vptr tuple_block tuple_offset))
    (Returnstate ignored(gateway_presentation_incref_cont inc_parameters)m3)m3 w3 r1 value after next
    ltac:(exact I)ltac:(cbn;lia)(INC_CLOSED _)SET_SOURCE READY3 REST1)
    as(p2 &r2 &m4 &w4 &status &m5 &w5 &e2 &EVENTS2 &READY4 &PREFIX2 &OP2 &REST2).
  assert(SET_OP:gateway_presentation_operation backend gateway_presentation_tuple_set
    [Vptr tuple_block tuple_offset;Vlong Int64.zero;Vptr child child_offset]m4 w4 status m5 w5 e2).
  { exists gateway_presentation_set_definition;split;[reflexivity|exact OP2]. }
  destruct(SET_EFFECT _ m4 w4 status m5 w5 e2 READY4 SET_OP)as[STATUS READY5];subst status.
  destruct(gateway_presentation_call_source backend ge(installed(Vptr tuple_block tuple_offset))set_parameters tuple_block tuple_offset
    callable callable_offset m5 call_symbol gateway_presentation_call_definition(SET_CLOSED _)
    ltac:(rewrite SET_INDEX;exact INC_INDEX)ltac:(rewrite SET_COUNT,INC_COUNT;exact COUNT)
    ltac:(rewrite SET_TUPLE;exact INC_TUPLE)ltac:(rewrite SET_CALLABLE,INC_CALLABLE;exact CALLABLE)
    CALL_SYMBOL CALL_FUNCTION eq_refl)
    as[call_parameters[CALL_SOURCE[CALL_TUPLE[CALL_ARRAY[CALL_COUNT[CALL_INDEX CALL_CALLABLE]]]]]].
  destruct(gateway_source_sdk_receipt backend ge _ _ _ _ [Vptr callable callable_offset;Vptr tuple_block tuple_offset]
    (gateway_presentation_call_cont call_parameters)(installed(Vptr tuple_block tuple_offset))
    (Returnstate(Vint Int.zero)(gateway_presentation_set_cont set_parameters)m5)m5 w5 r2 value after next
    ltac:(exact I)ltac:(cbn;lia)(SET_CLOSED _)CALL_SOURCE READY5 REST2)
    as(p3 &r3 &m6 &w6 &result &m7 &w7 &e3 &EVENTS3 &READY6 &PREFIX3 &OP3 &REST3).
  assert(CALL_OP:gateway_presentation_operation backend gateway_presentation_call
    [Vptr callable callable_offset;Vptr tuple_block tuple_offset]m6 w6 result m7 w7 e3).
  { exists gateway_presentation_call_definition;split;[reflexivity|exact OP3]. }
  destruct(CALL_EFFECT _ m6 w6 result m7 w7 e3 READY6 CALL_OP)as[POINTER READY7].
  destruct(gateway_presentation_release_source backend ge(called(Vptr tuple_block tuple_offset)result)call_parameters tuple_block tuple_offset
    result m7 release_symbol gateway_presentation_release_definition(CALL_CLOSED _ _)
    ltac:(rewrite CALL_TUPLE,SET_TUPLE;exact INC_TUPLE)RELEASE_SYMBOL RELEASE_FUNCTION eq_refl)
    as[release_parameters[RELEASE_SOURCE[RELEASE_TUPLE[RELEASE_RESULT RELEASE_CALLABLE]]]].
  destruct(gateway_source_sdk_receipt backend ge _ _ _ _ [Vptr tuple_block tuple_offset]
    (gateway_presentation_release_cont release_parameters)(called(Vptr tuple_block tuple_offset)result)
    (Returnstate result(gateway_presentation_call_cont call_parameters)m7)m7 w7 r3 value after next
    ltac:(exact I)ltac:(cbn;lia)(CALL_CLOSED _ _)RELEASE_SOURCE READY7 REST3)
    as(p4 &r4 &m8 &w8 &released_value &m9 &w9 &e4 &EVENTS4 &READY8 &PREFIX4 &OP4 &REST4).
  assert(RELEASE_OP:gateway_presentation_operation backend gateway_presentation_tuple_release[Vptr tuple_block tuple_offset]
    m8 w8 released_value m9 w9 e4).
  { exists gateway_presentation_release_definition;split;[reflexivity|exact OP4]. }
  pose proof(RELEASE_EFFECT _ result m8 w8 released_value m9 w9 e4 READY8 RELEASE_OP)as READY9.
  destruct(gateway_pure_path_ready_return backend ge(released result)(RELEASE_CLOSED result)
    (Returnstate released_value(gateway_presentation_release_cont release_parameters)m9)result w9 r4 value after next
    (gateway_presentation_return_pure ge release_parameters released_value result m9 RELEASE_RESULT POINTER)READY9 REST4)
    as[SAME[FINAL QUIET]].
  subst result.
  exists(Vptr tuple_block tuple_offset),(p0++gateway_primitive e0::p1++gateway_primitive e1::p2++gateway_primitive e2::p3),r3,m6,w6,m7,w7,e3.
  split.
  - rewrite EVENTS0,EVENTS1,EVENTS2,EVENTS3;repeat first[rewrite<-app_assoc|progress cbn[app]];reflexivity.
  - split;[exact CALL_OP|]. split;[exact READY6|]. split;assumption.
Qed.
