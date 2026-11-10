(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Type tests consume an independently established builtin layout. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Integers Values Memory Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayRootLeases.
Import ListNotations.

Inductive gateway_builtin_type_address(ge:Clight.genv):gateway_builtin_kind->Values.val->Prop:=
|gateway_builtin_unicode_type:forall object,Genv.find_symbol ge _PyUnicode_Type=Some object ->
    gateway_builtin_type_address ge gateway_unicode_kind(Vptr object Ptrofs.zero)
|gateway_builtin_bytes_type:forall object,Genv.find_symbol ge _PyBytes_Type=Some object ->
    gateway_builtin_type_address ge gateway_bytes_kind(Vptr object Ptrofs.zero)
|gateway_builtin_long_type:forall object,Genv.find_symbol ge _PyLong_Type=Some object ->
    gateway_builtin_type_address ge gateway_long_kind(Vptr object Ptrofs.zero)
|gateway_builtin_dictionary_type:forall object,Genv.find_symbol ge _PyDict_Type=Some object ->
    gateway_builtin_type_address ge gateway_dict_kind(Vptr object Ptrofs.zero).

Record gateway_instance_runtime {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (python:World->python_world)(objects:World->gateway_object_heap)(leases:World->nat->Values.val->Prop):Prop:={
  gateway_builtin_instance_operation:forall before world object value actual expected class_object result after next observed,
    gateway_objects_ready(python world)(objects world)before ->
    gateway_rooted(python world)(objects world)object ->
    gateway_object_values(objects world)object=Some value ->gateway_object_kind value=Some actual ->
    gateway_builtin_type_address ge expected class_object ->
    gateway_object_operation backend gateway_api_is_instance[object;class_object]before world result after next observed ->
    exists status,result=Vint status /\gateway_instance_result(objects world)object expected status /\
      gateway_leases_retained leases world next /\
      (status<>Int.neg Int.one ->gateway_observer_return(python world)(objects world)before(python next)(objects next)after)
}.

(* Positive IsInstance alone is not used to infer the object's layout. *)
Lemma gateway_known_instance_result heap object value actual expected status :
  gateway_object_values heap object=Some value ->gateway_object_kind value=Some actual ->
  gateway_instance_result heap object expected status ->
  status=(if gateway_builtin_accepts expected actual then Int.one else Int.zero) \/status=Int.neg Int.one.
Proof.
  intros LOOKUP KIND RESULT;inversion RESULT;subst.
  - assert(SAME:value0=value)by congruence;subst value0.
    assert(SAME:actual0=actual)by congruence;subst actual0;left;reflexivity.
  - match goal with FOREIGN:forall description,gateway_object_values heap object=Some description ->gateway_object_kind description=None|-_=>
      specialize(FOREIGN value LOOKUP);rewrite KIND in FOREIGN;discriminate end.
  - right;reflexivity.
Qed.
