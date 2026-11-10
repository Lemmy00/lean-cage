(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A dictionary key test uses the independently source-constructed
   builtin layout, so an arbitrary object's spoofed class cannot supply this conclusion. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers Values Memory Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayValue
  GatewayObjectInstances GatewayReferenceThreads GatewayReferenceObservers.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Lemma gateway_value_has_builtin_layout decimal_float heap object wire:
  gateway_value_heap decimal_float heap object wire->exists value kind,
    gateway_object_values heap object=Some value /\gateway_object_kind value=Some kind.
Proof.
  intro VALUE;inversion VALUE;subst.
  - exists gateway_none_object,gateway_none_kind;auto.
  - eexists;exists gateway_bool_kind;split;[eassumption|reflexivity].
  - destruct(gateway_scalar_layout_is_builtin _ _ _ _ H0)as[kind[KIND CHOICES]]. eexists;exists kind;split;[eassumption|exact KIND].
  - eexists;exists gateway_list_kind;split;[eassumption|reflexivity].
  - eexists;exists gateway_dict_kind;split;[eassumption|reflexivity].
Qed.

Lemma gateway_known_positive_unicode heap pointer value actual status:
  gateway_object_values heap pointer=Some value->gateway_object_kind value=Some actual->
  gateway_instance_result heap pointer gateway_unicode_kind status->0<Int.signed status->
  status=Int.one /\exists characters,value=gateway_unicode_object characters.
Proof.
  intros LOOKUP KIND RESULT POSITIVE.
  destruct(gateway_known_instance_result _ _ _ _ _ _ LOOKUP KIND RESULT)as[SAME|NEGATIVE].
  - subst status;destruct value;cbn in KIND;try discriminate;injection KIND as SAME;subst actual;
      cbn[gateway_builtin_accepts]in POSITIVE|-*;try(change(0<0)in POSITIVE;lia).
    split;[reflexivity|eexists;reflexivity].
  - subst status;change(0< -1)in POSITIVE;lia.
Qed.

Theorem gateway_reference_actual_unicode_key {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects decimal_float
    (instances:gateway_instance_runtime backend ge python objects(fun _ _ _=>False))
    ledger held before world key wire class_pointer status after next observed:
  gateway_objects_ready(python world)(objects world)before->
  gateway_reference_scope python objects decimal_float ledger held world->
  gateway_rooted(python world)(objects world)key->gateway_value_heap decimal_float(objects world)key wire->
  gateway_builtin_type_address ge gateway_unicode_kind class_pointer->
  gateway_object_operation backend gateway_api_is_instance[key;class_pointer]before world(Vint status)after next observed->
  0<Int.signed status->
  status=Int.one /\(exists characters,gateway_object_values(objects world)key=Some(gateway_unicode_object characters)) /\
  gateway_reference_scope python objects decimal_float ledger held next /\
  gateway_observer_return(python world)(objects world)before(python next)(objects next)after.
Proof.
  intros READY SCOPE ROOT VALUE CLASS OPERATION POSITIVE.
  destruct(gateway_value_has_builtin_layout _ _ _ _ VALUE)as[value[kind[LOOKUP KIND]]].
  destruct(gateway_builtin_instance_operation _ _ _ _ _ instances before world key value kind gateway_unicode_kind class_pointer (Vint status)after next observed
    READY ROOT LOOKUP KIND CLASS OPERATION)as[returned[SAME[RESULT[RETAINED OBSERVER]]]].
  injection SAME as STATUS;subst returned.
  destruct(gateway_known_positive_unicode _ _ _ _ _ LOOKUP KIND RESULT POSITIVE)as[ONE[characters ACTUAL]].
  assert(NOT_ERROR:status<>Int.neg Int.one)by(intro NEG;rewrite NEG in POSITIVE;change(0< -1)in POSITIVE;lia).
  pose proof(OBSERVER NOT_ERROR)as EFFECT.
  split;[exact ONE|]. split;[exists characters;rewrite ACTUAL in LOOKUP;exact LOOKUP|]. split.
  - eapply gateway_reference_observer_scope;eassumption.
  - exact EFFECT.
Qed.
