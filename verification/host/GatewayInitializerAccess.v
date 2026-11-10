(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: SDK calls retain existing native allocation roles
   without a contents frame. *)
From Stdlib Require Import List ZArith.
From compcert Require Import Integers Values Memory.
From HostGateway Require Import GatewayMachine GatewayRuntime GatewayPython GatewayObjects GatewayInitializerSDK
  GatewayInitializerObjectBindings GatewayInitializerObjectsSource GatewayErrorRuntime GatewayNativeRegions.
Import ListNotations.

Definition gateway_initializer_native_retained {World}(native:World->block->Prop)before world after next:Prop:=
  forall object,Mem.valid_block before object->native world object->Mem.valid_block after object /\native next object.

(* These are allocation-identity and representation effects, not write exclusion.
   Reentrant callbacks may change permitted C-global values and public objects. *)
Record gateway_initializer_access_runtime {World Event}(backend:gateway_backend World Event)
    (python:World->python_world)(objects:World->gateway_object_heap)(normal:mem->World->Prop)
    (native:World->block->Prop)(module_descriptor:mem->World->Values.val->Prop):Prop:={
  gateway_initializer_import_native:forall before world name bytes result after next observed,
    normal before world->gateway_error_cstring before name bytes->
    gateway_runtime_operation backend initializer_import_definition[name]before world result after next observed->
    gateway_initializer_native_retained native before world after next;
  gateway_initializer_attribute_native:forall before world object name bytes result after next observed,
    normal before world->gateway_rooted(python world)(objects world)object->gateway_error_cstring before name bytes->
    gateway_runtime_operation backend initializer_attribute_definition[object;name]before world result after next observed->
    gateway_initializer_native_retained native before world after next;
  gateway_initializer_module_native:forall before world descriptor result after next observed,
    normal before world->module_descriptor before world descriptor->
    gateway_runtime_operation backend initializer_module_definition[descriptor;Vint(Int.repr 3%Z)]before world result after next observed->
    gateway_initializer_native_retained native before world after next;
  gateway_initializer_add_native:forall before world module name bytes object result after next observed,
    normal before world->gateway_rooted(python world)(objects world)module->gateway_rooted(python world)(objects world)object->
    gateway_error_cstring before name bytes->
    gateway_runtime_operation backend initializer_add_definition[module;name;object]before world result after next observed->
    gateway_initializer_native_retained native before world after next;
  gateway_initializer_add_ref_native:forall before world module name bytes object result after next observed,
    normal before world->gateway_rooted(python world)(objects world)module->gateway_rooted(python world)(objects world)object->
    gateway_error_cstring before name bytes->
    gateway_runtime_operation backend initializer_add_ref_definition[module;name;object]before world result after next observed->
    gateway_initializer_native_retained native before world after next
}.

Lemma gateway_initializer_native_region_retained {World}native protected before world after next:
  @gateway_native_region_owned World native protected before world->gateway_initializer_native_retained native before world after next->
  gateway_native_region_owned native protected after next.
Proof. intros OWNED RETAIN object position MEMBER;destruct(OWNED object position MEMBER)as[LIVE NATIVE];apply RETAIN;assumption. Qed.

Section Lift.
Context {World Event}(backend:gateway_backend World Event)python objects normal attached native module_descriptor exported
  (sdk:gateway_initializer_sdk backend python objects normal attached module_descriptor exported)
  (access:gateway_initializer_access_runtime backend python objects normal native module_descriptor)
  (protected:block->Z->Prop).
Let clear:=fun memory world=>normal memory world /\gateway_native_region_owned native protected memory world.
Let rooted:=fun memory world=>attached memory world /\gateway_native_region_owned native protected memory world.

Lemma gateway_initializer_new_reference_native_roles before world result after next:
  gateway_native_region_owned native protected after next->
  gateway_initializer_new_reference python objects normal attached before world result after next->
  gateway_initializer_new_reference python objects clear rooted before world result after next.
Proof.
  intros OWNED[ATTACHED[NULL|[NORMAL[CREDIT ROOT]]]].
  - split;[split;assumption|left;exact NULL].
  - split;[split;assumption|right;split;[split;assumption|split;assumption]].
Qed.

Theorem gateway_initializer_sdk_with_native_roles:
  gateway_initializer_sdk backend python objects clear rooted module_descriptor exported.
Proof.
  constructor.
  - intros before world name bytes result after next observed[SIDE OWNED]STRING OPERATION.
    eapply gateway_initializer_new_reference_native_roles.
    + eapply gateway_initializer_native_region_retained;[exact OWNED|].
      eapply gateway_initializer_import_native;[exact access|exact SIDE|exact STRING|exact OPERATION].
    + eapply gateway_initializer_import_effect;[exact sdk|exact SIDE|exact STRING|exact OPERATION].
  - intros before world object name bytes result after next observed[SIDE OWNED]OBJECT STRING OPERATION.
    eapply gateway_initializer_new_reference_native_roles.
    + eapply gateway_initializer_native_region_retained;[exact OWNED|].
      eapply gateway_initializer_attribute_native;[exact access|exact SIDE|exact OBJECT|exact STRING|exact OPERATION].
    + eapply gateway_initializer_attribute_effect;[exact sdk|exact SIDE|exact OBJECT|exact STRING|exact OPERATION].
  - intros before world descriptor result after next observed[SIDE OWNED]DESCRIPTOR OPERATION.
    eapply gateway_initializer_new_reference_native_roles.
    + eapply gateway_initializer_native_region_retained;[exact OWNED|].
      eapply gateway_initializer_module_native;[exact access|exact SIDE|exact DESCRIPTOR|exact OPERATION].
    + eapply gateway_initializer_module_effect;[exact sdk|exact SIDE|exact DESCRIPTOR|exact OPERATION].
  - intros before world module name bytes object result after next observed[SIDE OWNED]MODULE OBJECT STRING OPERATION.
    assert(RETAINED:gateway_native_region_owned native protected after next).
    { eapply gateway_initializer_native_region_retained;[exact OWNED|].
      eapply gateway_initializer_add_native;[exact access|exact SIDE|exact MODULE|exact OBJECT|exact STRING|exact OPERATION]. }
    destruct(gateway_initializer_add_effect _ _ _ _ _ _ _ sdk before world module name bytes object result after next observed
      SIDE MODULE OBJECT STRING OPERATION)as[ATTACHED[status[RESULT[SUCCESS FAILURE]]]].
    split;[split;assumption|]. exists status;split;[exact RESULT|]. split;[|exact FAILURE].
    intro ZERO;destruct(SUCCESS ZERO)as[NORMAL[DEBIT EXPORT]];split;[split;assumption|split;assumption].
  - intros before world module name bytes object result after next observed[SIDE OWNED]MODULE OBJECT STRING OPERATION.
    assert(RETAINED:gateway_native_region_owned native protected after next).
    { eapply gateway_initializer_native_region_retained;[exact OWNED|].
      eapply gateway_initializer_add_ref_native;[exact access|exact SIDE|exact MODULE|exact OBJECT|exact STRING|exact OPERATION]. }
    destruct(gateway_initializer_add_ref_effect _ _ _ _ _ _ _ sdk before world module name bytes object result after next observed
      SIDE MODULE OBJECT STRING OPERATION)as[ATTACHED[COUNTS[status[RESULT SUCCESS]]]].
    split;[split;assumption|]. split;[exact COUNTS|]. exists status;split;[exact RESULT|].
    intro ZERO;destruct(SUCCESS ZERO)as[NORMAL EXPORT];split;[split;assumption|exact EXPORT].
Qed.
End Lift.
