(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Real dictionary key guards observe the same source-constructed
   key and parent snapshots; a spoofed class or a duplicate cannot supply these facts. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Values Memory Integers Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayImport GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayValue
  GatewayObjectDiscipline GatewayObjectThreads GatewayObjectInstances GatewayReferenceKeyType GatewayContainerABI GatewayContainerGuards
  GatewayContainerLength GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceThreads GatewayReferenceGraphCapture
  GatewayReferenceContainerScope GatewayReferenceContainerContext GatewayGraphSnapshots.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Lemma gateway_reference_captured_root {World}python objects decimal_float ledger held world ticket pointer wire initial:
  @gateway_reference_scope World python objects decimal_float ledger held world->
  In(gateway_reference_graph_capture ticket pointer wire initial)held->gateway_rooted(python world)(objects world)pointer.
Proof.
  intros SCOPE MEMBER.
  destruct(gateway_reference_capture_member _ _ _ _ _ _ _ SCOPE MEMBER)as[[owner OWNED]REST].
  eapply gateway_reference_owned_rooted;[exact(proj1 SCOPE)|exact OWNED].
Qed.

Theorem gateway_reference_dictionary_key_integer {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects decimal_float(instances:gateway_instance_runtime backend ge python objects(fun _ _ _=>Logic.False))
    ledger held ticket key wire initial class_pointer before world returned after next observed:
  gateway_objects_ready(python world)(objects world)before->
  gateway_reference_scope python objects decimal_float ledger held world->
  In(gateway_reference_graph_capture ticket key wire initial)held->
  gateway_builtin_type_address ge gateway_unicode_kind class_pointer->
  gateway_object_operation backend gateway_api_is_instance[key;class_pointer]before world returned after next observed->
  exists status,returned=Vint status.
Proof.
  intros READY SCOPE MEMBER CLASS OPERATION.
  pose proof(gateway_reference_captured_root python objects decimal_float ledger held world ticket key wire initial SCOPE MEMBER)as ROOT.
  destruct(gateway_reference_capture_member _ _ _ _ _ _ _ SCOPE MEMBER)as[OWNER[PRIVATE[DESTROY[VALUE SNAPSHOT]]]].
  destruct(gateway_value_has_builtin_layout _ _ _ _ VALUE)as[description[kind[LOOKUP KIND]]].
  destruct(gateway_builtin_instance_operation _ _ _ _ _ instances before world key description kind gateway_unicode_kind class_pointer
    returned after next observed READY ROOT LOOKUP KIND CLASS OPERATION)as[status[SAME REST]].
  exists status;exact SAME.
Qed.

Theorem gateway_reference_dictionary_key_observed {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects decimal_float(instances:gateway_instance_runtime backend ge python objects(fun _ _ _=>Logic.False))
    ledger held ticket key wire initial class_pointer before world status after next observed:
  gateway_objects_ready(python world)(objects world)before->
  gateway_reference_scope python objects decimal_float ledger held world->
  In(gateway_reference_graph_capture ticket key wire initial)held->
  gateway_builtin_type_address ge gateway_unicode_kind class_pointer->0<Int.signed status->
  gateway_object_operation backend gateway_api_is_instance[key;class_pointer]before world(Vint status)after next observed->
  (exists characters,gateway_object_values initial key=Some(gateway_unicode_object characters)) /\
  gateway_observer_return(python world)(objects world)before(python next)(objects next)after.
Proof.
  intros READY SCOPE MEMBER CLASS POSITIVE OPERATION.
  pose proof(gateway_reference_captured_root python objects decimal_float ledger held world ticket key wire initial SCOPE MEMBER)as ROOT.
  destruct(gateway_reference_capture_member _ _ _ _ _ _ _ SCOPE MEMBER)as[OWNER[PRIVATE[DESTROY[VALUE[INITIAL SNAPSHOT]]]]].
  destruct(gateway_reference_actual_unicode_key backend ge python objects decimal_float instances ledger held before world key wire class_pointer
    status after next observed READY SCOPE ROOT VALUE CLASS OPERATION POSITIVE)
    as[ONE[[characters LOOKUP][NEXT_SCOPE EFFECT]]].
  split;[exists characters;rewrite SNAPSHOT in LOOKUP by constructor;exact LOOKUP|exact EFFECT].
Qed.

Theorem gateway_reference_dictionary_contains_integer {World Event}(backend:gateway_backend World Event)
    python objects decimal_float(abi:gateway_container_abi_runtime backend python objects)
    ledger held parent_ticket parent fields entries parent_initial key_ticket key key_wire key_initial characters
    before world returned after next observed:
  gateway_objects_ready(python world)(objects world)before->
  gateway_reference_scope python objects decimal_float ledger held world->
  In(gateway_reference_graph_capture parent_ticket parent
    (LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields entries))parent_initial)held->
  In(gateway_reference_graph_capture key_ticket key key_wire key_initial)held->
  gateway_object_values parent_initial parent=Some(gateway_dict_object fields)->
  gateway_object_values key_initial key=Some(gateway_unicode_object characters)->
  gateway_object_operation backend gateway_api_dict_contains[parent;key]before world returned after next observed->
  exists status,returned=Vint status.
Proof.
  intros READY SCOPE PARENT KEY PARENT_LOOKUP KEY_LOOKUP OPERATION.
  pose proof(gateway_reference_captured_root _ _ _ _ _ _ _ _ _ _ SCOPE PARENT)as PARENT_ROOT.
  pose proof(gateway_reference_captured_root _ _ _ _ _ _ _ _ _ _ SCOPE KEY)as KEY_ROOT.
  destruct(gateway_reference_graph_snapshot _ _ _ _ _ _ _ _ _ _ SCOPE PARENT)as[PARENT_DESTROY PARENT_SNAPSHOT].
  destruct(gateway_reference_graph_snapshot _ _ _ _ _ _ _ _ _ _ SCOPE KEY)as[KEY_DESTROY KEY_SNAPSHOT].
  eapply gateway_dict_contains_integer;[exact abi|exact READY|exact PARENT_ROOT|exact KEY_ROOT| | |exact OPERATION].
  - rewrite PARENT_SNAPSHOT by constructor;exact PARENT_LOOKUP.
  - rewrite KEY_SNAPSHOT by constructor;exact KEY_LOOKUP.
Qed.

Theorem gateway_reference_dictionary_contains_observed {World Event}(backend:gateway_backend World Event)
    python objects decimal_float(containers:gateway_container_runtime backend python objects)
    ledger held parent_ticket parent fields entries parent_initial key_ticket key key_wire key_initial characters
    before world after next observed:
  gateway_objects_ready(python world)(objects world)before->
  gateway_reference_scope python objects decimal_float ledger held world->
  In(gateway_reference_graph_capture parent_ticket parent
    (LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields entries))parent_initial)held->
  In(gateway_reference_graph_capture key_ticket key key_wire key_initial)held->
  gateway_object_values parent_initial parent=Some(gateway_dict_object fields)->
  gateway_object_values key_initial key=Some(gateway_unicode_object characters)->
  gateway_object_operation backend gateway_api_dict_contains[parent;key]before world(Vint Int.zero)after next observed->
  gateway_dictionary_lookup characters fields=None /\
  gateway_observer_return(python world)(objects world)before(python next)(objects next)after.
Proof.
  intros READY SCOPE PARENT KEY PARENT_LOOKUP KEY_LOOKUP OPERATION.
  pose proof(gateway_reference_captured_root _ _ _ _ _ _ _ _ _ _ SCOPE PARENT)as PARENT_ROOT.
  pose proof(gateway_reference_captured_root _ _ _ _ _ _ _ _ _ _ SCOPE KEY)as KEY_ROOT.
  destruct(gateway_reference_graph_snapshot _ _ _ _ _ _ _ _ _ _ SCOPE PARENT)as[PARENT_DESTROY PARENT_SNAPSHOT].
  destruct(gateway_reference_graph_snapshot _ _ _ _ _ _ _ _ _ _ SCOPE KEY)as[KEY_DESTROY KEY_SNAPSHOT].
  assert(PARENT_CURRENT:gateway_object_values(objects world)parent=Some(gateway_dict_object fields))
    by(rewrite PARENT_SNAPSHOT by constructor;exact PARENT_LOOKUP).
  assert(KEY_CURRENT:gateway_object_values(objects world)key=Some(gateway_unicode_object characters))
    by(rewrite KEY_SNAPSHOT by constructor;exact KEY_LOOKUP).
  destruct(gateway_runtime_dict_contains _ _ _ containers before world parent fields key characters Int.zero after next observed
    READY PARENT_ROOT KEY_ROOT PARENT_CURRENT KEY_CURRENT OPERATION)as[RESULT EFFECT].
  assert(NONERROR:Int.zero<>Int.neg Int.one)by(vm_compute;discriminate).
  split;[|apply EFFECT;exact NONERROR].
  destruct RESULT as[[SAME UNIQUE]|[[SAME DUPLICATE]|NEGATIVE]];[exact UNIQUE| |contradiction].
  exfalso;apply Int.one_not_zero;symmetry;exact SAME.
Qed.
