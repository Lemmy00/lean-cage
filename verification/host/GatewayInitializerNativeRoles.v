(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Initial native roles survive the actual individual
  operations. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewayPython GatewayObjects GatewayThreadRuntime GatewayObjectThreads
  GatewayStreamInterface GatewayNativeRegions GatewayRegionThreads GatewayReferenceThreads GatewayBootstrapRuntime GatewayBootstrapReferenceScope
  GatewayInterpreterRuntime.
Import ListNotations.
Local Close Scope lean_scope.

Section NativeRoles.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
  (native:World->block->Prop)(stable:World->block->Z->Prop)
  (base:option Values.val->mem->World->Prop)(protected:block->Z->Prop).
Let side:=gateway_native_region_discipline native base protected.

Lemma gateway_native_roles_bootstrap_post output before world after next observed:
  gateway_native_region_owned native protected before world ->
  gateway_bootstrap_post io native stable base output before world after next observed ->
  gateway_bootstrap_post io native stable side output before world after next observed.
Proof.
  intros HELD[NEXT[ACCESS[FRAME QUIET]]];split;[|split;[exact ACCESS|split;assumption]].
  split;[exact NEXT|];eapply gateway_native_region_effect;eassumption.
Qed.

Theorem gateway_bootstrap_with_native_roles module_filename canonicalizes
    (runtime:gateway_bootstrap_runtime backend io native stable base module_filename canonicalizes):
  gateway_bootstrap_runtime backend io native stable side module_filename canonicalizes.
Proof.
  constructor.
  - intros before world address object offset result after next observed[SIDE HELD]NATIVE POINTER ACCESS OPERATION.
    destruct(gateway_loader_address_operation _ _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ _
      SIDE NATIVE POINTER ACCESS OPERATION)as[POST REST].
    split;[eapply gateway_native_roles_bootstrap_post;eassumption|exact REST].
  - intros before world pointer bytes maximum result after next observed[SIDE HELD]STRING PROTECTED MAXIMUM OPERATION.
    destruct(gateway_bounded_length_operation _ _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ _
      SIDE STRING PROTECTED MAXIMUM OPERATION)as[POST REST].
    split;[eapply gateway_native_roles_bootstrap_post;eassumption|exact REST].
  - intros before world first second left right result after next observed[SIDE HELD]FIRST SECOND LENGTH BOUND OPERATION.
    destruct(gateway_memory_compare_operation _ _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ _ _
      SIDE FIRST SECOND LENGTH BOUND OPERATION)as[POST REST].
    split;[eapply gateway_native_roles_bootstrap_post;eassumption|exact REST].
  - intros before world destination destination_offset source source_offset bytes result after next observed
      [SIDE HELD]NATIVE POINTER PROTECTED DISJOINT BOUND OPERATION.
    destruct(gateway_memory_copy_operation _ _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ _ _ _
      SIDE NATIVE POINTER PROTECTED DISJOINT BOUND OPERATION)as[POST REST].
    split;[eapply gateway_native_roles_bootstrap_post;eassumption|exact REST].
  - intros before world pointer original destination result after next observed[SIDE HELD]STRING PROTECTED NATIVE POINTER SEPARATE OPERATION.
    destruct(gateway_canonical_path_operation _ _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ _
      SIDE STRING PROTECTED NATIVE POINTER SEPARATE OPERATION)as[POST REST].
    split;[eapply gateway_native_roles_bootstrap_post;eassumption|exact REST].
Qed.

Theorem gateway_interpreter_with_native_roles python objects current identifier
    (runtime:gateway_interpreter_runtime backend io native stable base python objects current identifier):
  gateway_interpreter_runtime backend io native stable side python objects current identifier.
Proof.
  assert(POST:forall before world after next observed,gateway_native_region_owned native protected before world ->
    gateway_interpreter_query_post io native stable base python objects current identifier before world after next observed ->
    gateway_interpreter_query_post io native stable side python objects current identifier before world after next observed).
  { intros before world after next observed HELD[RAW PYTHON OBJECTS HEAP CURRENT IDENTIFIER];constructor;try assumption.
    eapply gateway_native_roles_bootstrap_post;eassumption. }
  constructor.
  - intros before world after next[SIDE HELD]INTERFERENCE.
    eapply gateway_interpreter_ambient_identity;[exact runtime|exact SIDE|exact INTERFERENCE].
  - intros before world result after next observed[SIDE HELD]OPERATION.
    destruct(gateway_interpreter_get_operation _ _ _ _ _ _ _ _ _ runtime _ _ _ _ _ _ SIDE OPERATION)
      as[RESULT[POINTER RAW]].
    split;[exact RESULT|]. split;[exact POINTER|]. eapply POST;eassumption.
  - intros before world result after next observed[SIDE HELD]OPERATION.
    destruct(gateway_interpreter_id_operation _ _ _ _ _ _ _ _ _ runtime _ _ _ _ _ _ SIDE OPERATION)as[RESULT RAW].
    split;[exact RESULT|]. eapply POST;eassumption.
Qed.

Theorem gateway_bootstrap_profile_with_native_roles python objects
    (profile:gateway_bootstrap_python_profile native base python objects):
  gateway_bootstrap_python_profile native side python objects.
Proof.
  constructor.
  - intros memory world[SIDE HELD];eapply gateway_bootstrap_profile_ready;[exact profile|exact SIDE].
  - intros memory world object[SIDE HELD]NATIVE;eapply gateway_bootstrap_profile_native;[exact profile|exact SIDE|exact NATIVE].
Qed.

Lemma gateway_object_thread_native_roles_project heap_allocation mode before world after_mode after next:
  gateway_object_thread_operation backend native stable side heap_allocation mode before world after_mode after next ->
  gateway_object_thread_operation backend native stable base heap_allocation mode before world after_mode after next.
Proof.
  intro OPERATION;inversion OPERATION;subst;cbn[side gateway_native_region_discipline]in *.
  all:match goal with SIDE:side ?mode ?memory ?owner |- _=>
    change(base mode memory owner /\gateway_native_region_owned native protected memory owner)in SIDE;
    destruct SIDE as[SIDE HELD]end.
  all:eauto 5 using gateway_object_thread_save,gateway_object_thread_restore,gateway_object_thread_errno,
    gateway_object_thread_clock,gateway_object_thread_poll,gateway_object_thread_send,gateway_object_thread_receive,
    gateway_object_thread_signals,gateway_object_thread_volatile,gateway_object_thread_malloc,
    gateway_object_thread_free,gateway_object_thread_memchr.
Qed.

Theorem gateway_reference_threads_with_native_roles heap_allocation python objects
    (references:gateway_reference_thread_contract backend native stable base heap_allocation python objects):
  gateway_reference_thread_contract backend native stable side heap_allocation python objects.
Proof.
  constructor.
  - intros mode before world after next[SIDE HELD]INTERFERENCE.
    eapply gateway_reference_thread_ambient;[exact references|exact SIDE|exact INTERFERENCE].
  - intros mode before world after_mode after next OPERATION.
    eapply gateway_reference_thread_return;[exact references|].
    eapply gateway_object_thread_native_roles_project;exact OPERATION.
Qed.
End NativeRoles.
