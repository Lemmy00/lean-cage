(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Individual initializer SDK calls create or transfer references. *)
From Stdlib Require Import ZArith List String.
From compcert Require Import Coqlib Integers AST Values Memory Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayRuntime GatewayInitializerObjectsSource
  GatewayInitializerObjectBindings GatewayPython GatewayObjects GatewayReferenceRuntime GatewayErrorRuntime.
Import ListNotations.
Local Open Scope string_scope.

Definition gateway_initializer_new_reference {World}
    (python : World -> python_world) (objects : World -> gateway_object_heap)
    (normal attached : mem -> World -> Prop) (before : mem) world result after next : Prop :=
  attached after next /\
  ((result = Vnullptr /\ (forall pointer,
      python_native_strong (python next) pointer = python_native_strong (python world) pointer)) \/
    normal after next /\ gateway_reference_credit (python world) (python next) result /\
    gateway_rooted (python next) (objects next) result).

Definition gateway_initializer_reference_debit (before after : python_world) pointer : Prop :=
  python_native_strong before pointer = S (python_native_strong after pointer) /\
  (forall other, other <> pointer -> python_native_strong after other = python_native_strong before other).

(* Module/attribute values can alias cached, immortal or externally mutable objects.
   No result is declared fresh or private. These laws contain no C-global frame,
   callback outcome, persistent class-global fact or initializer-success premise. *)
Record gateway_initializer_sdk {World Event} (backend : gateway_backend World Event)
    (python : World -> python_world) (objects : World -> gateway_object_heap)
    (normal attached : mem -> World -> Prop)
    (module_descriptor : mem -> World -> Values.val -> Prop)
    (exported : World -> Values.val -> list Byte.int -> Values.val -> Prop) : Prop := {
  gateway_initializer_import_effect : forall before world name bytes result after next observed,
    normal before world -> gateway_error_cstring before name bytes ->
    gateway_runtime_operation backend initializer_import_definition [name] before world result after next observed ->
    gateway_initializer_new_reference python objects normal attached before world result after next;
  gateway_initializer_attribute_effect : forall before world object name bytes result after next observed,
    normal before world -> gateway_rooted (python world) (objects world) object ->
    gateway_error_cstring before name bytes ->
    gateway_runtime_operation backend initializer_attribute_definition [object; name]
      before world result after next observed ->
    gateway_initializer_new_reference python objects normal attached before world result after next;
  gateway_initializer_module_effect : forall before world descriptor result after next observed,
    normal before world -> module_descriptor before world descriptor ->
    gateway_runtime_operation backend initializer_module_definition [descriptor; Vint (Int.repr 3)]
      before world result after next observed ->
    gateway_initializer_new_reference python objects normal attached before world result after next;
  gateway_initializer_add_effect : forall before world module name bytes object result after next observed,
    normal before world -> gateway_rooted (python world) (objects world) module ->
    gateway_rooted (python world) (objects world) object -> gateway_error_cstring before name bytes ->
    gateway_runtime_operation backend initializer_add_definition [module; name; object]
      before world result after next observed ->
    attached after next /\ exists status,
      result = Vint status /\
      (status = Int.zero -> normal after next /\
        gateway_initializer_reference_debit (python world) (python next) object /\ exported next module bytes object) /\
      (status <> Int.zero -> forall pointer,
        python_native_strong (python next) pointer = python_native_strong (python world) pointer);
  gateway_initializer_add_ref_effect : forall before world module name bytes object result after next observed,
    normal before world -> gateway_rooted (python world) (objects world) module ->
    gateway_rooted (python world) (objects world) object -> gateway_error_cstring before name bytes ->
    gateway_runtime_operation backend initializer_add_ref_definition [module; name; object]
      before world result after next observed ->
    attached after next /\ (forall pointer,
      python_native_strong (python next) pointer = python_native_strong (python world) pointer) /\
    exists status, result = Vint status /\
      (status = Int.zero -> normal after next /\ exported next module bytes object)
}.
