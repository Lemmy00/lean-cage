(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Pair/flag primitives retain the same invocation's SDK shadow. *)
From Stdlib Require Import ZArith List.
From compcert Require Import AST Values Memory Ctypes Clight.
From HostGateway Require Import GatewayMachine GatewayRuntime GatewaySpawnABI GatewaySpawnActions
  GatewaySpawnResources GatewaySpawnRuntime GatewayBuilderHistory GatewayBuilderThreads.
Import ListNotations.

Lemma gateway_descriptor_api_no_sdk_write api:
  In api[gateway_socketpair_api;gateway_fcntl_api;gateway_close_api]->
  ~gateway_builder_mutation(gateway_spawn_signature api).
Proof.
  intros MEMBER[writer[WRITER DECLARATION]].
  rewrite actual_gateway_spawn_signatures in DECLARATION;injection DECLARATION as SAME.
  destruct writer;try solve[cbn in WRITER;intuition discriminate].
  all:repeat destruct MEMBER as[EQUAL|MEMBER];try contradiction;subst api;discriminate SAME.
Qed.

Theorem gateway_descriptor_keeps_builders {World Event}(backend:gateway_backend World Event)
    native builders actions attributes(history:gateway_builder_history_runtime backend native builders actions attributes)
    api arguments before world result after next observed:
  gateway_builder_headers native actions attributes before world->
  In api[gateway_socketpair_api;gateway_fcntl_api;gateway_close_api]->
  gateway_spawn_operation backend api arguments before world result after next observed->builders next=builders world.
Proof.
  intros HEADERS OBSERVER[definition[DECLARATION OPERATION]].
  rewrite actual_gateway_spawn_signatures in DECLARATION;injection DECLARATION as SAME;subst definition.
  eapply gateway_builder_history_external;
    [exact history|exact HEADERS|apply gateway_descriptor_api_no_sdk_write;exact OBSERVER|exact OPERATION].
Qed.

Section BuilderDescriptors.
Context {World Event}(backend:gateway_backend World Event)io native stable base resources ipc
    (runtime:gateway_spawn_descriptor_runtime backend io native stable base resources ipc)
    builders(actions attributes:block)(history:gateway_builder_history_runtime backend native builders actions attributes).
Hypothesis HEADERS:forall mode memory world,base mode memory world->
  gateway_builder_headers native actions attributes memory world.

Ltac retain_descriptor_shadow:=
  match goal with
  |SNAPSHOT:builders ?old = ?snapshot,
   SIDE:base None ?before ?old,
   OPERATION:gateway_spawn_operation backend ?api ?arguments ?before ?old ?returned ?after ?next ?observed
   |-builders ?next = ?snapshot=>
    rewrite(gateway_descriptor_keeps_builders backend native builders actions attributes history
      api arguments before old returned after next observed(HEADERS None before old SIDE)
      ltac:(cbn;auto 5)OPERATION);exact SNAPSHOT
  |SNAPSHOT:builders ?old = ?snapshot,
   SIDE:base None ?before ?old,
   INTERFERENCE:gateway_interference backend ?before ?old ?after ?next
   |-builders ?next = ?snapshot=>
    rewrite(gateway_builder_history_ambient _ _ _ _ _ history before old after next
      (HEADERS None before old SIDE)INTERFERENCE);exact SNAPSHOT
  end.

Theorem gateway_descriptors_with_builder_history snapshot:
  gateway_spawn_descriptor_runtime backend io native stable
    (gateway_builder_thread_discipline base builders snapshot)resources ipc.
Proof.
  constructor.
  - intros before world after next[SIDE SNAPSHOT]VALID INTERFERENCE.
    eapply gateway_spawn_ambient;[exact runtime|exact SIDE|exact VALID|exact INTERFERENCE].
  - intros before world object offset result after next observed[SIDE SNAPSHOT]VALID PRIVATE POINTER OPERATION.
    destruct(gateway_socketpair_operation _ _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ SIDE VALID PRIVATE POINTER OPERATION)
      as(AFTER&STATE&ACCESS&PERMISSIONS&FRAME&EXCLUSIVE&IO&RESULT).
    split;[split;[exact AFTER|retain_descriptor_shadow]|].
    split;[exact STATE|]. split;[exact ACCESS|]. split;[exact PERMISSIONS|]. split;[exact FRAME|].
    split;[exact EXCLUSIVE|]. split;assumption.
  - intros before world source minimum entry result after next observed[SIDE SNAPSHOT]VALID OWNED BOUND OPERATION.
    destruct(gateway_duplicate_operation _ _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ _ SIDE VALID OWNED BOUND OPERATION)
      as(AFTER&STATE&ACCESS&FRAME&EXCLUSIVE&IO&RESULT).
    split;[split;[exact AFTER|retain_descriptor_shadow]|].
    split;[exact STATE|]. split;[exact ACCESS|]. split;[exact FRAME|]. split;[exact EXCLUSIVE|]. split;assumption.
  - intros before world source entry result after next observed[SIDE SNAPSHOT]VALID OWNED EXCLUSIVE OPERATION.
    destruct(gateway_get_flags_operation _ _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ SIDE VALID OWNED EXCLUSIVE OPERATION)
      as(AFTER&STATE&ACCESS&FRAME&REFERENCE&STATUS&KEPT&IO&RESULT).
    split;[split;[exact AFTER|retain_descriptor_shadow]|].
    split;[exact STATE|]. split;[exact ACCESS|]. split;[exact FRAME|]. split;[exact REFERENCE|].
    split;[exact STATUS|]. split;[exact KEPT|]. split;assumption.
  - intros before world source entry flags result after next observed[SIDE SNAPSHOT]VALID OWNED EXCLUSIVE OPERATION.
    destruct(gateway_set_flags_operation _ _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ _ SIDE VALID OWNED EXCLUSIVE OPERATION)
      as(AFTER&STATE&ACCESS&FRAME&REFERENCE&STATUS&KEPT&IO&RESULT).
    split;[split;[exact AFTER|retain_descriptor_shadow]|].
    split;[exact STATE|]. split;[exact ACCESS|]. split;[exact FRAME|]. split;[exact REFERENCE|].
    split;[exact STATUS|]. split;[exact KEPT|]. split;assumption.
  - intros before world source entry result after next observed[SIDE SNAPSHOT]VALID OWNED OPERATION.
    destruct(gateway_close_operation _ _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _ SIDE VALID OWNED OPERATION)
      as(RESULT&AFTER&STATE&ACCESS&FRAME&REMOVED&REFERENCE&STATUS&KEPT&IO).
    split;[exact RESULT|]. split;[split;[exact AFTER|retain_descriptor_shadow]|].
    split;[exact STATE|]. split;[exact ACCESS|]. split;[exact FRAME|]. split;[exact REMOVED|].
    split;[exact REFERENCE|]. split;[exact STATUS|]. split;assumption.
Qed.
End BuilderDescriptors.
