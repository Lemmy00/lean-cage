(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Nonwriter primitives retain only this invocation's SDK shadow. *)
From Stdlib Require Import List ZArith.
From compcert Require Import AST Values Memory Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewayMachine GatewayRuntime GatewayRuntimeABI GatewaySpawnABI GatewaySpawnActions
  GatewayNativeRoots GatewayThreadRuntime.
Import ListNotations.

Definition gateway_builder_headers {World}(native_private:World->block->Prop)actions attributes memory world:Prop:=
  gateway_native_roots native_private[actions;attributes]memory world.

(* This is a single-operation registry law for the chosen private header
   lifetimes. It preserves neither SDK representation bytes nor genuine after
   arbitrary writes. Other invocations use different selected header lifetimes. *)
Record gateway_builder_history_runtime {World Event}(backend:gateway_backend World Event)
    (native_private:World->block->Prop)(builders:World->gateway_spawn_builders)actions attributes:Prop:={
  gateway_builder_history_ambient:forall before world after next,
    gateway_builder_headers native_private actions attributes before world->
    gateway_interference backend before world after next->builders next=builders world;
  gateway_builder_history_external:forall definition arguments before world result after next observed,
    gateway_builder_headers native_private actions attributes before world->~gateway_builder_mutation definition->
    gateway_runtime_operation backend definition arguments before world result after next observed->builders next=builders world;
  gateway_builder_history_volatile:forall before world pointer result after next observed,
    gateway_builder_headers native_private actions attributes before world->
    gateway_builtin backend(EF_vload Mint32)[tptr(tvolatile tint)][pointer]
      before world result after next observed->builders next=builders world
}.

Definition gateway_thread_resource_observer(definition:Ctypes.fundef Clight.function):Prop:=
  In definition[gateway_save_thread_definition;gateway_restore_thread_definition;gateway_errno_location_definition;
    gateway_clock_gettime_definition;gateway_poll_definition;gateway_send_definition;gateway_receive_definition;
    gateway_check_signals_definition].

Lemma gateway_thread_observer_no_sdk_write definition:
  gateway_thread_resource_observer definition->~gateway_builder_mutation definition.
Proof.
  intros MEMBER[api[WRITER DECLARATION]].
  rewrite actual_gateway_spawn_signatures in DECLARATION;injection DECLARATION as SAME.
  unfold gateway_thread_resource_observer in MEMBER.
  repeat destruct MEMBER as[EQUAL|MEMBER];try contradiction;subst definition;destruct api;discriminate SAME.
Qed.

Theorem gateway_thread_observer_keeps_builders {World Event}(backend:gateway_backend World Event)
    native_private builders actions attributes
    (runtime:gateway_builder_history_runtime backend native_private builders actions attributes)
    definition arguments before world result after next observed:
  gateway_builder_headers native_private actions attributes before world->
  gateway_thread_resource_observer definition->
  gateway_runtime_operation backend definition arguments before world result after next observed->builders next=builders world.
Proof.
  intros HEADERS OBSERVER OPERATION;eapply gateway_builder_history_external;
    [exact runtime|exact HEADERS|apply gateway_thread_observer_no_sdk_write;exact OBSERVER|exact OPERATION].
Qed.
