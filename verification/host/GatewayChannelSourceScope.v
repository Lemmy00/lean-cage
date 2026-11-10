(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Invocation identities come from the actual four fresh C allocations. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Maps AST Values Memory Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayExchangeEntry GatewaySpawnABI GatewayStackAllocation.
Import ListNotations.

Record gateway_channel_storage (environment : env) (before allocated : mem) : Type := {
  gateway_channel_data : block;
  gateway_channel_control : block;
  gateway_channel_actions : block;
  gateway_channel_attributes : block;
  gateway_channel_data_local : environment ! _pair = Some (gateway_channel_data, tarray tint 2);
  gateway_channel_control_local : environment ! _control = Some (gateway_channel_control, tarray tint 2);
  gateway_channel_actions_local : environment ! _actions = Some (gateway_channel_actions, gateway_actions_type);
  gateway_channel_attributes_local : environment ! _attributes = Some (gateway_channel_attributes, gateway_attributes_type);
  gateway_channel_data_control : gateway_channel_data <> gateway_channel_control;
  gateway_channel_data_actions : gateway_channel_data <> gateway_channel_actions;
  gateway_channel_data_attributes : gateway_channel_data <> gateway_channel_attributes;
  gateway_channel_control_actions : gateway_channel_control <> gateway_channel_actions;
  gateway_channel_control_attributes : gateway_channel_control <> gateway_channel_attributes;
  gateway_channel_actions_attributes : gateway_channel_actions <> gateway_channel_attributes;
  gateway_channel_data_fresh : ~ Mem.valid_block before gateway_channel_data;
  gateway_channel_control_fresh : ~ Mem.valid_block before gateway_channel_control;
  gateway_channel_actions_fresh : ~ Mem.valid_block before gateway_channel_actions;
  gateway_channel_attributes_fresh : ~ Mem.valid_block before gateway_channel_attributes
}.

Theorem actual_exchange_channel_storage ge arguments before environment temporaries allocated :
  function_entry2 ge f_host_exchange arguments before environment temporaries allocated ->
  inhabited (gateway_channel_storage environment before allocated).
Proof.
  intro ENTRY; inversion ENTRY; subst.
  match goal with ALLOC : alloc_variables _ _ _ _ _ _ |- _ =>
    pose proof (actual_exchange_allocations _ _ _ _ ALLOC) as STACK end.
  destruct STACK as [BUFFERS [[LIVE DISTINCT] FRAME]].
  destruct (BUFFERS _pair (tarray tint 2) ltac:(cbn; auto 12)) as (data & DATA & DATA_FRESH & DATA_RANGE).
  destruct (BUFFERS _control (tarray tint 2) ltac:(cbn; auto 12)) as (control & CONTROL & CONTROL_FRESH & CONTROL_RANGE).
  destruct (BUFFERS _actions gateway_actions_type ltac:(cbn; auto 12)) as (actions & ACTIONS & ACTIONS_FRESH & ACTIONS_RANGE).
  destruct (BUFFERS _attributes gateway_attributes_type ltac:(cbn; auto 12))
    as (attributes & ATTRIBUTES & ATTRIBUTES_FRESH & ATTRIBUTES_RANGE).
  constructor.
  refine {| gateway_channel_data := data; gateway_channel_control := control;
    gateway_channel_actions := actions; gateway_channel_attributes := attributes;
    gateway_channel_data_local := DATA; gateway_channel_control_local := CONTROL;
    gateway_channel_actions_local := ACTIONS; gateway_channel_attributes_local := ATTRIBUTES;
    gateway_channel_data_fresh := DATA_FRESH; gateway_channel_control_fresh := CONTROL_FRESH;
    gateway_channel_actions_fresh := ACTIONS_FRESH; gateway_channel_attributes_fresh := ATTRIBUTES_FRESH |}.
  all: eapply DISTINCT; eauto; discriminate.
Qed.

Inductive gateway_channel_pair_kind := gateway_channel_data_pair | gateway_channel_control_pair.

Definition gateway_channel_output {environment before allocated}
    (storage : gateway_channel_storage environment before allocated) kind : block :=
  match kind with
  | gateway_channel_data_pair => gateway_channel_data _ _ _ storage
  | gateway_channel_control_pair => gateway_channel_control _ _ _ storage
  end.

Theorem actual_channel_output_local environment before allocated
    (storage : gateway_channel_storage environment before allocated) kind :
  environment ! (match kind with gateway_channel_data_pair => _pair | gateway_channel_control_pair => _control end) =
    Some (gateway_channel_output storage kind, tarray tint 2).
Proof. destruct kind; [apply gateway_channel_data_local | apply gateway_channel_control_local]. Qed.
