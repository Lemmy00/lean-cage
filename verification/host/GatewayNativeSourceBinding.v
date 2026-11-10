(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: An actual source entry produces the pending native call key and operands. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayNativeImport GatewayNativeSpawnOperands
  GatewaySpawnABI GatewaySpawnCall GatewaySpawnActions GatewayExchangeEntry GatewayExchangePrepared GatewayExchangeScope.
Import ListNotations.
Open Scope Z_scope.
Module ND := GatewayNativeImport.

Record gateway_native_source_key := {
  gateway_source_process : nat;
  gateway_source_entry_position : nat;
  gateway_source_actions : block;
  gateway_source_attributes : block
}.

Record gateway_native_pending_spawn {World Event} (backend : gateway_backend World Event)
    (current_process native_position : World -> nat) builders genuine actions_view attributes_view
    (key : gateway_native_source_key) initial_memory initial_world events memory world
    (actual_arguments : list Values.val)
    (code : ND.LeanCage_Host_NativeCode_Operation) : Prop := {
  gateway_pending_spawn_source : exists arguments environment temporaries allocated blocks symbols continuation,
    function_entry2 (Clight.globalenv prog) f_host_exchange arguments initial_memory environment temporaries allocated /\
    actual_arguments = gateway_spawn_call_values blocks symbols (gateway_source_actions key) (gateway_source_attributes key) /\
    gateway_steps backend (Clight.globalenv prog)
      (gateway_live (State f_host_exchange (fn_body f_host_exchange) Kstop environment temporaries allocated) initial_world)
      events (gateway_live (Callstate (gateway_spawn_signature gateway_posix_spawn_api)
        actual_arguments
        continuation memory) world) /\
    environment ! _actions = Some (gateway_source_actions key, gateway_actions_type) /\
    environment ! _attributes = Some (gateway_source_attributes key, gateway_attributes_type) /\
    ~ Mem.valid_block initial_memory (gateway_source_actions key) /\
    ~ Mem.valid_block initial_memory (gateway_source_attributes key) /\
    gateway_source_actions key <> gateway_source_attributes key /\
    gateway_source_process key = current_process initial_world /\
    gateway_source_entry_position key = native_position initial_world /\
    gateway_native_spawn_operands builders genuine actions_view attributes_view memory world
      actual_arguments code
}.

(* The source scope producer supplies the actual function-entry/fresh-header
   facts. An SDK result, birth, exec and future source continuation are absent. *)
Theorem gateway_actual_pending_spawn_key {World Event} (backend : gateway_backend World Event)
    current_process native_position builders genuine actions_view attributes_view arguments environment temporaries
    initial_memory initial_world allocated events memory world blocks symbols actions attributes continuation code :
  function_entry2 (Clight.globalenv prog) f_host_exchange arguments initial_memory environment temporaries allocated ->
  gateway_steps backend (Clight.globalenv prog)
    (gateway_live (State f_host_exchange (fn_body f_host_exchange) Kstop environment temporaries allocated) initial_world)
    events (gateway_live (Callstate (gateway_spawn_signature gateway_posix_spawn_api)
      (gateway_spawn_call_values blocks symbols actions attributes) continuation memory) world) ->
  environment ! _actions = Some (actions, gateway_actions_type) ->
  environment ! _attributes = Some (attributes, gateway_attributes_type) ->
  ~ Mem.valid_block initial_memory actions -> ~ Mem.valid_block initial_memory attributes -> actions <> attributes ->
  gateway_native_spawn_operands builders genuine actions_view attributes_view memory world
    (gateway_spawn_call_values blocks symbols actions attributes) code ->
  gateway_native_pending_spawn backend current_process native_position builders genuine actions_view attributes_view
    {| gateway_source_process := current_process initial_world;
       gateway_source_entry_position := native_position initial_world;
       gateway_source_actions := actions; gateway_source_attributes := attributes |}
    initial_memory initial_world events memory world (gateway_spawn_call_values blocks symbols actions attributes) code.
Proof.
  intros ENTRY SOURCE ACTIONS ATTRIBUTES FRESH_ACTIONS FRESH_ATTRIBUTES DISTINCT OPERANDS.
  constructor; exists arguments, environment, temporaries, allocated, blocks, symbols, continuation.
  split; [exact ENTRY |]. split; [reflexivity |]. split; [exact SOURCE |]. split; [exact ACTIONS |].
  split; [exact ATTRIBUTES |]. split; [exact FRESH_ACTIONS |]. split; [exact FRESH_ATTRIBUTES |].
  split; [exact DISTINCT |]. split; [reflexivity |]. split; [reflexivity |exact OPERANDS].
Qed.
