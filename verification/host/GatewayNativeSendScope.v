(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: A data send belongs to its nearest real exchange caller. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Maps Integers AST Values Memory Clight.
Require Import CallContexts.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewaySpawnABI GatewayNativeSourceBinding
  GatewayNativePendingStreams GatewayNativeRows GatewayNativeReferences GatewaySpawnResources
  GatewayChannelSourceScope GatewaySendOperation GatewayHeaderTransfer GatewayPayloadReturn.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

(* These are the two actual direct host_transfer calls in host_exchange.
   Reentrant requests have another nearest saved exchange environment; an
   arbitrary ancestor prefix must not relabel their sends as this invocation. *)
Inductive gateway_request_send_scope (environment : env) : cont -> Prop :=
| gateway_request_header_send : forall temporaries amount saved descriptor caller_temporaries,
    gateway_request_send_scope environment
      (plug_cont (send_transfer_cont temporaries amount saved descriptor)
        (header_transfer_cont environment caller_temporaries))
| gateway_request_payload_send : forall temporaries amount saved descriptor caller_temporaries,
    gateway_request_send_scope environment
      (plug_cont (send_transfer_cont temporaries amount saved descriptor)
        (payload_transfer_cont environment caller_temporaries)).

Record gateway_pending_request_send {World Event} (backend : gateway_backend World Event)
    process position key initial_memory initial_world events memory world arguments code : Prop := {
  gateway_request_send_source : gateway_pending_send_source backend process position key
    initial_memory initial_world events memory world arguments code;
  gateway_request_send_caller : exists entry_arguments environment temporaries allocated continuation,
    function_entry2 (Clight.globalenv prog) f_host_exchange entry_arguments initial_memory
      environment temporaries allocated /\
    environment ! _actions = Some (gateway_source_actions key, gateway_actions_type) /\
    environment ! _attributes = Some (gateway_source_attributes key, gateway_attributes_type) /\
    gateway_steps backend (Clight.globalenv prog)
      (gateway_live (State f_host_exchange (fn_body f_host_exchange) Kstop environment temporaries allocated) initial_world)
      events (gateway_live (Callstate GatewayRuntimeABI.gateway_send_definition arguments continuation memory) world) /\
    gateway_request_send_scope environment continuation
}.

Theorem gateway_actual_pending_request_send {World Event} (backend : gateway_backend World Event)
    process position entry_arguments environment temporaries initial_memory initial_world allocated
    events memory world continuation descriptor object offset amount payload :
  function_entry2 (Clight.globalenv prog) f_host_exchange entry_arguments initial_memory
    environment temporaries allocated ->
  gateway_steps backend (Clight.globalenv prog)
    (gateway_live (State f_host_exchange (fn_body f_host_exchange) Kstop environment temporaries allocated) initial_world)
    events (gateway_live (Callstate GatewayRuntimeABI.gateway_send_definition
      [Vint descriptor; Vptr object offset; Vlong (Int64.repr amount); Vint (Int.repr 16384)] continuation memory) world) ->
  gateway_request_send_scope environment continuation ->
  0 < amount <= 65536 ->
  Mem.loadbytes memory object (Ptrofs.unsigned offset) amount = Some (inj_bytes payload) ->
  exists storage : gateway_channel_storage environment initial_memory allocated,
    gateway_pending_request_send backend process position
      {|gateway_source_process := process initial_world; gateway_source_entry_position := position initial_world;
        gateway_source_actions := gateway_channel_actions _ _ _ storage;
        gateway_source_attributes := gateway_channel_attributes _ _ _ storage|}
      initial_memory initial_world events memory world
      [Vint descriptor; Vptr object offset; Vlong (Int64.repr amount); Vint (Int.repr 16384)]
      (GatewayNativeCallOperands.gateway_native_send_code descriptor payload (Int64.repr amount) (Int.repr 16384)).
Proof.
  intros ENTRY PREFIX SCOPE AMOUNT BYTES.
  destruct (gateway_actual_pending_send_source backend process position entry_arguments environment temporaries
    initial_memory initial_world allocated events memory world continuation descriptor object offset amount payload
    ENTRY PREFIX AMOUNT BYTES) as [storage SOURCE].
  exists storage; constructor; [exact SOURCE |].
  exists entry_arguments, environment, temporaries, allocated, continuation.
  split; [exact ENTRY |]. split; [exact (gateway_channel_actions_local _ _ _ storage) |].
  split; [exact (gateway_channel_attributes_local _ _ _ storage) |]. split; assumption.
Qed.

Theorem gateway_actual_pending_request_row {World Event} (backend : gateway_backend World Event)
    process position builders genuine actions attributes rows resources pending
    (recording : gateway_native_row_runtime backend process position builders genuine actions attributes rows)
    (primitive : gateway_pending_send_runtime process position resources pending)
    key initial_memory initial_world events memory world arguments code current selected row :
  gateway_pending_request_send backend process position key initial_memory initial_world events memory world arguments code ->
  pending arguments memory world current selected row ->
  gateway_native_row_process row = Lean.Nat_of_nat (gateway_source_process key) /\
  gateway_native_row_operation row = code /\
  (gateway_source_entry_position key <= position world /\ position world <= selected < position current)%nat /\
  gateway_source_actions key <> gateway_source_attributes key /\
  gateway_native_leased_references (resources world) (gateway_native_row_input row).
Proof.
  intros [SOURCE SCOPE] OBSERVED.
  eapply gateway_actual_pending_send_row; [exact recording |exact primitive |exact SOURCE |exact OBSERVED].
Qed.
