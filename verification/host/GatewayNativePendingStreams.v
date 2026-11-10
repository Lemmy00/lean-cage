(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: A pending send is registered at
   its real call entry, before peer progress. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Clight.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewaySource GatewayMachine GatewaySpawnHistory GatewayRuntimeABI GatewayNativeImport
  GatewaySpawnABI GatewaySpawnResources GatewayNativeWords GatewayNativeRows GatewayNativeReferences GatewayNativeCallOperands
  GatewayChannelSourceScope GatewayNativeSourceBinding.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.
Module ND := GatewayNativeImport.

(* The observer names an actual SDK-internal row of this SAME arguments/memory/
   world invocation. It is available while the call is pending; no later SDK
   result, acknowledgement, send product or peer receive is an input. *)
Record gateway_pending_send_runtime {World} (process position : World -> nat)
    (resources : World -> gateway_resource_state)
    (pending : list Values.val -> mem -> World -> World -> nat -> ND.LeanCage_Host_NativeCode_CallRow -> Prop) : Prop := {
  gateway_pending_send_primitive : forall arguments memory world current selected row code,
    gateway_native_call_operands memory gateway_send_definition arguments code ->
    pending arguments memory world current selected row ->
    gateway_native_row_process row = Nat_of_nat (process world) /\
    gateway_native_row_operation row = code /\ (position world <= selected < position current)%nat /\
    gateway_native_leased_references (resources world) (gateway_native_row_input row)
}.

Record gateway_pending_send_source {World Event} (backend : gateway_backend World Event)
    (process position : World -> nat) (key : gateway_native_source_key)
    initial_memory initial_world events memory world arguments code : Prop := {
  gateway_pending_send_prefix : exists entry_arguments environment temporaries allocated continuation,
    function_entry2 (Clight.globalenv prog) f_host_exchange entry_arguments initial_memory
      environment temporaries allocated /\
    inhabited (gateway_channel_storage environment initial_memory allocated) /\
    gateway_steps backend (Clight.globalenv prog)
      (gateway_live (State f_host_exchange (fn_body f_host_exchange) Kstop environment temporaries allocated) initial_world)
      events (gateway_live (Callstate gateway_send_definition arguments continuation memory) world) /\
    environment ! _actions = Some (gateway_source_actions key, gateway_actions_type) /\
    environment ! _attributes = Some (gateway_source_attributes key, gateway_attributes_type) /\
    ~ Mem.valid_block initial_memory (gateway_source_actions key) /\
    ~ Mem.valid_block initial_memory (gateway_source_attributes key) /\
    gateway_source_actions key <> gateway_source_attributes key /\
    gateway_source_process key = process initial_world /\
    gateway_source_entry_position key = position initial_world /\
    gateway_native_call_operands memory gateway_send_definition arguments code
}.

Theorem gateway_actual_pending_send_source {World Event} (backend : gateway_backend World Event)
    process position entry_arguments environment temporaries initial_memory initial_world allocated
    events memory world continuation descriptor object offset amount payload :
  function_entry2 (Clight.globalenv prog) f_host_exchange entry_arguments initial_memory
    environment temporaries allocated ->
  gateway_steps backend (Clight.globalenv prog)
    (gateway_live (State f_host_exchange (fn_body f_host_exchange) Kstop environment temporaries allocated) initial_world)
    events (gateway_live (Callstate gateway_send_definition
      [Vint descriptor; Vptr object offset; Vlong (Int64.repr amount); Vint (Int.repr 16384)] continuation memory) world) ->
  0 < amount <= 65536 ->
  Mem.loadbytes memory object (Ptrofs.unsigned offset) amount = Some (inj_bytes payload) ->
  exists storage : gateway_channel_storage environment initial_memory allocated,
    gateway_pending_send_source backend process position
      {|gateway_source_process := process initial_world; gateway_source_entry_position := position initial_world;
        gateway_source_actions := gateway_channel_actions _ _ _ storage;
        gateway_source_attributes := gateway_channel_attributes _ _ _ storage|}
      initial_memory initial_world events memory world
      [Vint descriptor; Vptr object offset; Vlong (Int64.repr amount); Vint (Int.repr 16384)]
      (gateway_native_send_code descriptor payload (Int64.repr amount) (Int.repr 16384)).
Proof.
  intros ENTRY PREFIX AMOUNT BYTES.
  destruct (actual_exchange_channel_storage _ _ _ _ _ _ ENTRY) as [storage].
  exists storage; constructor.
  exists entry_arguments, environment, temporaries, allocated, continuation.
  split; [exact ENTRY |]. split; [constructor; exact storage |]. split; [exact PREFIX |].
  split; [exact (gateway_channel_actions_local _ _ _ storage) |].
  split; [exact (gateway_channel_attributes_local _ _ _ storage) |].
  split; [exact (gateway_channel_actions_fresh _ _ _ storage) |].
  split; [exact (gateway_channel_attributes_fresh _ _ _ storage) |].
  split; [exact (gateway_channel_actions_attributes _ _ _ storage) |].
  split; [reflexivity |]. split; [reflexivity |].
  apply gateway_native_send_operands.
  rewrite Int64.unsigned_repr; [exact BYTES |].
  change Int64.max_unsigned with 18446744073709551615; lia.
Qed.

Theorem gateway_actual_pending_send_row {World Event} (backend : gateway_backend World Event)
    process position builders genuine actions attributes rows resources pending
    (recording : gateway_native_row_runtime backend process position builders genuine actions attributes rows)
    (primitive : gateway_pending_send_runtime process position resources pending)
    key initial_memory initial_world events memory world arguments code current selected row :
  gateway_pending_send_source backend process position key initial_memory initial_world events memory world arguments code ->
  pending arguments memory world current selected row ->
  gateway_native_row_process row = Nat_of_nat (gateway_source_process key) /\
  gateway_native_row_operation row = code /\
  (gateway_source_entry_position key <= position world /\ position world <= selected < position current)%nat /\
  gateway_source_actions key <> gateway_source_attributes key /\
  gateway_native_leased_references (resources world) (gateway_native_row_input row).
Proof.
  intros [SOURCE] OBSERVED.
  destruct SOURCE as (entry_arguments & environment & temporaries & allocated & continuation &
    ENTRY & STORAGE & PREFIX & ACTIONS & ATTRIBUTES & FRESH_ACTIONS & FRESH_ATTRIBUTES & DISTINCT & PROCESS & POSITION & OPERANDS).
  destruct (gateway_native_run_actor backend process position builders genuine actions attributes rows recording
    (Clight.globalenv prog) _ _ _ PREFIX) as [SAME_PROCESS LATER].
  cbn [gateway_state_world] in SAME_PROCESS, LATER.
  destruct (@gateway_pending_send_primitive World process position resources pending primitive arguments memory world current selected row code OPERANDS OBSERVED)
    as [ACTOR [INPUT [ORDER LEASES]]].
  split; [rewrite ACTOR, PROCESS, SAME_PROCESS; reflexivity |].
  split; [exact INPUT |]. split; [split; [lia |exact ORDER] |].
  split; assumption.
Qed.
