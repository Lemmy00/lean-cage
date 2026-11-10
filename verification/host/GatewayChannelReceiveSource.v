(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: The actual original C prefix and
   current source lease bind each receive to its shared invocation data. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import AST Values Memory Integers Clight.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewaySource GatewayMachine GatewayRuntime GatewayRuntimeABI GatewayStreamInterface
  GatewayThreadRuntime GatewayChannelSourceScope GatewayChannelCodeProducer GatewayChannelReceiveCode
  GatewaySpawnResources GatewayNativeImport GatewayNativeWords GatewayNativeRows GatewayNativeReferences
  GatewayNativeStreamObservation GatewayNativeCallOperands GatewaySpawnHistory.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.
Module ND := GatewayNativeImport.

(* No original-read or exclusive-reader role is supplied by an SDK. The
   caller must produce this current held FD from its actual pair/stream source
   context; the primitive binds only that actual operation's full row. *)
Theorem gateway_actual_source_receive_row {World Event} (backend : gateway_backend World Event)
    io native stable discipline thread_errno process position builders genuine actions attributes resources rows
    (thread : gateway_thread_runtime backend io native stable discipline thread_errno)
    (recording : gateway_native_row_runtime backend process position builders genuine actions attributes rows)
    (observation : gateway_native_stream_runtime backend io rows)
    (references : gateway_native_reference_runtime backend resources rows)
    entry_arguments environment temporaries before initial allocated source_events memory world
    continuation saved descriptor object offset amount result after next event
    (entry : gateway_resource_descriptor) :
  function_entry2 (Clight.globalenv prog) f_host_exchange entry_arguments before environment temporaries allocated ->
  gateway_steps backend (Clight.globalenv prog)
    (gateway_live (State f_host_exchange (fn_body f_host_exchange) Kstop environment temporaries allocated) initial)
    source_events
    (gateway_live (Callstate gateway_receive_definition
      [Vint descriptor; Vptr object offset; Vlong (Int64.repr amount); Vint Int.zero] continuation memory) world) ->
  discipline (Some saved) memory world -> native world object -> 0 < amount <= 65536 ->
  gateway_native_pointer memory object offset amount Writable ->
  gateway_owned_descriptor (resources world) (Int.signed descriptor) entry ->
  gateway_runtime_operation backend gateway_receive_definition
    [Vint descriptor; Vptr object offset; Vlong (Int64.repr amount); Vint Int.zero]
    memory world result after next event ->
  exists (storage : gateway_channel_storage environment before allocated) selected row bytes use,
    rows world event = Some (selected, row) /\
    (position initial <= selected < position next)%nat /\
    ND.LeanCage_Host_ChannelCode_ReceiveUse_invocation use =
      gateway_channel_invocation _ _ _ storage (process initial) (position initial) /\
    ND.LeanCage_Host_ChannelCode_ReceiveUse_position use = Nat_of_nat selected /\
    ND.LeanCage_Host_ChannelCode_ReceiveUse_row use = row /\
    ND.LeanCage_Host_ChannelCode_ReceiveUse_bytes use = gateway_native_bytes bytes /\
    gateway_channel_receive_checked use /\
    gateway_native_stream_product row ND.LeanCage_Host_NativeCode_Product_received bytes.
Proof.
  intros ENTRY PREFIX SIDE PRIVATE AMOUNT OUTPUT HELD OPERATION.
  destruct (actual_exchange_channel_storage _ _ _ _ _ _ ENTRY) as [storage].
  destruct (gateway_actual_receive_native_row backend io native stable discipline thread_errno process position
    builders genuine actions attributes rows thread recording observation saved memory world descriptor object offset amount
    result after next event SIDE PRIVATE AMOUNT OUTPUT OPERATION)
    as (selected & row & count & bytes & ROW & PROCESS & CODE & ORDER & PRODUCT & RESULT & COUNT & BYTES & IO & REST).
  pose proof (@gateway_native_source_leases World Event backend resources rows references gateway_receive_definition
    [Vint descriptor; Vptr object offset; Vlong (Int64.repr amount); Vint Int.zero]
    memory world result after next event selected row OPERATION ROW (Int.signed descriptor) entry HELD) as INPUT.
  destruct (gateway_native_run_actor backend process position builders genuine actions attributes rows recording
    (Clight.globalenv prog) _ _ _ PREFIX) as [SAME_PROCESS LATER].
  cbn [gateway_state_world] in SAME_PROCESS, LATER.
  rewrite SAME_PROCESS in PROCESS.
  exists storage, selected, row, bytes,
    (gateway_channel_receive_use _ _ _ storage (process initial) (position initial) selected row descriptor amount entry bytes).
  split; [exact ROW |]. split; [lia |]. split; [reflexivity |]. split; [reflexivity |].
  split; [reflexivity |]. split; [reflexivity |]. split; [|exact PRODUCT].
  constructor; apply gateway_channel_receive_use_consistent; try assumption; [lia |exact (proj1 INPUT)].
Qed.
