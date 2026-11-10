(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: A complete actual pair helper retains its same-row kernel origin. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewaySource GatewayMachine GatewayStreamInterface GatewayThreadRuntime
  GatewaySpawnABI GatewaySpawnResources GatewaySpawnRuntime GatewayPairContext GatewayPairInputs GatewayPairHistory GatewayPairBuffers
  GatewayPairSource GatewayPairKernelOrigin GatewayNativeImport GatewayNativeWords GatewayNativeRows GatewayNativeReferences
  GatewayNativeStreamObservation GatewayNativePairObservation GatewaySpawnHistory.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.
Module ND := GatewayNativeImport.

Theorem actual_private_pair_native_origin {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
    native_private stable_readonly discipline thread_errno resources ipc
    (runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno)
    (descriptors:gateway_spawn_descriptor_runtime backend io native_private stable_readonly discipline resources ipc)
    process position builders genuine actions attributes rows
    (recording:gateway_native_row_runtime backend process position builders genuine actions attributes rows)
    (observation:gateway_native_pair_runtime backend resources ipc rows)
    object offset(history:mem->World->Prop)
    (buffers:gateway_pair_buffer_laws backend native_private stable_readonly discipline object offset history)
    before world events after next:
  gateway_pair_input native_private discipline resources object offset before world->
  history before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_private_pair)[Vptr object offset]Kstop before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next)->
  exists prefix suffix called call_world born born_world observed
    (receipt:gateway_socketpair_receipt ipc(resources call_world)(resources born_world)) selected row,
    events=prefix++gateway_primitive observed::suffix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(Internal f_host_private_pair)[Vptr object offset]Kstop before)world)prefix
      (gateway_live(Callstate(gateway_spawn_signature gateway_socketpair_api)(pair_socket_arguments object offset)
        (pair_socket_cont(Vptr object offset))called)call_world) /\
    gateway_spawn_operation backend gateway_socketpair_api(pair_socket_arguments object offset)
      called call_world(Vint Int.zero)born born_world observed /\
    Mem.load Mint32 born object(Ptrofs.unsigned offset)=
      Some(Vint(Int.repr(gateway_pair_left _ _ _ receipt))) /\
    Mem.load Mint32 born object(Ptrofs.unsigned offset+4)=
      Some(Vint(Int.repr(gateway_pair_right _ _ _ receipt))) /\
    rows call_world observed=Some(selected,row) /\
    gateway_native_row_process row=Nat_of_nat(process world) /\
    gateway_native_row_operation row=gateway_native_pair_code /\
    (position world<=selected<position next)%nat /\
    gateway_native_row_product row=ND.LeanCage_Host_NativeCode_Product_socketPair
      (gateway_native_int(Int.repr(gateway_pair_left _ _ _ receipt)))
      (gateway_native_int(Int.repr(gateway_pair_right _ _ _ receipt))) /\
    gateway_native_lease_at(gateway_native_row_output row)(gateway_pair_left _ _ _ receipt)
      (gateway_socket_descriptor(gateway_pair_left_object _ _ _ receipt)(gateway_pair_left_description _ _ _ receipt)) /\
    gateway_native_lease_at(gateway_native_row_output row)(gateway_pair_right _ _ _ receipt)
      (gateway_socket_descriptor(gateway_pair_right_object _ _ _ receipt)(gateway_pair_right_description _ _ _ receipt)) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate(Vint Int.zero)(pair_socket_cont(Vptr object offset))born)born_world)suffix
      (gateway_live(Returnstate(Vint Int.zero)Kstop after)next) /\
    gateway_pair_input native_private discipline resources object offset called call_world /\
    gateway_resource_reference(resources world)(resources call_world) /\
    gateway_resource_reference(resources world)(resources next) /\
    exists left right,4<=left /\4<=right /\
      gateway_pair_full_context native_private discipline resources ipc
        (gateway_pair_receipt_identity ipc(resources call_world)(resources born_world)receipt)
        object offset left right history after next.
Proof.
  intros INITIAL HISTORY RUN.
  destruct(actual_private_pair_with_kernel_origin_history backend io native_private stable_readonly discipline
    thread_errno resources ipc runtime descriptors object offset history buffers before world events after next
    INITIAL HISTORY RUN)
    as(prefix&suffix&called&call_world&born&born_world&observed&receipt&EVENTS&PREFIX&OPERATION&
      LEFT_LOAD&RIGHT_LOAD&SUFFIX&INPUT&ORIGIN&FINAL_REFERENCE&FINAL).
  destruct(gateway_actual_socket_pair_native_row backend process position builders genuine actions attributes
    resources ipc rows recording observation object offset called call_world born born_world observed receipt
    OPERATION LEFT_LOAD RIGHT_LOAD)
    as(selected&row&ROW&PROCESS&CODE&ORDER&PRODUCT&FIRST&SECOND).
  destruct(gateway_native_run_actor backend process position builders genuine actions attributes rows recording
    (Clight.globalenv prog)_ _ _ PREFIX)as[PREFIX_PROCESS PREFIX_POSITION].
  destruct(gateway_native_run_actor backend process position builders genuine actions attributes rows recording
    (Clight.globalenv prog)_ _ _ SUFFIX)as[SUFFIX_PROCESS SUFFIX_POSITION].
  cbn[gateway_state_world]in PREFIX_PROCESS,PREFIX_POSITION,SUFFIX_PROCESS,SUFFIX_POSITION.
  rewrite PREFIX_PROCESS in PROCESS.
  exists prefix,suffix,called,call_world,born,born_world,observed,receipt,selected,row.
  split;[exact EVENTS|]. split;[exact PREFIX|]. split;[exact OPERATION|].
  split;[exact LEFT_LOAD|]. split;[exact RIGHT_LOAD|]. split;[exact ROW|]. split;[exact PROCESS|].
  split;[exact CODE|]. split;[lia|]. split;[exact PRODUCT|]. split;[exact FIRST|]. split;[exact SECOND|].
  split;[exact SUFFIX|]. split;[exact INPUT|]. split;[exact ORIGIN|]. split;[exact FINAL_REFERENCE|exact FINAL].
Qed.
