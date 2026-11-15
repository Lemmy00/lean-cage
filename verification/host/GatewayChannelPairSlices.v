(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: The actual copyout source slice
   supplies the same shared pair use and source invocation. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPairCopyout GatewayChannelSourceScope
  GatewayChannelCodeProducer GatewayChannelPairSource GatewayNativeImport GatewayNativeRows GatewayNativePairObservation
  GatewayNativeReferences GatewayNativeWords GatewaySpawnHistory GatewaySpawnResources GatewaySpawnABI GatewayPairSource
  GatewayPairContext.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.
Module ND := GatewayNativeImport.

Theorem gateway_pair_slice_native_use {World Event} (backend : gateway_backend World Event)
    process position builders genuine actions attributes resources ipc rows
    (recording : gateway_native_row_runtime backend process position builders genuine actions attributes rows)
    (observation : gateway_native_pair_runtime backend resources ipc rows)
    entry_arguments environment temporaries initial_memory initial_world allocated
    (storage : gateway_channel_storage environment initial_memory allocated)
    kind object events target next identity ordinal :
  function_entry2 (Clight.globalenv prog) f_host_exchange entry_arguments initial_memory environment temporaries allocated ->
  gateway_channel_output storage kind = object ->
  gateway_copyout_pair_slice backend resources ipc object
    (State f_host_exchange (fn_body f_host_exchange) Kstop environment temporaries allocated) initial_world
    events target next identity ordinal ->
  exists prefix suffix continuation called call_world born born_world observed
    (receipt : gateway_socketpair_receipt ipc (resources call_world) (resources born_world)) selected row,
    identity = gateway_pair_receipt_identity ipc (resources call_world) (resources born_world) receipt /\
    length prefix = ordinal /\ events = prefix ++ gateway_primitive observed :: suffix /\
    gateway_steps backend (Clight.globalenv prog)
      (gateway_live (State f_host_exchange (fn_body f_host_exchange) Kstop environment temporaries allocated) initial_world)
      prefix (gateway_live (Callstate (gateway_spawn_signature gateway_socketpair_api)
        (pair_socket_arguments object Ptrofs.zero) continuation called) call_world) /\
    gateway_steps backend (Clight.globalenv prog)
      (gateway_live (Returnstate (Vint Int.zero) continuation born) born_world) suffix (gateway_live target next) /\
    gateway_channel_pending_pair backend process position
      (gateway_channel_invocation _ _ _ storage (process initial_world) (position initial_world)) kind
      initial_memory initial_world prefix called call_world (pair_socket_arguments object Ptrofs.zero) /\
    gateway_spawn_operation backend gateway_socketpair_api (pair_socket_arguments object Ptrofs.zero)
      called call_world (Vint Int.zero) born born_world observed /\
    Mem.load Mint32 born object 0 = Some (Vint (Int.repr (gateway_pair_left _ _ _ receipt))) /\
    Mem.load Mint32 born object 4 = Some (Vint (Int.repr (gateway_pair_right _ _ _ receipt))) /\
    rows call_world observed = Some (selected, row) /\
    (position initial_world <= selected < position next)%nat /\
    gateway_channel_pair_checked
      (gateway_channel_pair_use _ _ _ storage (process initial_world) (position initial_world) kind selected row
        ipc (resources call_world) (resources born_world) receipt).
Proof.
  intros ENTRY OUTPUT (prefix & suffix & continuation & called & call_world & born & born_world & observed & receipt &
    IDENTITY & INDEX & EVENTS & PREFIX & OPERATION & LEFT & RIGHT & SUFFIX).
  destruct (gateway_actual_socket_pair_native_row backend process position builders genuine actions attributes resources ipc rows
    recording observation object Ptrofs.zero called call_world born born_world observed receipt OPERATION LEFT RIGHT)
    as (selected & row & ROW & PROCESS & CODE & ORDER & PRODUCT & FIRST & SECOND).
  destruct (gateway_native_run_actor backend process position builders genuine actions attributes rows recording
    (Clight.globalenv prog) _ _ _ PREFIX) as [PREFIX_PROCESS PREFIX_POSITION].
  destruct (gateway_native_run_actor backend process position builders genuine actions attributes rows recording
    (Clight.globalenv prog) _ _ _ SUFFIX) as [SUFFIX_PROCESS SUFFIX_POSITION].
  cbn [gateway_state_world] in PREFIX_PROCESS, PREFIX_POSITION, SUFFIX_POSITION.
  rewrite PREFIX_PROCESS in PROCESS.
  exists prefix, suffix, continuation, called, call_world, born, born_world, observed, receipt, selected, row.
  split; [exact IDENTITY |]. split; [exact INDEX |]. split; [exact EVENTS |].
  split; [exact PREFIX |]. split; [exact SUFFIX |]. split.
  - constructor; exists entry_arguments, environment, temporaries, allocated, storage, continuation.
    split; [exact ENTRY |]. split; [reflexivity |]. split; [rewrite OUTPUT; reflexivity |exact PREFIX].
  - split; [exact OPERATION |]. split; [exact LEFT |]. split; [exact RIGHT |]. split; [exact ROW |].
    split; [lia |]. constructor; apply gateway_channel_pair_use_consistent; try assumption; lia.
Qed.

Theorem gateway_ordered_pair_slices_native_uses {World Event} (backend : gateway_backend World Event)
    process position builders genuine actions attributes resources ipc rows
    (recording : gateway_native_row_runtime backend process position builders genuine actions attributes rows)
    (observation : gateway_native_pair_runtime backend resources ipc rows)
    entry_arguments environment temporaries initial_memory initial_world allocated
    (storage : gateway_channel_storage environment initial_memory allocated)
    data control events target next data_identity control_identity :
  function_entry2 (Clight.globalenv prog) f_host_exchange entry_arguments initial_memory environment temporaries allocated ->
  gateway_channel_data _ _ _ storage = data -> gateway_channel_control _ _ _ storage = control ->
  gateway_copyout_pairs_slice_ordered backend resources ipc data control
    (State f_host_exchange (fn_body f_host_exchange) Kstop environment temporaries allocated) initial_world
    events target next data_identity control_identity ->
  exists data_use control_use data_position control_position data_prefix control_prefix data_memory control_memory
    data_world control_world data_event control_event,
    ND.LeanCage_Host_ChannelCode_PairUse_invocation data_use =
      gateway_channel_invocation _ _ _ storage (process initial_world) (position initial_world) /\
    ND.LeanCage_Host_ChannelCode_PairUse_invocation control_use =
      gateway_channel_invocation _ _ _ storage (process initial_world) (position initial_world) /\
    gateway_channel_pair_kind_of data_use = gateway_channel_kind gateway_channel_data_pair /\
    gateway_channel_pair_kind_of control_use = gateway_channel_kind gateway_channel_control_pair /\
    ND.LeanCage_Host_ChannelCode_PairUse_position data_use = Nat_of_nat data_position /\
    ND.LeanCage_Host_ChannelCode_PairUse_position control_use = Nat_of_nat control_position /\
    rows data_world data_event = Some (data_position, ND.LeanCage_Host_ChannelCode_PairUse_row data_use) /\
    rows control_world control_event = Some (control_position, ND.LeanCage_Host_ChannelCode_PairUse_row control_use) /\
    gateway_channel_pending_pair backend process position
      (gateway_channel_invocation _ _ _ storage (process initial_world) (position initial_world)) gateway_channel_data_pair
      initial_memory initial_world data_prefix data_memory data_world (pair_socket_arguments data Ptrofs.zero) /\
    gateway_channel_pending_pair backend process position
      (gateway_channel_invocation _ _ _ storage (process initial_world) (position initial_world)) gateway_channel_control_pair
      initial_memory initial_world control_prefix control_memory control_world (pair_socket_arguments control Ptrofs.zero) /\
    (position initial_world <= data_position < position next)%nat /\
    (position initial_world <= control_position < position next)%nat /\
    ND.LeanCage_Host_ChannelCode_PairUse_leftObject data_use = Nat_of_nat (pair_left_object ipc data_identity) /\
    ND.LeanCage_Host_ChannelCode_PairUse_rightObject data_use = Nat_of_nat (pair_right_object ipc data_identity) /\
    ND.LeanCage_Host_ChannelCode_PairUse_leftDescription data_use = Nat_of_nat (pair_left_description ipc data_identity) /\
    ND.LeanCage_Host_ChannelCode_PairUse_rightDescription data_use = Nat_of_nat (pair_right_description ipc data_identity) /\
    ND.LeanCage_Host_ChannelCode_PairUse_leftObject control_use = Nat_of_nat (pair_left_object ipc control_identity) /\
    ND.LeanCage_Host_ChannelCode_PairUse_rightObject control_use = Nat_of_nat (pair_right_object ipc control_identity) /\
    ND.LeanCage_Host_ChannelCode_PairUse_leftDescription control_use = Nat_of_nat (pair_left_description ipc control_identity) /\
    ND.LeanCage_Host_ChannelCode_PairUse_rightDescription control_use = Nat_of_nat (pair_right_description ipc control_identity) /\
    gateway_channel_pair_checked data_use /\ gateway_channel_pair_checked control_use.
Proof.
  intros ENTRY DATA CONTROL (data_ordinal & control_ordinal & ORDER & DATA_SLICE & CONTROL_SLICE).
  destruct (gateway_pair_slice_native_use backend process position builders genuine actions attributes resources ipc rows
    recording observation entry_arguments environment temporaries initial_memory initial_world allocated storage
    gateway_channel_data_pair data events target next data_identity data_ordinal ENTRY DATA DATA_SLICE)
    as (data_prefix & data_suffix & data_continuation & data_memory & data_world & data_born & data_born_world & data_event &
      data_receipt & data_position & data_row & DATA_ID & DATA_INDEX & DATA_EVENTS & DATA_PREFIX & DATA_SUFFIX & DATA_PENDING &
      DATA_OPERATION & DATA_LEFT & DATA_RIGHT & DATA_ROW & DATA_BOUND & DATA_CHECKED).
  destruct (gateway_pair_slice_native_use backend process position builders genuine actions attributes resources ipc rows
    recording observation entry_arguments environment temporaries initial_memory initial_world allocated storage
    gateway_channel_control_pair control events target next control_identity control_ordinal ENTRY CONTROL CONTROL_SLICE)
    as (control_prefix & control_suffix & control_continuation & control_memory & control_world & control_born & control_born_world &
      control_event & control_receipt & control_position & control_row & CONTROL_ID & CONTROL_INDEX & CONTROL_EVENTS & CONTROL_PREFIX &
      CONTROL_SUFFIX & CONTROL_PENDING & CONTROL_OPERATION & CONTROL_LEFT & CONTROL_RIGHT & CONTROL_ROW & CONTROL_BOUND & CONTROL_CHECKED).
  exists (gateway_channel_pair_use _ _ _ storage (process initial_world) (position initial_world) gateway_channel_data_pair
      data_position data_row ipc (resources data_world) (resources data_born_world) data_receipt),
    (gateway_channel_pair_use _ _ _ storage (process initial_world) (position initial_world) gateway_channel_control_pair
      control_position control_row ipc (resources control_world) (resources control_born_world) control_receipt),
    data_position, control_position, data_prefix, control_prefix, data_memory, control_memory,
    data_world, control_world, data_event, control_event.
  split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
  split; [reflexivity |]. split; [reflexivity |]. split; [exact DATA_ROW |]. split; [exact CONTROL_ROW |].
  split; [exact DATA_PENDING |]. split; [exact CONTROL_PENDING |]. split; [exact DATA_BOUND |]. split; [exact CONTROL_BOUND |].
  rewrite DATA_ID, CONTROL_ID.
  split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
  split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |]. split; assumption.
Qed.
