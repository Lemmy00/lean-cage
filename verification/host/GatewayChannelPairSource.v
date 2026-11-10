(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: The actual source pointer fixes
   data/control before the syscall returns. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
From LeanImport Require Import Lean.
Require Import CallContexts.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewaySpawnABI GatewayChannelSourceScope
  GatewaySpawnRuntime GatewaySpawnResources GatewaySpawnHistory GatewayNativeRows GatewayNativePairObservation GatewayPairSource GatewayExchangeSetup GatewayExchangePairPaths GatewayChannelCodeProducer GatewayNativeImport.
Import ListNotations.
Local Close Scope lean_scope.
Module ND := GatewayNativeImport.

Definition gateway_channel_local kind :=
  match kind with gateway_channel_data_pair => _pair | gateway_channel_control_pair => _control end.
Definition gateway_channel_stage kind :=
  match kind with gateway_channel_data_pair => exchange_data_stage | gateway_channel_control_pair => exchange_control_stage end.

Record gateway_channel_pending_pair {World Event} (backend : gateway_backend World Event)
    (process position : World -> nat) (invocation : ND.LeanCage_Host_ChannelCode_Invocation)
    (kind : gateway_channel_pair_kind) initial_memory initial_world events memory world
    (actual_arguments : list Values.val) : Prop := {
  gateway_channel_pending_source : exists arguments environment temporaries allocated
      (storage : gateway_channel_storage environment initial_memory allocated) continuation,
    function_entry2 (Clight.globalenv prog) f_host_exchange arguments initial_memory environment temporaries allocated /\
    invocation = gateway_channel_invocation _ _ _ storage (process initial_world) (position initial_world) /\
    actual_arguments = pair_socket_arguments (gateway_channel_output storage kind) Ptrofs.zero /\
    gateway_steps backend (Clight.globalenv prog)
      (gateway_live (State f_host_exchange (fn_body f_host_exchange) Kstop environment temporaries allocated) initial_world)
      events (gateway_live (Callstate (gateway_spawn_signature gateway_socketpair_api)
        actual_arguments continuation memory) world)
}.

(* Both slices are actual source trajectories. They may end at the pending SDK
   frontier; no syscall result, future copyout, helper success or fork is used. *)
Theorem actual_exchange_pair_pending_source {World Event} (backend : gateway_backend World Event)
    process position arguments environment temporaries initial_memory initial_world allocated kind object
    caller_events helper_events helper_before helper_world helper_temporaries memory world :
  function_entry2 (Clight.globalenv prog) f_host_exchange arguments initial_memory environment temporaries allocated ->
  environment ! (gateway_channel_local kind) = Some (object, tarray tint 2) ->
  gateway_steps backend (Clight.globalenv prog)
    (gateway_live (State f_host_exchange (fn_body f_host_exchange) Kstop environment temporaries allocated) initial_world)
    caller_events (gateway_live (Callstate (Internal f_host_private_pair) [Vptr object Ptrofs.zero]
      (exchange_pair_cont (gateway_channel_stage kind) environment helper_temporaries) helper_before) helper_world) ->
  gateway_steps backend (Clight.globalenv prog)
    (gateway_live (Callstate (Internal f_host_private_pair) [Vptr object Ptrofs.zero] Kstop helper_before) helper_world)
    helper_events (gateway_live (Callstate (gateway_spawn_signature gateway_socketpair_api)
      (pair_socket_arguments object Ptrofs.zero) (pair_socket_cont (Vptr object Ptrofs.zero)) memory) world) ->
  exists storage : gateway_channel_storage environment initial_memory allocated,
    gateway_channel_output storage kind = object /\
    gateway_channel_pending_pair backend process position
      (gateway_channel_invocation _ _ _ storage (process initial_world) (position initial_world)) kind
      initial_memory initial_world (caller_events ++ helper_events) memory world (pair_socket_arguments object Ptrofs.zero).
Proof.
  intros ENTRY LOCAL CALLER HELPER.
  destruct (actual_exchange_channel_storage _ _ _ _ _ _ ENTRY) as [storage].
  assert (OUTPUT : gateway_channel_output storage kind = object).
  { pose proof (actual_channel_output_local _ _ _ storage kind) as LOOKUP.
    change (environment ! (gateway_channel_local kind) = Some (gateway_channel_output storage kind, tarray tint 2)) in LOOKUP.
    rewrite LOCAL in LOOKUP; inversion LOOKUP; reflexivity. }
  exists storage; split; [exact OUTPUT |].
  constructor; exists arguments, environment, temporaries, allocated, storage,
    (plug_cont (pair_socket_cont (Vptr object Ptrofs.zero))
      (exchange_pair_cont (gateway_channel_stage kind) environment helper_temporaries)).
  split; [exact ENTRY |]. split; [reflexivity |]. split; [rewrite OUTPUT; reflexivity |].
  eapply gateway_steps_append; [exact CALLER |].
  exact (gateway_plug_steps backend (Clight.globalenv prog) _ _ _
    (exchange_pair_cont (gateway_channel_stage kind) environment helper_temporaries) I HELPER).
Qed.

(* This observes a returned syscall, without requiring the private-pair helper
   or original exchange to return. The pre-return source frontier above remains
   available separately for actual committed, unobserved kernel rows. *)
Theorem gateway_channel_pair_row_from_call {World Event} (backend : gateway_backend World Event)
    process position builders genuine actions attributes resources ipc rows
    (recording : GatewayNativeRows.gateway_native_row_runtime backend process position builders genuine actions attributes rows)
    (observation : GatewayNativePairObservation.gateway_native_pair_runtime backend resources ipc rows)
    invocation kind initial_memory initial_world events memory world actual_arguments
    born born_world observed object
    (receipt : GatewaySpawnResources.gateway_socketpair_receipt ipc (resources world) (resources born_world)) :
  gateway_channel_pending_pair backend process position invocation kind initial_memory initial_world events memory world actual_arguments ->
  actual_arguments = pair_socket_arguments object Ptrofs.zero ->
  GatewaySpawnABI.gateway_spawn_operation backend gateway_socketpair_api actual_arguments
    memory world (Vint Int.zero) born born_world observed ->
  Mem.load Mint32 born object 0 = Some (Vint (Int.repr (GatewaySpawnResources.gateway_pair_left _ _ _ receipt))) ->
  Mem.load Mint32 born object 4 = Some (Vint (Int.repr (GatewaySpawnResources.gateway_pair_right _ _ _ receipt))) ->
  exists selected row use,
    rows world observed = Some (selected, row) /\
    (position initial_world <= selected < position born_world)%nat /\
    ND.LeanCage_Host_ChannelCode_PairUse_invocation use = invocation /\
    gateway_channel_pair_kind_of use = gateway_channel_kind kind /\
    ND.LeanCage_Host_ChannelCode_PairUse_position use = Nat_of_nat selected /\
    ND.LeanCage_Host_ChannelCode_PairUse_row use = row /\
    gateway_channel_pair_checked use.
Proof.
  intros [SOURCE] ARGS OPERATION LEFT RIGHT.
  destruct SOURCE as (entry_arguments & environment & temporaries & allocated & storage & continuation & ENTRY & INVOCATION & INPUTS & PREFIX).
  subst invocation.
  rewrite INPUTS in ARGS, OPERATION.
  assert (OUTPUT : gateway_channel_output storage kind = object).
  { inversion ARGS; reflexivity. }
  rewrite OUTPUT in OPERATION.
  destruct (GatewayNativePairObservation.gateway_actual_socket_pair_native_row backend process position builders genuine actions attributes
    resources ipc rows recording observation object Ptrofs.zero memory world born born_world observed receipt OPERATION LEFT RIGHT)
    as (selected & row & ROW & PROCESS & CODE & ORDER & PRODUCT & FIRST & SECOND).
  destruct (GatewayNativeRows.gateway_native_run_actor backend process position builders genuine actions attributes rows recording
    (Clight.globalenv prog) _ _ _ PREFIX) as [SAME_PROCESS POSITION].
  cbn [GatewaySpawnHistory.gateway_state_world] in SAME_PROCESS, POSITION.
  rewrite SAME_PROCESS in PROCESS.
  exists selected, row, (gateway_channel_pair_use _ _ _ storage (process initial_world) (position initial_world)
    kind selected row ipc (resources world) (resources born_world) receipt).
  split; [exact ROW |]. split; [lia |].
  split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
  constructor; apply gateway_channel_pair_use_consistent; try assumption; lia.
Qed.
