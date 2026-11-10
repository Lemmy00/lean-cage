(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Callback source executions keep the same SDK episode worlds. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayGlobalAddresses GatewayLinkedSource
  GatewayRuntimeMemory GatewayRuntimeEpisodes GatewaySourceCallbacks GatewayCallbackEntries GatewayCallbackGuards GatewayCallbackRetention.
Import ListNotations.

Definition gateway_state_world {World} (source : gateway_state World) : World :=
  match source with gateway_live _ world |gateway_dead _ world => world end.

Fixpoint gateway_observed_callbacks {World Event} (backend : gateway_backend World Event) runtime storage
    (leaf : mem -> World -> mem -> World -> Prop) depth
    (before : mem) (world : World) (arguments : list val) (after : mem) (next : World) (result : val) : Prop :=
  match depth with
  | O => False
  | S inside => exists identifier body events target,
      In (identifier, Gfun (Internal body)) global_definitions /\ gateway_callback_registered identifier = true /\
      length arguments = length (fn_params body) /\
      gateway_observed_steps backend (Clight.globalenv (gateway_linked_program runtime)) storage leaf
        (gateway_observed_callbacks backend runtime storage leaf inside)
        (gateway_live (Callstate (Internal body) arguments Kstop before) world) events target /\
      after = gateway_state_memory target /\ next = gateway_state_world target /\ gateway_callback_result target result
  end.

Theorem gateway_observed_callback_source {World Event} (backend : gateway_backend World Event)
    runtime storage leaf depth : forall before world arguments after next result,
  gateway_observed_callbacks backend runtime storage leaf depth before world arguments after next result ->
  gateway_source_callbacks backend runtime storage depth before arguments after result.
Proof.
  induction depth as [|depth IH]; intros before world arguments after next result CALLBACK; [contradiction |].
  destruct CALLBACK as (identifier & body & events & target & MEMBER & EXPORTED & ABI & RUN & AFTER & NEXT & RESULT).
  exists identifier, body, world, events, target; split; [exact MEMBER |split; [exact EXPORTED |split; [exact ABI |]]].
  split; [eapply gateway_observed_steps_memory; [exact IH |exact RUN] |split; assumption].
Qed.

Theorem gateway_observed_callback_cells {World Event} (backend : gateway_backend World Event)
    runtime storage leaf depth active complete before world arguments after next result :
  gateway_runtime_registration runtime -> gateway_interpreter_result_shapes backend ->
  (forall object, storage object -> ~ gateway_private_cell (Clight.globalenv (gateway_linked_program runtime)) object) ->
  Genv.find_symbol (Clight.globalenv (gateway_linked_program runtime)) _host_initializing = Some active ->
  Genv.find_symbol (Clight.globalenv (gateway_linked_program runtime)) _host_initialized = Some complete ->
  gateway_runtime_memory_scope (gateway_private_cell (Clight.globalenv (gateway_linked_program runtime))) before arguments ->
  gateway_observed_callbacks backend runtime storage leaf depth before world arguments after next result ->
  gateway_runtime_memory_scope (gateway_private_cell (Clight.globalenv (gateway_linked_program runtime))) after [result] /\
    (gateway_reentry_guard active complete before ->
      Mem.unchanged_on (fun object _ => gateway_private_cell (Clight.globalenv (gateway_linked_program runtime)) object) before after).
Proof.
  intros REGISTERED SHAPES STORAGE ACTIVE COMPLETE [MEMORY [LIVE ARGUMENTS]] CALLBACK.
  pose proof (gateway_observed_callback_source backend runtime storage leaf depth _ _ _ _ _ _ CALLBACK) as SOURCE.
  destruct (gateway_source_callbacks_memory backend runtime storage active complete depth REGISTERED SHAPES STORAGE ACTIVE COMPLETE
    before arguments after result MEMORY LIVE ARGUMENTS SOURCE) as [NEXT [RETAINED [RESULT FRAME]]].
  split; [split; [exact NEXT |split; [exact RETAINED |constructor; [exact RESULT |constructor]]] |exact FRAME].
Qed.
