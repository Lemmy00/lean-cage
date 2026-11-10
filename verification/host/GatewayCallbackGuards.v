(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Callback induction derives guard retention from actual primitive origins. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayGlobalAddresses GatewayRuntimeMemory
  GatewayScopedBackend GatewayFramedRuntime GatewayInitializationQueryControl GatewayInterpreterSource.
Import ListNotations.

Definition gateway_reentry_guard active complete memory : Prop :=
  Mem.load Mint32 memory active 0 = Some (Vint Int.one) \/
  (Mem.load Mint32 memory active 0 = Some (Vint Int.zero) /\
   Mem.load Mint32 memory complete 0 = Some (Vint Int.one)).

Lemma gateway_private_flag_frame (ge : Clight.genv) identifier object word before after :
  gateway_private_cell_name identifier = true -> Genv.find_symbol ge identifier = Some object ->
  Mem.unchanged_on (fun object _ => gateway_private_cell ge object) before after ->
  Mem.load Mint32 before object 0 = Some (Vint word) -> Mem.load Mint32 after object 0 = Some (Vint word).
Proof.
  intros PRIVATE SYMBOL FRAME LOAD; eapply Mem.load_unchanged_on; [exact FRAME | |exact LOAD].
  intros position BOUND; exists identifier; split; assumption.
Qed.

Theorem gateway_reentry_guard_frame (ge : Clight.genv) active complete before after :
  Genv.find_symbol ge _host_initializing = Some active -> Genv.find_symbol ge _host_initialized = Some complete ->
  Mem.unchanged_on (fun object _ => gateway_private_cell ge object) before after ->
  gateway_reentry_guard active complete before -> gateway_reentry_guard active complete after.
Proof.
  intros ACTIVE COMPLETE FRAME [RUNNING |[IDLE FINISHED]].
  - left; eapply gateway_private_flag_frame with (identifier := _host_initializing); eassumption || reflexivity.
  - right; split.
    + eapply gateway_private_flag_frame with (identifier := _host_initializing); eassumption || reflexivity.
    + eapply gateway_private_flag_frame with (identifier := _host_initialized); eassumption || reflexivity.
Qed.

(* Individual ABI return observations supply only the declared register shape.
   They grant no global-memory, callback or application invariant conclusion. *)
Record gateway_interpreter_result_shapes {World Event} (backend : gateway_backend World Event) : Prop := {
  gateway_get_result_shape : forall before world result after next observed,
    gateway_external backend
      (EF_external "PyInterpreterState_Get" (mksignature [] Xptr cc_default)) []
      (tptr (Tstruct __is noattr)) cc_default [] before world result after next observed ->
    exists object offset, result = Vptr object offset;
  gateway_id_result_shape : forall before world object offset result after next observed,
    gateway_external backend
      (EF_external "PyInterpreterState_GetID" (mksignature [Xptr] Xlong cc_default))
      [tptr (Tstruct __is noattr)] tlong cc_default [Vptr object offset]
      before world result after next observed -> exists identifier, result = Vlong identifier
}.

Theorem gateway_scoped_property_closed {World Event} (backend : gateway_backend World Event)
    ge storage callback (guard : mem -> Prop) (property : mem -> World -> Prop) :
  (forall object, storage object -> ~ gateway_private_cell ge object) ->
  gateway_callback_memory_origin (gateway_private_cell ge) guard callback ->
  (forall before after, Mem.unchanged_on (fun object _ => gateway_private_cell ge object) before after ->
    guard before -> guard after) ->
  (forall memory world, property memory world -> guard memory) ->
  (forall before after world next, Mem.unchanged_on (fun object _ => gateway_private_cell ge object) before after ->
    property before world -> property after next) ->
  gateway_ambient_closed (gateway_scoped_backend backend ge storage callback) property.
Proof.
  intros STORAGE CALLBACK GUARD READY RETAINS before world after next PROPERTY [ACTUAL EPISODE].
  eapply RETAINS; [|exact PROPERTY].
  eapply gateway_scoped_episode_frame; [exact STORAGE |exact CALLBACK |exact GUARD |exact EPISODE |].
  eapply READY; exact PROPERTY.
Qed.

Theorem gateway_scoped_query_laws {World Event} (backend : gateway_backend World Event)
    ge storage callback (guard : mem -> Prop) (property : mem -> World -> Prop) :
  gateway_interpreter_result_shapes backend ->
  (forall object, storage object -> ~ gateway_private_cell ge object) ->
  gateway_callback_memory_origin (gateway_private_cell ge) guard callback ->
  (forall before after, Mem.unchanged_on (fun object _ => gateway_private_cell ge object) before after ->
    guard before -> guard after) ->
  (forall memory world, property memory world -> guard memory) ->
  (forall before after world next, Mem.unchanged_on (fun object _ => gateway_private_cell ge object) before after ->
    property before world -> property after next) ->
  gateway_initialization_query_laws (gateway_scoped_backend backend ge storage callback) property.
Proof.
  intros SHAPES STORAGE CALLBACK GUARD READY RETAINS; constructor.
  - intros before world result after next observed PROPERTY [ACTUAL EPISODE]; split.
    + eapply gateway_get_result_shape; eassumption.
    + eapply RETAINS; [|exact PROPERTY].
      eapply gateway_scoped_episode_frame; [exact STORAGE |exact CALLBACK |exact GUARD |exact EPISODE |].
      eapply READY; exact PROPERTY.
  - intros before world object offset result after next observed PROPERTY [ACTUAL EPISODE]; split.
    + eapply gateway_id_result_shape; eassumption.
    + eapply RETAINS; [|exact PROPERTY].
      eapply gateway_scoped_episode_frame; [exact STORAGE |exact CALLBACK |exact GUARD |exact EPISODE |].
      eapply READY; exact PROPERTY.
Qed.
