(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Finite actual application callback trees produce pointer retention. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayGlobalAddresses GatewayPointerOrigins
  GatewayPointerMemory GatewayPointerControl GatewayLinkedSource GatewayCallbackEntries GatewayRuntimeMemory
  GatewayRuntimeCoverage GatewayCoveredPointers.
Import ListNotations.

Definition gateway_state_memory {World} (source : gateway_state World) : mem :=
  match source with gateway_live source _ => memory_of source |gateway_dead memory _ => memory end.

(* A returned callback exposes its actual return value. Pending and lost callback
   prefixes expose no invented pointer. The outer actual occurrence and its
   micro-action coverage retain whether it returned or was lost. *)
Inductive gateway_callback_result {World} : gateway_state World -> val -> Prop :=
| gateway_callback_returned : forall value memory world,
    gateway_callback_result (gateway_live (Returnstate value Kstop memory) world) value
| gateway_callback_prefix : forall source, gateway_callback_result source Vundef.

Fixpoint gateway_source_callbacks {World Event} (backend : gateway_backend World Event) runtime storage depth
    (before : mem) (arguments : list val) (after : mem) (result : val) : Prop :=
  match depth with
  | O => False
  | S inside => exists identifier body world events target,
      In (identifier, Gfun (Internal body)) global_definitions /\ gateway_callback_registered identifier = true /\
      length arguments = length (fn_params body) /\
      gateway_covered_steps backend (Clight.globalenv (gateway_linked_program runtime)) storage
        (gateway_source_callbacks backend runtime storage inside)
        (gateway_live (Callstate (Internal body) arguments Kstop before) world) events target /\
      after = gateway_state_memory target /\ gateway_callback_result target result
  end.

Lemma gateway_callback_pointer_entry ge identifier body arguments memory :
  In (identifier, Gfun (Internal body)) global_definitions ->
  gateway_memory_avoids (gateway_private_cell ge) memory ->
  (forall object, gateway_private_cell ge object -> Mem.valid_block memory object) ->
  Forall (gateway_pointer_avoids (gateway_private_cell ge)) arguments ->
  gateway_pointer_source ge (Callstate (Internal body) arguments Kstop memory).
Proof.
  intros MEMBER MEMORY LIVE ARGUMENTS; split; [exact MEMORY |split; [exact LIVE |]].
  split; [|split; [exact I |exact ARGUMENTS]].
  exact (proj1 (forallb_forall _ _) actual_gateway_pointer_control (identifier, Gfun (Internal body)) MEMBER).
Qed.

Lemma gateway_callback_pointer_result {World} ge (target : gateway_state World) result :
  gateway_pointer_state ge target -> gateway_callback_result target result ->
  gateway_pointer_avoids (gateway_private_cell ge) result.
Proof.
  intros READY RETURN; inversion RETURN; subst; [exact (proj2 (proj2 (proj2 READY))) |exact I].
Qed.

Theorem gateway_source_callbacks_pointer {World Event} (backend : gateway_backend World Event)
    runtime storage depth :
  forallb gateway_runtime_function runtime = true ->
  (forall object, storage object -> ~ gateway_private_cell (Clight.globalenv (gateway_linked_program runtime)) object) ->
  gateway_callback_pointer_origin (gateway_private_cell (Clight.globalenv (gateway_linked_program runtime)))
    (gateway_source_callbacks backend runtime storage depth).
Proof.
  intros RUNTIME STORAGE; induction depth as [|depth IH];
    intros before arguments after result MEMORY LIVE ARGUMENTS CALLBACK; [contradiction |].
  destruct CALLBACK as (identifier & body & world & events & target & MEMBER & REGISTERED & ABI & RUN & AFTER & RESULT).
  pose proof (gateway_callback_pointer_entry _ _ _ _ _ MEMBER MEMORY LIVE ARGUMENTS) as INITIAL.
  pose proof (gateway_covered_pointer_prefix backend runtime storage _
    (gateway_live (Callstate (Internal body) arguments Kstop before) world) events target
    RUNTIME STORAGE IH INITIAL RUN) as FINAL.
  subst after; split; [|split; [|eapply gateway_callback_pointer_result; eassumption]].
  - destruct target as [source next |memory next]; [destruct source |]; exact (proj1 FINAL).
  - destruct target as [source next |memory next].
    + destruct source; exact (proj1 (proj2 FINAL)).
    + exact (proj2 FINAL).
Qed.
