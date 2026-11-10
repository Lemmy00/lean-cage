(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual numeric helper call binds its pointer and machine-width byte count before lexical checks. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayFunctionEntry GatewayNoLocalEntry GatewayFramedRuntime GatewayContexts GatewayCalls.
Import ListNotations.

Lemma gateway_json_number_entry_parameters ge object size before environment parameters allocated :
  function_entry2 ge f_host_json_number [Vptr object Ptrofs.zero; Vlong size] before environment parameters allocated ->
  parameters ! _bytes = Some (Vptr object Ptrofs.zero) /\ parameters ! _size = Some (Vlong size).
Proof.
  intro ENTRY; inversion ENTRY; subst.
  match goal with BIND : bind_parameter_temps _ _ _ = Some _ |- _ =>
    change (Some (PTree.set _size (Vlong size) (PTree.set _bytes (Vptr object Ptrofs.zero)
      (create_undef_temps (fn_temps f_host_json_number)))) = Some parameters) in BIND;
    inversion BIND; subst parameters end.
  split; [rewrite PTree.gso by discriminate; apply PTree.gss |apply PTree.gss].
Qed.

Theorem gateway_actual_json_number_call_entry {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) object size before world events value after next :
  gateway_ambient_closed backend property -> property before world ->
  gateway_steps backend ge (gateway_live (Callstate (Internal f_host_json_number) [Vptr object Ptrofs.zero; Vlong size] Kstop before) world) events
    (gateway_live (Returnstate value Kstop after) next) ->
  exists prefix suffix memory owner parameters,
    events = prefix ++ suffix /\
    Forall (fun event => event = gateway_source E0 \/ event = gateway_ambient) prefix /\
    gateway_steps backend ge (gateway_live (Callstate (Internal f_host_json_number) [Vptr object Ptrofs.zero; Vlong size] Kstop before) world) prefix
      (gateway_live (State f_host_json_number (fn_body f_host_json_number) Kstop empty_env parameters memory) owner) /\
    property memory owner /\ parameters ! _bytes = Some (Vptr object Ptrofs.zero) /\ parameters ! _size = Some (Vlong size) /\
    gateway_steps backend ge
      (gateway_live (State f_host_json_number (fn_body f_host_json_number) Kstop empty_env parameters memory) owner) suffix
      (gateway_live (Returnstate value Kstop after) next).
Proof.
  intros CLOSED INPUT RUN.
  destruct (actual_gateway_function_entry_ambient backend ge f_host_json_number [Vptr object Ptrofs.zero; Vlong size] Kstop
    before world events value Kstop after next RUN)
    as (pending & suffix & memory & owner & environment & parameters & allocated & EVENTS & AMBIENT & PREFIX & ENTRY & REST).
  destruct (gateway_json_number_entry_parameters _ _ _ _ _ _ _ ENTRY) as [BYTES SIZE].
  destruct (gateway_no_local_entry ge f_host_json_number [Vptr object Ptrofs.zero; Vlong size] memory environment parameters allocated eq_refl ENTRY) as [ENV SAME]; subst environment allocated.
  assert (READY : property memory owner).
  { exact (gateway_ambient_run_ready backend ge property CLOSED
      (Callstate (Internal f_host_json_number) [Vptr object Ptrofs.zero; Vlong size] Kstop before)
      before world pending memory owner INPUT AMBIENT PREFIX). }
  exists (pending ++ [gateway_source E0]), suffix, memory, owner, parameters.
  split; [rewrite EVENTS, <- app_assoc; reflexivity |]. split.
  - apply Forall_app; split; [eapply Forall_impl; [|exact AMBIENT]; intros event SAME; right; exact SAME |].
    constructor; [left; reflexivity |constructor].
  - split.
    + eapply gateway_steps_append; [exact PREFIX |].
      econstructor; [apply gateway_internal; [exact I |apply step_internal_function; exact ENTRY] |constructor].
    + split; [exact READY |]. split; [exact BYTES |]. split; [exact SIZE |exact REST].
Qed.
