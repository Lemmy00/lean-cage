(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Actual ordinary C steps cannot enter a class writer. *)
From Stdlib Require Import List Bool.
From compcert Require Import Coqlib Maps AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayLinkedSource GatewayOrdinarySource
  GatewayOrdinaryControl.
Import ListNotations.

Theorem gateway_ordinary_internal_source runtime source observed target :
  gateway_runtime_registration runtime -> internal_state source -> gateway_ordinary_source source ->
  step2 (Clight.globalenv (gateway_linked_program runtime)) source observed target -> gateway_ordinary_source target.
Proof.
  intros REGISTERED INTERNAL GOOD STEP; inversion STEP; subst;
    cbn [internal_state] in INTERNAL; try contradiction;
    cbn [gateway_ordinary_source] in GOOD |- *.
  all: try (destruct GOOD as [WHOLE [CURRENT [CONTINUATION GLOBALS]]]).
  all: try (cbn [gateway_ordinary_statement gateway_ordinary_action] in CURRENT;
    repeat rewrite andb_true_iff in CURRENT).
  all: try (cbn [gateway_ordinary_cont] in CONTINUATION).
  all: cbn [gateway_ordinary_cont gateway_ordinary_statement gateway_ordinary_action].
  all: repeat rewrite andb_true_iff.
  all: try solve [repeat split; assumption || reflexivity || tauto].
  - split.
    + assert (ORDINARY : gateway_ordinary_definition fd = true).
      { eapply gateway_ordinary_called_definition with (expression := a) (value := vf)
          (arguments := tyargs) (result := tyres) (convention := cconv)
          (environment := e) (temporaries := le) (memory := m); eassumption || tauto. }
      destruct fd as [body |]; [|exact I]. split; [exact ORDINARY |].
      eapply gateway_linked_internal_origin; [exact (proj1 REGISTERED) |eassumption].
    + repeat split; assumption.
  - destruct b; repeat split; tauto.
  - apply gateway_ordinary_call_cont; exact CONTINUATION.
  - apply gateway_ordinary_call_cont; exact CONTINUATION.
  - repeat split; try assumption; apply gateway_ordinary_switch; exact (proj2 CURRENT).
  - destruct (gateway_ordinary_find_label lbl (fn_body f) (call_cont k) s' k' WHOLE
      (gateway_ordinary_call_cont _ CONTINUATION) H) as [BODY CONT].
    repeat split; assumption.
  - destruct GOOD as [[ORDINARY [identifier MEMBER]] CONTINUATION].
    destruct (gateway_actual_ordinary_body identifier f MEMBER ORDINARY) as [BODY NONLOCAL].
    repeat split; try assumption.
    eapply gateway_ordinary_entry_unshadowed; eassumption.
  - destruct GOOD as [WHOLE [GLOBALS CONTINUATION]]; repeat split; assumption || reflexivity.
Qed.
