(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: A genuine GC visitor has a callable external ABI in the actual source environment. *)
From Stdlib Require Import ZArith List String.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayLinkedSource GatewayBindings GatewayOutcome.
Import ListNotations.
Local Open Scope string_scope.

(* This identifier names the SDK's existing function capability in the logical
   linked environment. It introduces no application implementation or stub. The
   platform adapter must bind it to the actual visitor supplied by CPython. *)
Definition gateway_sdk_visitor_identifier : ident := 65537%positive.
Definition gateway_sdk_visitor_definition : Ctypes.fundef function := External
  (EF_external "sdk.gc.visit" (mksignature [Xptr; Xptr] Xint cc_default))
  [tptr (Tstruct __object noattr); tptr tvoid] tint cc_default.
Definition gateway_sdk_capabilities := [(gateway_sdk_visitor_identifier, gateway_sdk_visitor_definition)].

Theorem gateway_sdk_capabilities_registered : gateway_runtime_registration gateway_sdk_capabilities.
Proof.
  split; [reflexivity |split].
  - repeat constructor; cbn; tauto.
  - assert (ABSENT : existsb (Pos.eqb gateway_sdk_visitor_identifier) (map fst global_definitions) = false)
      by (vm_compute; reflexivity).
    intros first second SOURCE FOREIGN SAME; subst first.
    cbn [gateway_sdk_capabilities] in FOREIGN; destruct FOREIGN as [SAME |IMPOSSIBLE]; [subst second |contradiction].
    assert (PRESENT : existsb (Pos.eqb gateway_sdk_visitor_identifier) (map fst global_definitions) = true).
    { apply existsb_exists; exists gateway_sdk_visitor_identifier; split; [exact SOURCE |apply Pos.eqb_refl]. }
    congruence.
Qed.

Theorem gateway_sdk_visitor_callable : exists symbol,
  Genv.find_symbol (Clight.globalenv (gateway_linked_program gateway_sdk_capabilities)) gateway_sdk_visitor_identifier = Some symbol /\
  Genv.find_funct_ptr (Clight.globalenv (gateway_linked_program gateway_sdk_capabilities)) symbol =
    Some gateway_sdk_visitor_definition.
Proof.
  apply gateway_linked_runtime_binding; [apply gateway_sdk_capabilities_registered |left; reflexivity].
Qed.

Theorem gateway_sdk_outcome_layout :
  gateway_outcome_member_layout (Clight.globalenv (gateway_linked_program gateway_sdk_capabilities)).
Proof.
  unfold gateway_outcome_member_layout; rewrite gateway_linked_composite_layout.
  exact actual_outcome_member_layout.
Qed.
