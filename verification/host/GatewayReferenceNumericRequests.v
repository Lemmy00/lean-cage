(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Numeric SDK arguments are the exact retained builtin values,
   with independent source reference credits even when cached object pointers coincide. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers Values.
From HostGateway Require Import GatewayPython GatewayObjects GatewayReferences GatewayValue GatewayObjectThreads
  GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceHeld GatewayReferenceThreads GatewayReferenceContainerScope.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Definition gateway_reference_scalar_capture ticket pointer value:gateway_held_value:={|
  gateway_held_ticket:=ticket;gateway_held_object:=pointer;gateway_held_view:=gateway_held_scalar_value value|}.

Theorem gateway_reference_scalar_capture_value {World}python objects decimal_float ledger held world ticket pointer value:
  @gateway_reference_scope World python objects decimal_float ledger held world->
  In(gateway_reference_scalar_capture ticket pointer value)held->
  gateway_rooted(python world)(objects world)pointer /\gateway_object_values(objects world)pointer=Some value /\
  gateway_private_tree(objects world)pointer /\gateway_destructible(objects world)pointer.
Proof.
  intros SCOPE MEMBER;destruct(gateway_reference_capture_member _ _ _ _ _ _ _ SCOPE MEMBER)
    as[[owner OWNED][PRIVATE[DESTROY[VALUE CHILDREN]]]].
  split;[eapply gateway_reference_owned_rooted;[exact(proj1 SCOPE)|exact OWNED]|].
  exact(conj VALUE(conj PRIVATE DESTROY)).
Qed.

Theorem gateway_reference_multiply_request {World}python objects decimal_float ledger held world memory left_ticket left first right_ticket right second:
  @gateway_reference_scope World python objects decimal_float ledger held world->
  In(gateway_reference_scalar_capture left_ticket left(gateway_long_object first))held->
  In(gateway_reference_scalar_capture right_ticket right(gateway_long_object second))held->
  gateway_constructor_request decimal_float(objects world)memory gateway_api_number_multiply[left;right](gateway_long_object(first*second)) /\
  gateway_constructor_roots(python world)(objects world)gateway_api_number_multiply[left;right].
Proof.
  intros SCOPE LEFT RIGHT.
  destruct(gateway_reference_scalar_capture_value _ _ _ _ _ _ _ _ _ SCOPE LEFT)as[LEFT_ROOT[LEFT_VALUE REST]].
  destruct(gateway_reference_scalar_capture_value _ _ _ _ _ _ _ _ _ SCOPE RIGHT)as[RIGHT_ROOT[RIGHT_VALUE MORE]].
  split;[apply gateway_request_multiply;assumption|split;assumption].
Qed.

Theorem gateway_reference_add_request {World}python objects decimal_float ledger held world memory left_ticket left first right_ticket right second:
  @gateway_reference_scope World python objects decimal_float ledger held world->
  In(gateway_reference_scalar_capture left_ticket left(gateway_long_object first))held->
  In(gateway_reference_scalar_capture right_ticket right(gateway_long_object second))held->
  gateway_constructor_request decimal_float(objects world)memory gateway_api_number_add[left;right](gateway_long_object(first+second)) /\
  gateway_constructor_roots(python world)(objects world)gateway_api_number_add[left;right].
Proof.
  intros SCOPE LEFT RIGHT.
  destruct(gateway_reference_scalar_capture_value _ _ _ _ _ _ _ _ _ SCOPE LEFT)as[LEFT_ROOT[LEFT_VALUE REST]].
  destruct(gateway_reference_scalar_capture_value _ _ _ _ _ _ _ _ _ SCOPE RIGHT)as[RIGHT_ROOT[RIGHT_VALUE MORE]].
  split;[apply gateway_request_add;assumption|split;assumption].
Qed.

Theorem gateway_reference_negative_request {World}python objects decimal_float ledger held world memory ticket pointer value:
  @gateway_reference_scope World python objects decimal_float ledger held world->
  In(gateway_reference_scalar_capture ticket pointer(gateway_long_object value))held->
  gateway_constructor_request decimal_float(objects world)memory gateway_api_number_negative[pointer](gateway_long_object(-value)) /\
  gateway_constructor_roots(python world)(objects world)gateway_api_number_negative[pointer].
Proof.
  intros SCOPE MEMBER.
  destruct(gateway_reference_scalar_capture_value _ _ _ _ _ _ _ _ _ SCOPE MEMBER)as[ROOT[LOOKUP REST]].
  split;[apply gateway_request_negative;exact LOOKUP|exact ROOT].
Qed.
