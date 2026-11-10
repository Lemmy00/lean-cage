(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Numeric reference roles name the real C temporaries at the
   actual invocation, keeping recursive callers and cached aliases distinct. *)
From HostGateway Require Import GatewaySource GatewayReferenceLedger.

Definition number_current_owner invocation:=gateway_reference_temporary invocation _value__1.
Definition number_base_owner invocation:=gateway_reference_temporary invocation _base.
Definition number_part_owner invocation:=gateway_reference_temporary invocation _part.
Definition number_scaled_owner invocation:=gateway_reference_temporary invocation _scaled.
Definition number_signed_owner invocation:=gateway_reference_temporary invocation _signed_value.
