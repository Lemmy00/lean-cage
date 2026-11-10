(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Outcome lookup guards preserve all other source definitions. *)
From Stdlib Require Import List Bool.
From compcert Require Import Coqlib AST Ctypes Clight.
From HostGateway Require Import GatewayOutcomeBeforeSource GatewayOutcomeAfterSource.
Import ListNotations.

Definition gateway_outcome_repaired_identifier identifier : bool :=
  Pos.eqb identifier GatewayOutcomeAfterSource._host_outcome_from ||
  Pos.eqb identifier GatewayOutcomeAfterSource._host_outcome_json.

Definition gateway_outcome_retained_definition
    (entry : ident * globdef (Ctypes.fundef Clight.function) type) : bool :=
  negb (gateway_outcome_repaired_identifier (fst entry)).

Theorem gateway_outcome_other_definitions_preserved :
  filter gateway_outcome_retained_definition GatewayOutcomeBeforeSource.global_definitions =
  filter gateway_outcome_retained_definition GatewayOutcomeAfterSource.global_definitions.
Proof. vm_compute; reflexivity. Qed.

Theorem gateway_outcome_public_identifiers_preserved :
  GatewayOutcomeBeforeSource.public_idents = GatewayOutcomeAfterSource.public_idents.
Proof. reflexivity. Qed.

Theorem gateway_outcome_composites_preserved :
  GatewayOutcomeBeforeSource.composites = GatewayOutcomeAfterSource.composites.
Proof. reflexivity. Qed.

Theorem gateway_outcome_function_identifiers_preserved :
  GatewayOutcomeBeforeSource._host_outcome_from = GatewayOutcomeAfterSource._host_outcome_from /\
  GatewayOutcomeBeforeSource._host_outcome_json = GatewayOutcomeAfterSource._host_outcome_json.
Proof. split; reflexivity. Qed.

Definition gateway_outcome_variable_definition
    (entry : ident * globdef (Ctypes.fundef Clight.function) type) : bool :=
  match snd entry with Gvar _ => true | Gfun _ => false end.

Theorem gateway_outcome_global_initializers_preserved :
  filter gateway_outcome_variable_definition GatewayOutcomeBeforeSource.global_definitions =
  filter gateway_outcome_variable_definition GatewayOutcomeAfterSource.global_definitions.
Proof. vm_compute; reflexivity. Qed.
