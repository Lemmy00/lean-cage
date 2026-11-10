(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The observation error repair preserves every other source body. *)
From Stdlib Require Import List Bool String.
From compcert Require Import Coqlib AST Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewayObservationBeforeSource GatewayObservationAfterSource GatewayRegistry.
Import ListNotations.
Local Open Scope string_scope.

Definition gateway_observation_repaired_identifier identifier : bool :=
  Pos.eqb identifier GatewayObservationAfterSource._host_outcome_observation ||
  Pos.eqb identifier GatewayObservationAfterSource._PyDict_GetItemWithError.

Definition gateway_observation_retained_definition
    (entry : ident * globdef (Ctypes.fundef Clight.function) type) : bool :=
  negb (gateway_observation_repaired_identifier (fst entry)).

Theorem gateway_observation_other_definitions_preserved :
  filter gateway_observation_retained_definition GatewayObservationBeforeSource.global_definitions =
  filter gateway_observation_retained_definition GatewayObservationAfterSource.global_definitions.
Proof. vm_compute; reflexivity. Qed.

Theorem gateway_observation_other_public_identifiers_preserved :
  filter (fun identifier => negb (Pos.eqb identifier GatewayObservationAfterSource._PyDict_GetItemWithError))
    GatewayObservationBeforeSource.public_idents =
  filter (fun identifier => negb (Pos.eqb identifier GatewayObservationAfterSource._PyDict_GetItemWithError))
    GatewayObservationAfterSource.public_idents.
Proof. vm_compute; reflexivity. Qed.

Theorem gateway_observation_composites_preserved :
  GatewayObservationBeforeSource.composites = GatewayObservationAfterSource.composites.
Proof. reflexivity. Qed.

Theorem gateway_observation_old_getter_identifier_preserved :
  GatewayObservationBeforeSource._host_outcome_observation = GatewayObservationAfterSource._host_outcome_observation.
Proof. reflexivity. Qed.

Theorem gateway_observation_added_dictionary_abi :
  In (GatewayObservationAfterSource._PyDict_GetItemWithError,
    Gfun (External (EF_external "PyDict_GetItemWithError" (mksignature [Xptr; Xptr] Xptr cc_default))
      [tptr (Tstruct GatewayObservationAfterSource.__object noattr);
       tptr (Tstruct GatewayObservationAfterSource.__object noattr)]
      (tptr (Tstruct GatewayObservationAfterSource.__object noattr)) cc_default))
    GatewayObservationAfterSource.global_definitions.
Proof. apply gateway_program_definition_present; vm_compute; reflexivity. Qed.
