(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-routes.lean: Generate the checked list scheme before the replacement trial. *)
From LeanImport Require Import Lean.
Scheme All for List_inst1.
Set Lean Error Mode "Fail".
Unset Lean Skip Missing Quotient.
Lean Import "ported-step.ndjson".
