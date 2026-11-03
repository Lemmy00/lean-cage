(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-routes.lean: A strict failed import is retained as a blocker, not a proof. *)
From LeanImport Require Import Lean.
Set Lean Error Mode "Fail".
Unset Lean Skip Missing Quotient.
Lean Import "ported-step.ndjson".
