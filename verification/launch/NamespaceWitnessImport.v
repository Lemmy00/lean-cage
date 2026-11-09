(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.acceptance: Strictly import the exact ordinary useful worker data. *)
From LeanImport Require Import Lean.
Set Lean Error Mode "Fail".
Unset Lean Skip Missing Quotient.
Unset Lean Just Parsing.
Set Lean Line Timeout 10.
Lean Import "caller-witness-code.ndjson".
Check LeanCage_Entry_CallerWitness_objects.
Check LeanCage_Entry_CallerWitness_cloexec.
Check LeanCage_Entry_CallerWitness_argumentBytes.
Check LeanCage_Entry_CallerWitness_ordinaryRead.
Check LeanCage_Entry_CallerWitness_ordinaryWrite.
Print Assumptions LeanCage_Entry_CallerWitness_objects.
Print Assumptions LeanCage_Entry_CallerWitness_argumentBytes.
