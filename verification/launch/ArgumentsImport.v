(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.effects: Import the actual executable byte decoder with strict kernel checking. *)
From LeanImport Require Import Lean.
Set Lean Error Mode "Fail".
Unset Lean Skip Missing Quotient.
Unset Lean Just Parsing.
Set Lean Line Timeout 10.
Lean Import "arguments-code.ndjson".
Check LeanCage_Entry_Arguments_unsigned.
Check LeanCage_Entry_ArgumentMeaning_decimalValue.
Check LeanCage_Entry_ArgumentMeaning_byteValues.
Check LeanCage_Entry_ArgumentMeaning_nativeValues.
Check LeanCage_Entry_PhysicalHandoff_binding.
Check LeanCage_Entry_PhysicalHandoff_objectCode.
Check LeanCage_Entry_PhysicalHandoff_grantBeforeRead.
Print Assumptions LeanCage_Entry_Arguments_unsigned.
