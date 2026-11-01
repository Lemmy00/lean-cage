(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.plan: Preserve strict checking of the actual numeric interface export. *)
From LeanImport Require Import Lean.
Set Lean Error Mode "Fail".
Unset Lean Skip Missing Quotient.
Unset Lean Just Parsing.
Set Lean Line Timeout 10.
Lean Import "../plan-decimal.ndjson".
Check LeanCageM4_Plan_parseDecimal.
Print Assumptions LeanCageM4_Plan_parseDecimal.
