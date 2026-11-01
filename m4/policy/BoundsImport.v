(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.bounds: Strict import of the actual normalized bounds interface. *)
From LeanImport Require Import Lean.
Set Lean Error Mode "Fail".
Unset Lean Skip Missing Quotient.
Unset Lean Just Parsing.
Set Lean Line Timeout 10.
Lean Import "../bounds.ndjson".
Check LeanCageM4_Bounds_nativeBounds.
Print Assumptions LeanCageM4_Bounds_nativeBounds.
