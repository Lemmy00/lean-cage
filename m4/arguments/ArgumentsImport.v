(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.arguments: Strict imported argument-length predicate and reference total. *)
From LeanImport Require Import Lean.
Set Lean Error Mode "Fail".
Unset Lean Skip Missing Quotient.
Unset Lean Just Parsing.
Set Lean Line Timeout 10.
Lean Import "../arguments.ndjson".
Check LeanCageM4_Arguments_nativeArgumentLengths.
Print Assumptions LeanCageM4_Arguments_nativeArgumentLengths.
