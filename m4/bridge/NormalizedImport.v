(* §AR-m4-bridge.import: Fail closed and keep every kernel check enabled. *)
From LeanImport Require Import Lean.
Set Lean Error Mode "Fail".
Unset Lean Skip Missing Quotient.
Unset Lean Just Parsing.
Set Lean Line Timeout 10.
Lean Import "../normalized-decoder.ndjson".
Check LeanCageM4_Normalized_decode.
Print Assumptions LeanCageM4_Normalized_decode.
