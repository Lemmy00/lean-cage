(* §AR-m4-routes.reporting.bridge: Check the actual exported recursive representations. *)
From LeanImport Require Import Lean.
Require Import TypePrefix TypeRecursors.
Set Lean Error Mode "Fail".
Unset Lean Skip Missing Quotient.
Set Lean Defer Nested Recursors.
Lean Check Recursors "CC.Ty" "cc_ty_type" "cc_ty_sprop" "cc_ty_list_type" "cc_ty_list_sprop".
Lean Import "../../routes/ported-step.ndjson" 2775 13350.

