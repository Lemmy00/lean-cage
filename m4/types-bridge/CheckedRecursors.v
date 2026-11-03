(* §AR-m4-routes.reporting.bridge: Every exported signature and constructor equation is checked. *)
From LeanImport Require Import Lean.
Require Import TypePrefix TypeRecursors StmtPrefix StmtRecursors.
Set Lean Error Mode "Fail".
Unset Lean Skip Missing Quotient.
Lean Check Recursors "CC.Stmt" "cc_stmt_type" "cc_stmt_sprop" "cc_lstmts_type" "cc_lstmts_sprop".
Lean Assert Complete.
