(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Import the executable path layout with every strict kernel check. *)
From LeanImport Require Import Lean.
Set Lean Error Mode "Fail".
Unset Lean Skip Missing Quotient.
Unset Lean Just Parsing.
Set Lean Line Timeout 10.
Lean Import "bootstrap-code.ndjson".
Check LeanCage_Host_BootstrapCode_Layout.
Check LeanCage_Host_BootstrapCode_suffix.
Check LeanCage_Host_BootstrapCode_executable.
Check LeanCage_Host_BootstrapCode_results.
Check LeanCage_Host_BootstrapCode_supported.
Check LeanCage_Host_BootstrapCode_layout.
