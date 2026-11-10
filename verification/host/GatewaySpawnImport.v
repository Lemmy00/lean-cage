(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Import the exact executable engine descriptor projection. *)
From LeanImport Require Import Lean.
Set Lean Error Mode "Fail".
Unset Lean Skip Missing Quotient.
Unset Lean Just Parsing.
Set Lean Line Timeout 10.
Lean Import "spawn-code.ndjson".
Check LeanCage_Host_NativeSpawn_Descriptor.
Check LeanCage_Host_NativeSpawn_ChannelEvidence.
