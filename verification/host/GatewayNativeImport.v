(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: All native-event data crosses the strict kernel boundary. *)
From LeanImport Require Import Lean.
Set Lean Error Mode "Fail".
Unset Lean Skip Missing Quotient.
Unset Lean Just Parsing.
Set Lean Line Timeout 10.
Lean Import "native-code.ndjson".
Check LeanCage_Host_NativeCode_Operation.
Check LeanCage_Host_NativeCode_Product.
Check LeanCage_Host_NativeCode_Reply.
Check LeanCage_Host_NativeCode_References.
Check LeanCage_Host_NativeCode_Credentials.
