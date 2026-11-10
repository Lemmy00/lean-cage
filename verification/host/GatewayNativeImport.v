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
Check LeanCage_Host_ChannelCode_PairKind.
Check LeanCage_Host_ChannelCode_Invocation.
Check LeanCage_Host_ChannelCode_Invocation_WellFormed.
Check LeanCage_Host_ChannelCode_Invocation_storage.
Check LeanCage_Host_ChannelCode_ReferenceAt.
Check LeanCage_Host_ChannelCode_PairUse.
Check LeanCage_Host_ChannelCode_PairUse_Consistent.
Check LeanCage_Host_ChannelCode_ReceiveUse.
Check LeanCage_Host_ChannelCode_ReceiveUse_Consistent.
