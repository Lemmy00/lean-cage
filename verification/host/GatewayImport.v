(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Strictly import the executable native bound and slot selectors. *)
From LeanImport Require Import Lean.
Set Lean Error Mode "Fail".
Unset Lean Skip Missing Quotient.
Unset Lean Just Parsing.
Set Lean Line Timeout 10.
Lean Import "gateway-code.ndjson".
Check LeanCage_Host_GatewayChecks_bounded.
Check LeanCage_Host_GatewayChecks_slotMaximum.
Check LeanCage_Host_GatewayWords_encode.
Check LeanCage_Host_GatewayWords_decode.
Check LeanCage_Host_GatewayWords_Encoding.
Check LeanCage_Host_GatewayRequestCode_Field.
Check LeanCage_Host_GatewayRequestCode_Request.
Check LeanCage_Host_GatewayRequestCode_magic.
Check LeanCage_Host_GatewayRequestCode_headerPrefix.
Check LeanCage_Host_GatewayRequestCode_descriptor.
Check LeanCage_Host_GatewayRequestCode_encode.
Check LeanCage_Host_GatewayResponseCode_Value.
Check LeanCage_Host_GatewayResponseCode_Subject.
Check LeanCage_Host_GatewayResponseCode_Encoded.
Check LeanCage_Host_GatewayResponseCode_Encoding.
Check LeanCage_Host_GatewayResponseCode_magic.
Check LeanCage_Host_GatewayResponseCode_ResponseEncoding.
Check LeanCage_Host_GatewayResponseWords_SourceEncoded.
Check LeanCage_Host_GatewayResponseWords_SourceResponseEncoding.
