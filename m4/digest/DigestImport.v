(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.digest: Strict import of the exact digest-byte computation. *)
From LeanImport Require Import Lean.
Set Lean Error Mode "Fail".
Unset Lean Skip Missing Quotient.
Unset Lean Just Parsing.
Set Lean Line Timeout 10.
Lean Import "../digest.ndjson".
Check LeanCageM4_Digest_nativeDigestBytes.
Print Assumptions LeanCageM4_Digest_nativeDigestBytes.
