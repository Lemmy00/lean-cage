(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-reporting.proof: Recheck the ordinary publication proof under the strict importer. *)
From LeanImport Require Import Lean.
Require Import NormalizedImport.
Set Lean Error Mode "Fail".
Unset Lean Skip Missing Quotient.
Unset Lean Just Parsing.
Set Lean Line Timeout 10.
Lean Import "../publication-extension.ndjson".
Check LeanCage_Reporting_normalized_publication.
Print Assumptions LeanCage_Reporting_normalized_publication.
