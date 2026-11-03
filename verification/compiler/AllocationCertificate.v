(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-compiled-reporting.certificate: The validator checks candidates against the actual RTL. *)
From compcert Require Import Errors.
Require Import OracleAllocation AllocationCandidates CandidateData FrontendCertificate.
Local Transparent ExecutableIteration.iterate CompilerPlatform.win64.
Definition oracle := allocation_candidates candidates.
Definition allocated_certificate :
 {allocated | OracleAllocation.transf_program oracle FrontendCertificate.rtl=Errors.OK allocated}.
Proof. eexists;vm_compute;reflexivity. Defined.
Definition allocated := proj1_sig allocated_certificate.
