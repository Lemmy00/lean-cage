(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-compiled-reporting.certificate: The compiler output consumes the existing reporting argument. *)
From compcert Require Import Errors.
Require Import RuntimeProgram FrontendCertificate AllocationCertificate AssemblyCertificate
 VerifiedBackend CompiledReporting.
Local Close Scope lean_scope.
Local Opaque FrontendCertificate.sharp_certificate FrontendCertificate.minor_certificate
 FrontendCertificate.selected_certificate FrontendCertificate.rtl_certificate
 AllocationCertificate.allocated_certificate AssemblyCertificate.linear_certificate
 AssemblyCertificate.stacked_certificate AssemblyCertificate.assembly_certificate.

Theorem current_compilation : compile oracle RuntimeProgram.program=Errors.OK assembly.
Proof.
 unfold compile.
 rewrite(proj2_sig sharp_certificate);cbn [Errors.bind];fold FrontendCertificate.sharp.
 rewrite(proj2_sig minor_certificate);cbn [Errors.bind];fold FrontendCertificate.minor.
 rewrite(proj2_sig selected_certificate);cbn [Errors.bind];fold FrontendCertificate.selected.
 rewrite(proj2_sig rtl_certificate);cbn [Errors.bind];fold FrontendCertificate.rtl.
 rewrite(proj2_sig allocated_certificate);cbn [Errors.bind];fold AllocationCertificate.allocated.
 rewrite(proj2_sig linear_certificate);cbn [Errors.bind];fold AssemblyCertificate.linear.
 rewrite(proj2_sig stacked_certificate);cbn [Errors.bind];fold AssemblyCertificate.stacked.
 rewrite(proj2_sig assembly_certificate).
 reflexivity.
Qed.

Theorem current_assembly_reporting :
 exists index order matches,
 Smallstep.fsim_properties(Clight.semantics2 RuntimeProgram.program)(Asm.semantics assembly)index order matches /\
 compiled_reporting_contract assembly index matches.
Proof.
 apply(current_reporting_backend oracle assembly).
 apply compile_match;exact current_compilation.
Qed.
