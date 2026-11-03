(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-compiled-reporting.certificate: Check code generation after validated allocation. *)
From compcert Require Import Errors Linearize Stacking Asmgen Compopts.
Require Import AllocationCertificate.
Local Transparent ExecutableIteration.iterate CompilerPlatform.win64 Compopts.debug Linearize.enumerate_aux.
Definition linear_certificate : {linear | Linearize.transf_program allocated=Errors.OK linear}.
Proof. eexists;vm_compute;reflexivity. Defined.
Definition linear := proj1_sig linear_certificate.
Definition stacked_certificate : {stacked | Stacking.transf_program linear=Errors.OK stacked}.
Proof. eexists;vm_compute;reflexivity. Defined.
Definition stacked := proj1_sig stacked_certificate.
Definition assembly_certificate : {assembly | Asmgen.transf_program stacked=Errors.OK assembly}.
Proof. eexists;vm_compute;reflexivity. Defined.
Definition assembly := proj1_sig assembly_certificate.
