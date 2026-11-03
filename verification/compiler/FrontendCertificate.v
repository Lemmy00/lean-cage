(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-compiled-reporting.certificate: Preserve checked frontend results for the actual program. *)
From Stdlib Require Import List ZArith.
From compcert Require Import Errors Cshmgen Cminorgen Selection RTLgen Compopts SelectOp.
Require Import RuntimeProgram.
Local Transparent Compopts.optim_for_size Compopts.propagate_float_constants
 Compopts.generate_float_constants Compopts.va_strict Compopts.optim_tailcalls
 Compopts.optim_constprop Compopts.optim_CSE Compopts.optim_redundancy Compopts.thumb Compopts.debug
 SelectOp.symbol_is_relocatable Selection.compile_switch Selection.if_conversion_heuristic
 RTLgen.more_likely.

Definition sharp_certificate : {sharp | Cshmgen.transl_program RuntimeProgram.program=Errors.OK sharp}.
Proof. eexists;vm_compute;reflexivity. Defined.
Definition sharp := proj1_sig sharp_certificate.
Definition minor_certificate : {minor | Cminorgen.transl_program sharp=Errors.OK minor}.
Proof. eexists;vm_compute;reflexivity. Defined.
Definition minor := proj1_sig minor_certificate.
Definition selected_certificate : {selected | Selection.sel_program minor=Errors.OK selected}.
Proof. eexists;vm_compute;reflexivity. Defined.
Definition selected := proj1_sig selected_certificate.
Definition rtl_certificate : {rtl | RTLgen.transl_program selected=Errors.OK rtl}.
Proof. eexists;vm_compute;reflexivity. Defined.
Definition rtl := proj1_sig rtl_certificate.
