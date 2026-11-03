(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-compiled-reporting.certificate: Untrusted candidates must pass the kernel's replay. *)
let checked = function
 | Errors.OK value -> value
 | Errors.Error message ->
   Format.eprintf "Compiler candidate failed: %a@." Driveraux.print_error message;
   exit 1

let () =
 Camlcoq.use_canonical_atoms := true;
 Clflags.option_fstruct_passing := true;
 Clflags.option_Osize := false;
 Clflags.option_ffloatconstprop := 0;
 Clflags.option_ftailcalls := false;
 Clflags.option_fconstprop := false;
 Clflags.option_fcse := false;
 Clflags.option_fredundancy := false;
 Clflags.option_g := false;
 Frontend.init ();
 let source = Frontend.parse_c_file "native/leancage_m3.c" Sys.argv.(1) in
 let source = Clightnorm.norm_program
   (checked (SimplLocals.transf_program (checked (SimplExpr.transl_program source)))) in
 let sharp = checked (Cshmgen.transl_program source) in
 let minor = checked (Cminorgen.transl_program sharp) in
 let selected = checked (ReplaySelection.sel_program minor) in
 let rtl = checked (ReplayRTLgen.transl_program selected) in
 let used = rtl in
 let candidates = List.filter_map (function
   | (_,AST.Gfun(AST.Internal f)) -> Some (f, checked (Allocation.transf_function f))
   | _ -> None) used.AST.prog_defs in
 QuoteLTL.write Sys.argv.(2) candidates;
 let allocated = checked (Allocation.transf_program used) in
 let linear = checked (ReplayLinearize.transf_program allocated) in
 let stacked = checked (Stacking.transf_program linear) in
 let assembly = checked (Asmgen.transf_program stacked) in
 let expanded = checked (Asmexpand.expand_program assembly) in
 let output = open_out Sys.argv.(3) in
 PrintAsm.print_program output expanded;
 close_out output
