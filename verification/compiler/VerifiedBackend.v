(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* Adapted from driver/Compiler.v in the pinned CompCert 3.17 source.
   The upstream notice and non-commercial license above apply to this proof.
   §AR-compiled-reporting.certificate: Check the Clight2 backend with explicit allocation choices. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Errors Smallstep Linking.
From compcert Require Cshmgen Cminorgen Selection RTLgen
 Linearize Stacking Asmgen.
From compcert Require Cshmgenproof Cminorgenproof Selectionproof RTLgenproof
 Linearizeproof
 Stackingproof Asmgenproof Asmgenproof0 Clight Asm RTL LTL.
Require Import OracleAllocation.
Local Open Scope linking_scope.
Local Open Scope error_monad_scope.

Definition backend_passes (oracle : RTL.function -> res LTL.function) :=
  mkpass (Cshmgenproof.match_prog)
  ::: mkpass (Cminorgenproof.match_prog)
  ::: mkpass (Selectionproof.match_prog)
  ::: mkpass (RTLgenproof.match_prog)
  ::: mkpass (OracleAllocation.match_prog oracle)
  ::: mkpass (Linearizeproof.match_prog)
  ::: mkpass (Stackingproof.match_prog)
  ::: mkpass (Asmgenproof.match_prog)
  ::: pass_nil _.

Definition backend_match oracle (source : Clight.program) (assembly : Asm.program) :=
 pass_match (compose_passes (backend_passes oracle)) source assembly.

Definition compile oracle (source : Clight.program) : res Asm.program :=
 do sharp <- Cshmgen.transl_program source;
 do minor <- Cminorgen.transl_program sharp;
 do selected <- Selection.sel_program minor;
 do rtl <- RTLgen.transl_program selected;
 do allocated <- OracleAllocation.transf_program oracle rtl;
 do linear <- Linearize.transf_program allocated;
 do stacked <- Stacking.transf_program linear;
 Asmgen.transf_program stacked.

Theorem backend_semantic_preservation oracle source assembly :
 backend_match oracle source assembly ->
 forward_simulation (Clight.semantics2 source) (Asm.semantics assembly).
Proof.
 intros MATCH;unfold backend_match,pass_match in MATCH;simpl in MATCH.
 repeat match goal with H:exists p,_ /\ _|-_=>destruct H as[?[? ?]] end.
 subst assembly.
 eapply compose_forward_simulations.
  eapply Cshmgenproof.transl_program_correct;eassumption.
 eapply compose_forward_simulations.
  eapply Cminorgenproof.transl_program_correct;eassumption.
 eapply compose_forward_simulations.
  eapply Selectionproof.transf_program_correct;eassumption.
 eapply compose_forward_simulations.
  eapply RTLgenproof.transf_program_correct;eassumption.
 eapply compose_forward_simulations.
  eapply OracleAllocation.transf_program_correct;eassumption.
 eapply compose_forward_simulations.
  eapply Linearizeproof.transf_program_correct;eassumption.
 eapply compose_forward_simulations.
  eapply Stackingproof.transf_program_correct with
    (return_address_offset:=Asmgenproof0.return_address_offset);
    [exact Asmgenproof.return_address_exists|eassumption].
 eapply Asmgenproof.transf_program_correct;eassumption.
Qed.

Theorem compile_match oracle source assembly :
 compile oracle source=OK assembly -> backend_match oracle source assembly.
Proof.
 unfold compile;intro COMPILE.
 destruct(Cshmgen.transl_program source)as[sharp|error]eqn:SHARP;cbn in COMPILE;try discriminate.
 destruct(Cminorgen.transl_program sharp)as[minor|error]eqn:MINOR;cbn in COMPILE;try discriminate.
 destruct(Selection.sel_program minor)as[selected|error]eqn:SELECTED;cbn in COMPILE;try discriminate.
 destruct(RTLgen.transl_program selected)as[rtl|error]eqn:RTL;cbn in COMPILE;try discriminate.
 destruct(OracleAllocation.transf_program oracle rtl)as[allocated|error]eqn:ALLOCATED;cbn in COMPILE;try discriminate.
 destruct(Linearize.transf_program allocated)as[linear|error]eqn:LINEAR;cbn in COMPILE;try discriminate.
 destruct(Stacking.transf_program linear)as[stacked|error]eqn:STACKED;cbn in COMPILE;try discriminate.
 unfold backend_match,pass_match;cbn.
 exists sharp;split;[apply Cshmgenproof.transf_program_match;exact SHARP|].
 exists minor;split;[apply Cminorgenproof.transf_program_match;exact MINOR|].
 exists selected;split;[apply Selectionproof.transf_program_match;exact SELECTED|].
 exists rtl;split;[apply RTLgenproof.transf_program_match;exact RTL|].
 exists allocated;split;[apply OracleAllocation.transf_program_match;exact ALLOCATED|].
 exists linear;split;[apply Linearizeproof.transf_program_match;exact LINEAR|].
 exists stacked;split;[apply Stackingproof.transf_program_match;exact STACKED|].
 exists assembly;split;[apply Asmgenproof.transf_program_match;exact COMPILE|reflexivity].
Qed.
