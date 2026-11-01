(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.strings: Actual caller checks, owned bytes and explicit execution boundaries. *)
From Stdlib Require Import List ZArith Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Library Machine ClightSteps.
From LeanCageMain Require Import Main MainStructure.
From LeanCageBounds Require Import BoundsMemory.
From LeanCageArguments Require Import StringMachine StringPath ArgumentStructure ArgumentMemory ArgumentBounds.
From LeanCageValidation Require Import StringRegion ValidationStructure ValidationValues ValidationFinish ExecutableCaller.
Import ListNotations.
Open Scope nat_scope.
Definition executable_bounds_frontier e le k m argc x rest values s :=
 if executable_bad(guest_bytes x) then selection_frontier 22 e le k m true s
 else exists final,s=argument_bounds_endpoint argc(x::rest)values e final k m.
Theorem executable_bounds_certificate cell e le m k argc argv ofs x rest values :
 (17<=argc<=2147483647)%Z->(16+Z.of_nat(length(x::rest))=argc)%Z->guest_table_span ofs argc->
 guest_arguments_owned m argv ofs 16(x::rest)->policy_image m values->
 e!_strcmp=None->e!_strlen=None->e!_policy__1=None->e!___stringlit_135=None->e!___stringlit_134=None->
 le!_argv=Some(Vptr argv ofs)->le!_argc=Some(Vint(Int.repr argc))->
 Mem.loadv Mptr m(Vptr main_policy_block(Ptrofs.repr 88))=Some(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 128)))->
 c_string m(literal_address ___stringlit_135)shell_bytes->c_string m(literal_address ___stringlit_134)python_bytes->
 region_certificate main_ge cell(fun after=>after=m)(executable_bounds_frontier e le k m argc x rest values)
 (34+(26*length(x::rest)+154))(State f_main(validation_suffix 22)k e le m).
Proof.
 intros COUNT SIZE SPAN OWN IMAGE STRCMP STRLEN POLICY SHELL PYTHON ARGV ARGC ARGS S P.
 pose proof OWN as[TEXT[LOAD REST]].
 eapply region_bind with(R:=selection_frontier 22 e le k m(executable_bad(guest_bytes x))).
 - eapply executable_check_certificate;[exact STRCMP|exact SHELL|exact PYTHON|exact POLICY|exact ARGS|exact LOAD|exact TEXT|exact S|exact P].
 - intros endpoint[intermediate[FRAME END]].
   unfold executable_bounds_frontier;destruct(executable_bad(guest_bytes x))eqn:BAD.
   + apply region_stop;[rewrite END;reflexivity|exists intermediate;auto].
   + subst endpoint;change(selection_after 22)with argument_suffix.
     destruct FRAME as[AV AC].
     destruct(argument_bounds_source cell m argv ofs argc(x::rest)values e intermediate k
      COUNT SIZE SPAN OWN STRLEN POLICY IMAGE ltac:(rewrite AV;exact ARGV)ltac:(rewrite AC;exact ARGC))
      as[count[final[BOUND PATH]]].
     eapply region_weaken;[|exact BOUND].
     replace count with(count+0)at 1 by lia.
     eapply region_string_path;[exact PATH|reflexivity|apply region_stop;[exact(string_path_memory _ _ _ _ _ PATH)|eexists;reflexivity]].
Qed.
