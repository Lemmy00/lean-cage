(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.strings: Actual caller checks, owned bytes and explicit execution boundaries. *)
From Stdlib Require Import List ZArith Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Library LibraryMachine Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From LeanCageMainNumber Require Import NumberControl.
From LeanCageMain Require Import Main MainStructure.
From LeanCageArguments Require Import StringMachine StringPath.
From LeanCageValidation Require Import StringRegion ValidationStructure ValidationMemory ValidationValues ValidationCalls ValidationFinish.
Import ListNotations.
Open Scope nat_scope.
Definition executable_bad bytes := negb(bytes_equal bytes shell_bytes)&&negb(bytes_equal bytes python_bytes).
Lemma executable_conditions_certificate cell R remaining e le m k argv ofs p bytes :
 e!_strcmp=None->e!___stringlit_135=None->e!___stringlit_134=None->e!_policy__1=None->
 Mem.loadv Mptr m(Vptr main_policy_block(Ptrofs.repr 88))=Some(Vptr argv ofs)->
 Mem.loadv Mptr m(Vptr argv ofs)=Some(address_value p)->
 c_string m p bytes->c_string m(literal_address ___stringlit_135)shell_bytes->
 c_string m(literal_address ___stringlit_134)python_bytes->
 (forall final,final!_t'30=Some(Val.of_bool(executable_bad bytes))->validation_frame le final->
 region_certificate main_ge cell(fun after=>after=m)R remaining(State f_main Sskip k e final m))->
 region_certificate main_ge cell(fun after=>after=m)R(28+remaining)(State f_main executable_conditions k e le m).
Proof.
 intros STRCMP SHELL PYTHON GLOBAL ARGS LOAD OWN D F NEXT;unfold executable_bad in NEXT.
 destruct(bytes_equal bytes shell_bytes)eqn:EQUAL;cbn[negb andb]in NEXT.
 - eapply region_weaken.
   + validation_unfold executable_conditions;validation_route;validation_route;validation_next.
     * apply certified_set_edge;apply policy_arguments_value;[exact GLOBAL|exact ARGS].
     * validation_route;validation_route;validation_next.
       { apply certified_set_edge;eapply executable_pointer_value;[apply PTree.gss|exact LOAD]. }
       validation_route;eapply comparison_call_certificate with(bytes:=bytes)(literal:=shell_bytes);
       [exact STRCMP|exact SHELL|unfold validation_literals;right;right;right;left;reflexivity|apply PTree.gss|exact OWN|exact D|].
       intros value EQ;validation_route;validation_next.
       -- eapply certified_if_edge with(v:=Vint value)(b:=false).
          ++ apply old_expression_value;apply value_temp;apply PTree.gss.
          ++ rewrite(strcmp_bool _ _ _ _ EQ),EQUAL;reflexivity.
       -- validation_next;[apply certified_set_edge;apply old_expression_value;apply value_int|].
          apply NEXT;[apply PTree.gss|validation_frame_auto].
   + lia.
 - eapply region_weaken.
   + validation_unfold executable_conditions;validation_route;validation_route;validation_next.
     * apply certified_set_edge;apply policy_arguments_value;[exact GLOBAL|exact ARGS].
     * validation_route;validation_route;validation_next.
       { apply certified_set_edge;eapply executable_pointer_value;[apply PTree.gss|exact LOAD]. }
       validation_route;eapply comparison_call_certificate with(bytes:=bytes)(literal:=shell_bytes);
       [exact STRCMP|exact SHELL|unfold validation_literals;right;right;right;left;reflexivity|apply PTree.gss|exact OWN|exact D|].
       intros value EQ;validation_route;validation_next.
       -- eapply certified_if_edge with(v:=Vint value)(b:=true).
          ++ apply old_expression_value;apply value_temp;apply PTree.gss.
          ++ rewrite(strcmp_bool _ _ _ _ EQ),EQUAL;reflexivity.
       -- validation_route;validation_route;validation_next.
          ++ apply certified_set_edge;apply policy_arguments_value;[exact GLOBAL|exact ARGS].
          ++ validation_route;validation_route;validation_next.
             { apply certified_set_edge;eapply executable_pointer_value;[apply PTree.gss|exact LOAD]. }
             validation_route;eapply comparison_call_certificate with(bytes:=bytes)(literal:=python_bytes);
             [exact STRCMP|exact PYTHON|unfold validation_literals;right;right;right;right;left;reflexivity|apply PTree.gss|exact OWN|exact F|].
             intros value2 EQ2;validation_route;validation_next.
             ** apply certified_set_edge;eapply cast_expression_value;
                [apply old_expression_value;apply value_temp;apply PTree.gss|apply strcmp_cast;exact EQ2].
             ** apply NEXT;[apply PTree.gss|validation_frame_auto].
   + lia.
Qed.
Lemma executable_check_certificate cell e le m k argv ofs p bytes :
 e!_strcmp=None->e!___stringlit_135=None->e!___stringlit_134=None->e!_policy__1=None->
 Mem.loadv Mptr m(Vptr main_policy_block(Ptrofs.repr 88))=Some(Vptr argv ofs)->
 Mem.loadv Mptr m(Vptr argv ofs)=Some(address_value p)->
 c_string m p bytes->c_string m(literal_address ___stringlit_135)shell_bytes->
 c_string m(literal_address ___stringlit_134)python_bytes->
 region_certificate main_ge cell(fun after=>after=m)(selection_frontier 22 e le k m(executable_bad bytes))34
 (State f_main(validation_suffix 22)k e le m).
Proof.
 intros STRCMP SHELL PYTHON GLOBAL ARGS LOAD OWN D F.
 change(validation_suffix 22)with(Ssequence executable_check(selection_after 22));validation_route.
 change executable_check with(Ssequence executable_conditions(selection_finish 22));validation_route.
 eapply executable_conditions_certificate;
 [exact STRCMP|exact SHELL|exact PYTHON|exact GLOBAL|exact ARGS|exact LOAD|exact OWN|exact D|exact F|].
 intros final RESULT FRAME;apply selection_finish_certificate with(result:=_t'30);
 [exact executable_selection_shape|exact RESULT|exact FRAME].
Qed.
