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
Definition export_bad bytes := negb(bytes_equal bytes discard_bytes)&&negb(bytes_equal bytes files_bytes).
Lemma export_conditions_certificate cell R remaining e le m k argv ofs p bytes :
 e!_strcmp=None->e!___stringlit_133=None->e!___stringlit_132=None->le!_argv=Some(Vptr argv ofs)->
 Mem.loadv Mptr m(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 104)))=Some(address_value p)->
 c_string m p bytes->c_string m(literal_address ___stringlit_133)discard_bytes->
 c_string m(literal_address ___stringlit_132)files_bytes->
 (forall final,final!_t'18=Some(Val.of_bool(export_bad bytes))->validation_frame le final->
 region_certificate main_ge cell(fun after=>after=m)R remaining(State f_main Sskip k e final m))->
 region_certificate main_ge cell(fun after=>after=m)R(20+remaining)(State f_main export_conditions k e le m).
Proof.
 intros STRCMP DISCARD FILES ARGV LOAD OWN D F NEXT;unfold export_bad in NEXT.
 destruct(bytes_equal bytes discard_bytes)eqn:EQUAL;cbn[negb andb]in NEXT.
 - eapply region_weaken.
   + validation_unfold export_conditions;validation_route;validation_route;validation_next.
     * apply certified_set_edge;eapply validation_argv_value;[exact ARGV|lia|exact LOAD].
     * validation_route;eapply comparison_call_certificate with(bytes:=bytes)(literal:=discard_bytes);
       [exact STRCMP|exact DISCARD|unfold validation_literals;right;left;reflexivity|apply PTree.gss|exact OWN|exact D|].
       intros value EQ;validation_route;validation_next.
       -- eapply certified_if_edge with(v:=Vint value)(b:=false).
          ++ apply old_expression_value;apply value_temp;apply PTree.gss.
          ++ rewrite(strcmp_bool _ _ _ _ EQ),EQUAL;reflexivity.
       -- validation_next;[apply certified_set_edge;apply old_expression_value;apply value_int|].
          apply NEXT;[apply PTree.gss|validation_frame_auto].
   + lia.
 - eapply region_weaken.
   + validation_unfold export_conditions;validation_route;validation_route;validation_next.
     * apply certified_set_edge;eapply validation_argv_value;[exact ARGV|lia|exact LOAD].
     * validation_route;eapply comparison_call_certificate with(bytes:=bytes)(literal:=discard_bytes);
       [exact STRCMP|exact DISCARD|unfold validation_literals;right;left;reflexivity|apply PTree.gss|exact OWN|exact D|].
       intros value EQ;validation_route;validation_next.
       -- eapply certified_if_edge with(v:=Vint value)(b:=true).
          ++ apply old_expression_value;apply value_temp;apply PTree.gss.
          ++ rewrite(strcmp_bool _ _ _ _ EQ),EQUAL;reflexivity.
       -- validation_route;validation_route;validation_next.
          ++ apply certified_set_edge;eapply validation_argv_value;[WriteAll.lookup|lia|exact LOAD].
          ++ validation_route;eapply comparison_call_certificate with(bytes:=bytes)(literal:=files_bytes);
             [exact STRCMP|exact FILES|unfold validation_literals;right;right;left;reflexivity|apply PTree.gss|exact OWN|exact F|].
             intros value2 EQ2;validation_route;validation_next.
             ** apply certified_set_edge;eapply cast_expression_value;
                [apply old_expression_value;apply value_temp;apply PTree.gss|apply strcmp_cast;exact EQ2].
             ** apply NEXT;[apply PTree.gss|validation_frame_auto].
   + lia.
Qed.
Lemma export_check_certificate cell e le m k argv ofs p bytes :
 e!_strcmp=None->e!___stringlit_133=None->e!___stringlit_132=None->le!_argv=Some(Vptr argv ofs)->
 Mem.loadv Mptr m(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 104)))=Some(address_value p)->
 c_string m p bytes->c_string m(literal_address ___stringlit_133)discard_bytes->
 c_string m(literal_address ___stringlit_132)files_bytes->
 region_certificate main_ge cell(fun after=>after=m)(selection_frontier 16 e le k m(export_bad bytes))26
 (State f_main(validation_suffix 16)k e le m).
Proof.
 intros STRCMP DISCARD FILES ARGV LOAD OWN D F.
 change(validation_suffix 16)with(Ssequence export_check(selection_after 16));validation_route.
 change export_check with(Ssequence export_conditions(selection_finish 16));validation_route.
 eapply export_conditions_certificate;
 [exact STRCMP|exact DISCARD|exact FILES|exact ARGV|exact LOAD|exact OWN|exact D|exact F|].
 intros final RESULT FRAME;apply selection_finish_certificate with(result:=_t'18);
 [exact export_selection_shape|exact RESULT|exact FRAME].
Qed.
