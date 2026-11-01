(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.strings: Actual caller checks, owned bytes and explicit execution boundaries. *)
From Stdlib Require Import List ZArith Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Library LibraryMachine Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From LeanCageMainNumber Require Import NumberControl.
From LeanCageMain Require Import Main MainStructure.
From LeanCageArguments Require Import StringMachine StringPath.
From LeanCageDigest Require Import DigestWords DigestSource.
From LeanCageValidation Require Import StringRegion ValidationStructure ValidationMemory ValidationValues ValidationCalls.
Import ListNotations.
Open Scope nat_scope.
Definition option_bad bytes := negb(bytes_equal bytes none_bytes)&&negb(digest_valid bytes).
Lemma digest_tree_certificate cell R remaining e le m k p bytes :
 e!_strcmp=None->e!___stringlit_56=None->e!_tree_digest=None->e!_digest_text=None->
 Mem.loadv Mptr m(Vptr(symbol_block _tree_digest)Ptrofs.zero)=Some(address_value p)->
 c_string m p bytes->c_string m(literal_address ___stringlit_56)none_bytes->
 (forall final,final!_t'23=Some(Val.of_bool(option_bad bytes))->validation_frame le final->
 region_certificate main_ge cell(fun after=>after=m)R remaining(State f_main Sskip k e final m))->
 region_certificate main_ge cell(fun after=>after=m)R(2100+remaining)(State f_main digest_tree k e le m).
Proof.
 intros STRCMP LITERAL GLOBAL DIGEST LOAD OWN NONE NEXT.
 unfold option_bad in NEXT;destruct(bytes_equal bytes none_bytes)eqn:EQUAL;cbn[negb andb]in NEXT.
 - eapply region_weaken.
   + validation_unfold digest_tree;validation_route;validation_route;validation_next.
     * apply certified_set_edge;apply validation_global_pointer;[exact GLOBAL|reflexivity|exact LOAD].
     * validation_route.
       eapply comparison_call_certificate with(bytes:=bytes)(literal:=none_bytes);
       [exact STRCMP|exact LITERAL|unfold validation_literals;left;reflexivity|apply PTree.gss|exact OWN|exact NONE|].
       intros value EQ;validation_route;validation_next.
       -- eapply certified_if_edge with(v:=Vint value)(b:=false).
          ++ apply old_expression_value;apply value_temp;apply PTree.gss.
          ++ rewrite(strcmp_bool _ _ _ _ EQ),EQUAL;reflexivity.
       -- validation_next;[apply certified_set_edge;apply old_expression_value;apply value_int|].
          apply NEXT;[apply PTree.gss|validation_frame_auto].
   + lia.
 - eapply region_weaken.
   + validation_unfold digest_tree;validation_route;validation_route;validation_next.
     * apply certified_set_edge;apply validation_global_pointer;[exact GLOBAL|reflexivity|exact LOAD].
     * validation_route.
       eapply comparison_call_certificate with(bytes:=bytes)(literal:=none_bytes);
       [exact STRCMP|exact LITERAL|unfold validation_literals;left;reflexivity|apply PTree.gss|exact OWN|exact NONE|].
       intros value EQ;validation_route;validation_next.
       -- eapply certified_if_edge with(v:=Vint value)(b:=true).
          ++ apply old_expression_value;apply value_temp;apply PTree.gss.
          ++ rewrite(strcmp_bool _ _ _ _ EQ),EQUAL;reflexivity.
       -- validation_route;validation_route;validation_next.
          ++ apply certified_set_edge;apply validation_global_pointer;[exact GLOBAL|reflexivity|exact LOAD].
          ++ validation_route;eapply digest_invocation_certificate with(bytes:=bytes);
             [exact DIGEST|apply PTree.gss|exact OWN|].
             validation_route;validation_next.
             ** apply certified_set_edge;eapply cast_expression_value.
                --- apply old_expression_value;eapply value_unary;
                    [apply value_temp;apply PTree.gss|apply bool_negation].
                --- apply number_bool_cast.
             ** apply NEXT;[apply PTree.gss|validation_frame_auto].
   + lia.
Qed.
Lemma digest_stdin_certificate cell R remaining e le m k p bytes prior :
 e!_strcmp=None->e!___stringlit_56=None->e!_stdin_digest=None->e!_digest_text=None->
 le!_t'23=Some(Val.of_bool prior)->
 Mem.loadv Mptr m(Vptr(symbol_block _stdin_digest)Ptrofs.zero)=Some(address_value p)->
 c_string m p bytes->c_string m(literal_address ___stringlit_56)none_bytes->
 (forall final,final!_t'25=Some(Val.of_bool(prior||option_bad bytes))->validation_frame le final->
 region_certificate main_ge cell(fun after=>after=m)R remaining(State f_main Sskip k e final m))->
 region_certificate main_ge cell(fun after=>after=m)R(2110+remaining)(State f_main digest_stdin k e le m).
Proof.
 intros STRCMP LITERAL GLOBAL DIGEST PRIOR LOAD OWN NONE NEXT;destruct prior.
 - cbn[orb]in NEXT;eapply region_weaken.
   + validation_unfold digest_stdin;validation_next.
     * eapply certified_if_edge with(v:=Val.of_bool true)(b:=true);
       [apply old_expression_value;apply value_temp;exact PRIOR|reflexivity].
     * validation_next;[apply certified_set_edge;apply old_expression_value;apply value_int|].
       apply NEXT;[apply PTree.gss|validation_frame_auto].
   + lia.
 - cbn[orb]in NEXT;unfold option_bad in NEXT;destruct(bytes_equal bytes none_bytes)eqn:EQUAL;cbn[negb andb]in NEXT.
   + eapply region_weaken.
     * validation_unfold digest_stdin;validation_next.
       -- eapply certified_if_edge with(v:=Val.of_bool false)(b:=false);
          [apply old_expression_value;apply value_temp;exact PRIOR|reflexivity].
       -- validation_route;validation_route;validation_next.
          ++ apply certified_set_edge;apply validation_global_pointer;[exact GLOBAL|reflexivity|exact LOAD].
          ++ validation_route;eapply comparison_call_certificate with(bytes:=bytes)(literal:=none_bytes);
             [exact STRCMP|exact LITERAL|unfold validation_literals;left;reflexivity|apply PTree.gss|exact OWN|exact NONE|].
             intros value EQ;validation_route;validation_next.
             ** eapply certified_if_edge with(v:=Vint value)(b:=false).
                --- apply old_expression_value;apply value_temp;apply PTree.gss.
                --- rewrite(strcmp_bool _ _ _ _ EQ),EQUAL;reflexivity.
             ** validation_next;[apply certified_set_edge;eapply cast_expression_value;
                [apply old_expression_value;apply value_int|reflexivity]|].
                apply NEXT;[apply PTree.gss|validation_frame_auto].
     * lia.
   + eapply region_weaken.
     * validation_unfold digest_stdin;validation_next.
       -- eapply certified_if_edge with(v:=Val.of_bool false)(b:=false);
          [apply old_expression_value;apply value_temp;exact PRIOR|reflexivity].
       -- validation_route;validation_route;validation_next.
          ++ apply certified_set_edge;apply validation_global_pointer;[exact GLOBAL|reflexivity|exact LOAD].
          ++ validation_route;eapply comparison_call_certificate with(bytes:=bytes)(literal:=none_bytes);
             [exact STRCMP|exact LITERAL|unfold validation_literals;left;reflexivity|apply PTree.gss|exact OWN|exact NONE|].
             intros value EQ;validation_route;validation_next.
             ** eapply certified_if_edge with(v:=Vint value)(b:=true).
                --- apply old_expression_value;apply value_temp;apply PTree.gss.
                --- rewrite(strcmp_bool _ _ _ _ EQ),EQUAL;reflexivity.
             ** validation_route;validation_route;validation_route;validation_next.
                --- apply certified_set_edge;apply validation_global_pointer;[exact GLOBAL|reflexivity|exact LOAD].
                --- validation_route;eapply digest_invocation_certificate with(bytes:=bytes);
                    [exact DIGEST|apply PTree.gss|exact OWN|].
                    validation_route;validation_next.
                    +++ apply certified_set_edge;eapply cast_expression_value.
                        *** apply old_expression_value;eapply value_unary;
                            [apply value_temp;apply PTree.gss|apply bool_negation].
                        *** apply number_bool_cast.
                    +++ validation_route;validation_next.
                        *** apply certified_set_edge;eapply cast_expression_value;
                            [apply old_expression_value;apply value_temp;apply PTree.gss|apply number_bool_cast].
                        *** apply NEXT;[apply PTree.gss|validation_frame_auto].
     * lia.
Qed.
Definition digest_after := second_statement(validation_suffix 20).
Definition digest_pair_bad tree stdin := option_bad tree||option_bad stdin.
Definition digest_frontier e le k m tree stdin s := exists final,
 validation_frame le final /\
 s=if digest_pair_bad tree stdin then State f_main digest_report
 (Kseq digest_report_rest(Kseq digest_return(Kseq digest_after k)))e final m
 else State f_main digest_after k e final m.
Lemma digest_pair_certificate cell e le m k tree stdin tree_bytes stdin_bytes :
 e!_strcmp=None->e!___stringlit_56=None->e!_tree_digest=None->e!_stdin_digest=None->e!_digest_text=None->
 Mem.loadv Mptr m(Vptr(symbol_block _tree_digest)Ptrofs.zero)=Some(address_value tree)->
 Mem.loadv Mptr m(Vptr(symbol_block _stdin_digest)Ptrofs.zero)=Some(address_value stdin)->
 c_string m tree tree_bytes->c_string m stdin stdin_bytes->c_string m(literal_address ___stringlit_56)none_bytes->
 region_certificate main_ge cell(fun after=>after=m)(digest_frontier e le k m tree_bytes stdin_bytes)4300
 (State f_main(validation_suffix 20)k e le m).
Proof.
 intros STRCMP LITERAL TREE STDIN DIGEST TL SL TO SO NONE;eapply region_weaken.
 - change(validation_suffix 20)with(Ssequence digest_check digest_after);validation_route.
   change digest_check with(Ssequence(Ssequence digest_tree digest_stdin)digest_finish);validation_route;validation_route.
   eapply digest_tree_certificate;[exact STRCMP|exact LITERAL|exact TREE|exact DIGEST|exact TL|exact TO|exact NONE|].
   intros mid RESULT FRAME;validation_route.
   eapply digest_stdin_certificate with(remaining:=4);[exact STRCMP|exact LITERAL|exact STDIN|exact DIGEST|exact RESULT|exact SL|exact SO|exact NONE|].
   intros final BOTH MORE;validation_route.
   change digest_finish with(Sifthenelse(Etempvar _t'25 tint)digest_failure Sskip).
   destruct(digest_pair_bad tree_bytes stdin_bytes)eqn:BAD.
   + validation_next.
     * eapply certified_if_edge with(v:=Val.of_bool true)(b:=true).
       -- apply old_expression_value;apply value_temp;change(option_bad tree_bytes||option_bad stdin_bytes)with(digest_pair_bad tree_bytes stdin_bytes)in BOTH;rewrite BAD in BOTH;exact BOTH.
       -- reflexivity.
     * change digest_failure with(Ssequence(Ssequence digest_report digest_report_rest)digest_return);validation_route;validation_route.
       apply region_stop;[reflexivity|].
       exists final;split;[eapply validation_frame_trans;eassumption|rewrite BAD;reflexivity].
   + validation_next.
     * eapply certified_if_edge with(v:=Val.of_bool false)(b:=false).
       -- apply old_expression_value;apply value_temp;change(option_bad tree_bytes||option_bad stdin_bytes)with(digest_pair_bad tree_bytes stdin_bytes)in BOTH;rewrite BAD in BOTH;exact BOTH.
       -- reflexivity.
     * validation_route;apply region_stop;[reflexivity|].
       exists final;split;[eapply validation_frame_trans;eassumption|rewrite BAD;reflexivity].
 - lia.
Qed.
From LeanCageValidation Require Import ValidationFinish.
Lemma digest_tree_rejection_without_stdin cell e le m k p bytes :
 e!_strcmp=None->e!___stringlit_56=None->e!_tree_digest=None->e!_digest_text=None->
 Mem.loadv Mptr m(Vptr(symbol_block _tree_digest)Ptrofs.zero)=Some(address_value p)->
 c_string m p bytes->c_string m(literal_address ___stringlit_56)none_bytes->option_bad bytes=true->
 region_certificate main_ge cell(fun after=>after=m)(selection_frontier 20 e le k m true)2120
 (State f_main(validation_suffix 20)k e le m).
Proof.
 intros STRCMP LITERAL TREE DIGEST LOAD OWN NONE BAD;eapply region_weaken.
 - change(validation_suffix 20)with(Ssequence digest_check(selection_after 20));validation_route.
   change digest_check with(Ssequence(Ssequence digest_tree digest_stdin)(selection_finish 20));validation_route;validation_route.
   eapply digest_tree_certificate;[exact STRCMP|exact LITERAL|exact TREE|exact DIGEST|exact LOAD|exact OWN|exact NONE|].
   intros mid RESULT FRAME;validation_route;validation_unfold digest_stdin;validation_next.
   + eapply certified_if_edge with(v:=Val.of_bool true)(b:=true).
     * apply old_expression_value;apply value_temp;rewrite BAD in RESULT;exact RESULT.
     * reflexivity.
   + validation_next;[apply certified_set_edge;apply old_expression_value;apply value_int|].
     apply selection_finish_certificate with(result:=_t'25);[exact digest_selection_shape|apply PTree.gss|].
     eapply validation_frame_trans;[exact FRAME|validation_frame_auto].
 - lia.
Qed.
