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
Definition mode_bytes_bad bytes := negb(bytes_equal bytes plan_bytes)&&negb(bytes_equal bytes check_bytes).
Definition mode_bad argc bytes := (argc<?17)%Z||mode_bytes_bad bytes.
Lemma mode_count_expression e le m argc : (Int.min_signed<=argc<=Int.max_signed)%Z->
 le!_argc=Some(Vint(Int.repr argc))->
 expression_value main_ge e le m
 (Ebinop Olt(Etempvar _argc tint)(Econst_int(Int.repr 17)tint)tint)(Val.of_bool(argc<?17)%Z).
Proof.
 intros RANGE REG;eapply binary_expression_value;
 [apply old_expression_value;apply value_temp;exact REG|apply old_expression_value;apply value_int|].
 change(Some(Val.of_bool(Int.lt(Int.repr argc)(Int.repr 17)))=Some(Val.of_bool(argc<?17)%Z)).
 unfold Int.lt;rewrite Int.signed_repr by exact RANGE;change(Int.signed(Int.repr 17))with 17%Z.
 destruct(zlt argc 17);destruct(argc<?17)%Z eqn:LT;try reflexivity;
 apply Z.ltb_lt in LT||apply Z.ltb_ge in LT;lia.
Qed.
Lemma mode_pair_certificate cell R remaining e le m k argv ofs p bytes :
 e!_strcmp=None->e!___stringlit_131=None->e!___stringlit_130=None->le!_argv=Some(Vptr argv ofs)->
 Mem.loadv Mptr m(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 8)))=Some(address_value p)->
 c_string m p bytes->c_string m(literal_address ___stringlit_131)plan_bytes->
 c_string m(literal_address ___stringlit_130)check_bytes->
 (forall final,final!_t'4=Some(Val.of_bool(mode_bytes_bad bytes))->validation_frame le final->
 region_certificate main_ge cell(fun after=>after=m)R remaining(State f_main Sskip k e final m))->
 region_certificate main_ge cell(fun after=>after=m)R(24+remaining)(State f_main mode_pair k e le m).
Proof.
 intros STRCMP PLAN CHECK ARGV LOAD OWN P C NEXT;unfold mode_bytes_bad in NEXT.
 destruct(bytes_equal bytes plan_bytes)eqn:EQUAL;cbn[negb andb]in NEXT.
 - eapply region_weaken.
   + mode_unfold;validation_route;validation_route;validation_next.
     * apply certified_set_edge;eapply validation_argv_value;[exact ARGV|lia|exact LOAD].
     * validation_route;eapply comparison_call_certificate with(bytes:=bytes)(literal:=plan_bytes);
       [exact STRCMP|exact PLAN|unfold validation_literals;do 5 right;left;reflexivity|apply PTree.gss|exact OWN|exact P|].
       intros value EQ;validation_route;validation_next.
       -- eapply certified_if_edge with(v:=Vint value)(b:=false).
          ++ apply old_expression_value;apply value_temp;apply PTree.gss.
          ++ rewrite(strcmp_bool _ _ _ _ EQ),EQUAL;reflexivity.
       -- validation_next;[apply certified_set_edge;eapply cast_expression_value;
          [apply old_expression_value;apply value_int|reflexivity]|].
          apply NEXT;[apply PTree.gss|validation_frame_auto].
   + lia.
 - eapply region_weaken.
   + mode_unfold;validation_route;validation_route;validation_next.
     * apply certified_set_edge;eapply validation_argv_value;[exact ARGV|lia|exact LOAD].
     * validation_route;eapply comparison_call_certificate with(bytes:=bytes)(literal:=plan_bytes);
       [exact STRCMP|exact PLAN|unfold validation_literals;do 5 right;left;reflexivity|apply PTree.gss|exact OWN|exact P|].
       intros value EQ;validation_route;validation_next.
       -- eapply certified_if_edge with(v:=Vint value)(b:=true).
          ++ apply old_expression_value;apply value_temp;apply PTree.gss.
          ++ rewrite(strcmp_bool _ _ _ _ EQ),EQUAL;reflexivity.
       -- validation_route;validation_route;validation_route;validation_next.
          ++ apply certified_set_edge;eapply validation_argv_value;[WriteAll.lookup|lia|exact LOAD].
          ++ validation_route;eapply comparison_call_certificate with(bytes:=bytes)(literal:=check_bytes);
             [exact STRCMP|exact CHECK|unfold validation_literals;do 6 right;left;reflexivity|apply PTree.gss|exact OWN|exact C|].
             intros value2 EQ2;validation_route;validation_next.
             ** apply certified_set_edge;eapply cast_expression_value;
                [apply old_expression_value;apply value_temp;apply PTree.gss|apply strcmp_cast;exact EQ2].
             ** validation_route;validation_next.
                --- apply certified_set_edge;eapply cast_expression_value;
                    [apply old_expression_value;apply value_temp;apply PTree.gss|apply number_bool_cast].
                --- apply NEXT;[apply PTree.gss|validation_frame_auto].
   + lia.
Qed.
Lemma mode_conditions_certificate cell R remaining e le m k argc argv ofs p bytes :
 (Int.min_signed<=argc<=Int.max_signed)%Z->le!_argc=Some(Vint(Int.repr argc))->
 e!_strcmp=None->e!___stringlit_131=None->e!___stringlit_130=None->le!_argv=Some(Vptr argv ofs)->
 Mem.loadv Mptr m(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 8)))=Some(address_value p)->
 c_string m p bytes->c_string m(literal_address ___stringlit_131)plan_bytes->
 c_string m(literal_address ___stringlit_130)check_bytes->
 (forall final,final!_t'4=Some(Val.of_bool(mode_bad argc bytes))->validation_frame le final->
 region_certificate main_ge cell(fun after=>after=m)R remaining(State f_main Sskip k e final m))->
 region_certificate main_ge cell(fun after=>after=m)R(25+remaining)(State f_main mode_conditions k e le m).
Proof.
 intros RANGE ARGC STRCMP PLAN CHECK ARGV LOAD OWN P C NEXT;rewrite mode_condition_structure.
 unfold mode_bad in NEXT;destruct(argc<?17)%Z eqn:SHORT;cbn[orb]in NEXT.
 - eapply region_weaken.
   + validation_next.
     * eapply certified_if_edge with(v:=Val.of_bool(argc<?17)%Z)(b:=true);
       [apply mode_count_expression;assumption|rewrite number_bool_value,SHORT;reflexivity].
     * validation_next;[apply certified_set_edge;apply old_expression_value;apply value_int|].
       apply NEXT;[apply PTree.gss|validation_frame_auto].
   + lia.
 - validation_next.
   + eapply certified_if_edge with(v:=Val.of_bool(argc<?17)%Z)(b:=false);
     [apply mode_count_expression;assumption|rewrite number_bool_value,SHORT;reflexivity].
   + eapply mode_pair_certificate;eassumption.
Qed.
Lemma mode_check_certificate cell e le m k argc argv ofs p bytes :
 (Int.min_signed<=argc<=Int.max_signed)%Z->le!_argc=Some(Vint(Int.repr argc))->
 e!_strcmp=None->e!___stringlit_131=None->e!___stringlit_130=None->le!_argv=Some(Vptr argv ofs)->
 Mem.loadv Mptr m(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 8)))=Some(address_value p)->
 c_string m p bytes->c_string m(literal_address ___stringlit_131)plan_bytes->
 c_string m(literal_address ___stringlit_130)check_bytes->
 region_certificate main_ge cell(fun after=>after=m)(selection_frontier 2 e le k m(mode_bad argc bytes))31
 (State f_main(validation_suffix 2)k e le m).
Proof.
 intros RANGE ARGC STRCMP PLAN CHECK ARGV LOAD OWN P C.
 change(validation_suffix 2)with(Ssequence(selection_check 2)(selection_after 2));validation_route.
 change(selection_check 2)with(Ssequence mode_conditions(selection_finish 2));validation_route.
 eapply mode_conditions_certificate;
 [exact RANGE|exact ARGC|exact STRCMP|exact PLAN|exact CHECK|exact ARGV|exact LOAD|exact OWN|exact P|exact C|].
 intros final RESULT FRAME;apply selection_finish_certificate with(result:=_t'4);
 [exact mode_selection_shape|exact RESULT|exact FRAME].
Qed.
Lemma mode_short_arguments cell e le m k argc :
 (Int.min_signed<=argc<17)%Z->le!_argc=Some(Vint(Int.repr argc))->
 region_certificate main_ge cell(fun after=>after=m)(selection_frontier 2 e le k m true)8
 (State f_main(validation_suffix 2)k e le m).
Proof.
 intros RANGE ARGC.
 change(validation_suffix 2)with(Ssequence(selection_check 2)(selection_after 2));validation_route.
 change(selection_check 2)with(Ssequence mode_conditions(selection_finish 2));validation_route.
 rewrite mode_condition_structure;validation_next.
 - eapply certified_if_edge with(v:=Val.of_bool(argc<?17)%Z)(b:=true).
   + apply mode_count_expression;[change Int.max_signed with 2147483647%Z;lia|exact ARGC].
   + rewrite number_bool_value;f_equal;apply Z.ltb_lt;lia.
 - validation_next;[apply certified_set_edge;apply old_expression_value;apply value_int|].
   apply selection_finish_certificate with(result:=_t'4);
   [exact mode_selection_shape|apply PTree.gss|validation_frame_auto].
Qed.
