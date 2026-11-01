(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.strings: Actual caller checks, owned bytes and explicit execution boundaries. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Library LibraryMachine Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From LeanCageMainNumber Require Import NumberControl.
From LeanCageMain Require Import Main MainStructure.
From LeanCageArguments Require Import StringMachine StringPath.
From LeanCageValidation Require Import StringRegion ValidationStructure ValidationMemory ValidationValues ValidationCalls ValidationFinish ModeCaller.
Import ListNotations.
Open Scope nat_scope.
Ltac prefix_next := eapply store_next;[reflexivity| |].
Ltac prefix_route := prefix_next;[apply unchanged_store_edge;WriteAll.structural|].
Theorem mode_first_comparison e le m k argc argv ofs p :
 (17<=argc<=Int.max_signed)%Z->le!_argc=Some(Vint(Int.repr argc))->
 e!_strcmp=None->e!___stringlit_131=None->le!_argv=Some(Vptr argv ofs)->
 Mem.loadv Mptr m(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 8)))=Some(address_value p)->
 exists called,store_path main_ge(fun after=>after=m)(State f_main(validation_suffix 2)k e le m)8
 (Callstate strcmp_definition[address_value p;address_value(literal_address ___stringlit_131)]called m).
Proof.
 intros RANGE ARGC STRCMP PLAN ARGV LOAD;eexists.
 change(validation_suffix 2)with(Ssequence(selection_check 2)(selection_after 2));prefix_route.
 change(selection_check 2)with(Ssequence mode_conditions(selection_finish 2));prefix_route.
 rewrite mode_condition_structure;prefix_next.
 - eapply certified_if_edge with(v:=Val.of_bool(argc<?17)%Z)(b:=false).
   + apply mode_count_expression;[change Int.min_signed with(-2147483648)%Z;lia|exact ARGC].
   + rewrite number_bool_value;f_equal;apply Z.ltb_ge;lia.
 - mode_unfold;prefix_route;prefix_route;prefix_next.
   + apply certified_set_edge;eapply validation_argv_value;[exact ARGV|lia|exact LOAD].
   + prefix_route;prefix_next.
     * eapply certified_call_edge.
       -- reflexivity.
       -- apply old_expression_value;eapply value_function;
          [exact STRCMP|exact(proj1 validation_function_bindings)|reflexivity].
       -- eapply cons_argument_values;
          [apply old_expression_value;apply value_temp;apply PTree.gss|reflexivity|].
          eapply cons_argument_values;
          [apply validation_literal_value;[exact PLAN|unfold validation_literals;do 5 right;left;reflexivity]|reflexivity|apply no_argument_values].
       -- exact(proj1(proj2 validation_function_bindings)).
       -- reflexivity.
     * constructor;reflexivity.
Qed.
Theorem strcmp_waits_loss ge cell m left right xs ys k n :
 c_string m left xs->c_string m right ys->
 string_steps ge cell(live(Callstate strcmp_definition[address_value left;address_value right]k m))
 (repeat(previous_event library_wait)n++[string_loss])(dead m).
Proof.
 intros LEFT RIGHT;induction n;cbn.
 - econstructor;[apply string_loss_everywhere|constructor].
 - econstructor;[constructor;apply library_wait_step;constructor;exists xs,ys;auto|exact IHn].
Qed.
Theorem mode_prefix_waits_loss cell e le m k argc argv ofs p bytes n :
 (17<=argc<=Int.max_signed)%Z->le!_argc=Some(Vint(Int.repr argc))->
 e!_strcmp=None->e!___stringlit_131=None->le!_argv=Some(Vptr argv ofs)->
 Mem.loadv Mptr m(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 8)))=Some(address_value p)->
 c_string m p bytes->c_string m(literal_address ___stringlit_131)plan_bytes->
 exists prefix,string_cost prefix=8 /\
 string_steps main_ge cell(live(State f_main(validation_suffix 2)k e le m))
 (prefix++repeat(previous_event library_wait)n++[string_loss])(dead m).
Proof.
 intros RANGE ARGC STRCMP PLAN ARGV LOAD OWN LITERAL.
 destruct(mode_first_comparison e le m k argc argv ofs p RANGE ARGC STRCMP PLAN ARGV LOAD)as[called PATH].
 destruct(string_path_actual main_ge cell _ _ _(string_store_path main_ge cell _ _ _ m PATH))as[prefix[COST RUN]].
 exists prefix;split;[exact COST|];eapply string_steps_trans;[exact RUN|eapply strcmp_waits_loss;eassumption].
Qed.
Theorem mode_prefix_comparison cell e le m k argc argv ofs p bytes value :
 (17<=argc<=Int.max_signed)%Z->le!_argc=Some(Vint(Int.repr argc))->
 e!_strcmp=None->e!___stringlit_131=None->le!_argv=Some(Vptr argv ofs)->
 Mem.loadv Mptr m(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 8)))=Some(address_value p)->
 c_string m p bytes->c_string m(literal_address ___stringlit_131)plan_bytes->
 comparison_result(compare_bytes bytes plan_bytes)value->
 exists prefix called,string_cost prefix=8 /\
 string_steps main_ge cell(live(State f_main(validation_suffix 2)k e le m))
 (prefix++[previous_event(strcmp_returned p(literal_address ___stringlit_131)value)])
 (live(Returnstate(Vint value)called m)).
Proof.
 intros RANGE ARGC STRCMP PLAN ARGV LOAD OWN LITERAL RESULT.
 destruct(mode_first_comparison e le m k argc argv ofs p RANGE ARGC STRCMP PLAN ARGV LOAD)as[called PATH].
 destruct(string_path_actual main_ge cell _ _ _(string_store_path main_ge cell _ _ _ m PATH))as[prefix[COST RUN]].
 exists prefix,called;split;[exact COST|];eapply string_steps_trans;[exact RUN|].
 econstructor;[constructor;constructor;exists bytes,plan_bytes;auto|constructor].
Qed.
From compcert Require Import Globalenvs.
Require Import FreshMemoryDraft.
From LeanCageArguments Require Import ArgumentWitnesses.
From LeanCageDigest Require Import DigestWitnesses.
From LeanCageValidation Require Import ValidationAllocation ValidationWitnesses.
Open Scope nat_scope.
Definition magnitude_cases := [([Byte.repr 255],Int.repr 2);([Byte.repr 255],Int.repr 2147483647);
 ([],Int.repr(-7));([],Int.repr(-2147483648))].
Theorem magnitude_cases_checked : Forall(fun input=>digest_input_admissibleb(fst input)=true /\
 comparison_result(compare_bytes(fst input)plan_bytes)(snd input))magnitude_cases.
Proof. repeat(apply Forall_cons;[vm_compute;repeat constructor;congruence|]);constructor. Qed.
Theorem allocated_magnitude_source cell input : In input magnitude_cases->
 exists initial m argv p prefix called,Genv.init_mem Main.prog=Some initial /\old_memory initial m /\
 string_cost prefix=8 /\
 string_steps main_ge cell(live(State f_main(validation_suffix 2)Kstop empty_env(argument_witness_env argv 17)m))
 (prefix++[previous_event(strcmp_returned p(literal_address ___stringlit_131)(snd input))])
 (live(Returnstate(Vint(snd input))called m)).
Proof.
 intros IN;pose proof magnitude_cases_checked as CHECKED;rewrite Forall_forall in CHECKED.
 destruct(CHECKED input IN)as[VALID RESULT].
 destruct(allocated_validation_input 1(fst input)ltac:(lia)(digest_input_admissible_sound _ VALID))
 as[initial[m[argv[p[INIT[OLD[TEXT[LITERALS[LOAD[FRESH TABLE]]]]]]]]]].
 destruct(mode_prefix_comparison cell empty_env(argument_witness_env argv 17)m Kstop 17 argv Ptrofs.zero p(fst input)(snd input)
 ltac:(change Int.max_signed with 2147483647%Z;lia)
 ltac:(unfold argument_witness_env;WriteAll.lookup)eq_refl eq_refl
 ltac:(unfold argument_witness_env;WriteAll.lookup)
 ltac:(rewrite Ptrofs.add_zero_l;exact LOAD)TEXT ltac:(owned_literal)RESULT)
 as[prefix[called[COST RUN]]];exists initial,m,argv,p,prefix,called;auto.
Qed.
Theorem allocated_mode_wait_loss cell n :
 exists initial m argv prefix,Genv.init_mem Main.prog=Some initial /\old_memory initial m /\
 string_cost prefix=8 /\
 string_steps main_ge cell(live(State f_main(validation_suffix 2)Kstop empty_env(argument_witness_env argv 17)m))
 (prefix++repeat(previous_event library_wait)n++[string_loss])(dead m).
Proof.
 assert(VALID:digest_input_admissibleb plan_bytes=true)by reflexivity.
 destruct(allocated_validation_input 1 plan_bytes ltac:(lia)(digest_input_admissible_sound _ VALID))
 as[initial[m[argv[p[INIT[OLD[TEXT[LITERALS[LOAD[FRESH TABLE]]]]]]]]]].
 destruct(mode_prefix_waits_loss cell empty_env(argument_witness_env argv 17)m Kstop 17 argv Ptrofs.zero p plan_bytes n
 ltac:(change Int.max_signed with 2147483647%Z;lia)
 ltac:(unfold argument_witness_env;WriteAll.lookup)eq_refl eq_refl
 ltac:(unfold argument_witness_env;WriteAll.lookup)
 ltac:(rewrite Ptrofs.add_zero_l;exact LOAD)TEXT ltac:(owned_literal))
 as[prefix[COST RUN]];exists initial,m,argv,prefix;auto.
Qed.
