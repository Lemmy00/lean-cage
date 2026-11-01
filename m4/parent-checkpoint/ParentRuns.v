(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.composition: Candidate source connection; integration review remains open. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine Library LibraryMachine StoreSteps WriteAll.
From LeanCageMainNumber Require Import NumberStructure NumberMath NumberMemory NumberStorage NumberSource NumberSafety NumberControl NumberInitial.
From LeanCageMain Require Import Main MainStructure.
From LeanCageArguments Require Import StringMachine.
From LeanCageValidation Require Import ValidationStructure ValidationValues.
From LeanCageParent Require Import ParentMachine ParentStructure ParentParse ParentWords ParentGuards ParentComparison ParentFinish ParentObserve ParentControl ParentSource.
Import ListNotations.
Open Scope nat_scope.
Definition parent_internal := previous string_source.
Lemma parent_store_actual ge cell P start count last : store_path ge P start count last->
 parent_steps ge cell(live start)(repeat parent_internal count)(live last).
Proof.
 intros PATH;induction PATH;cbn;[constructor|].
 destruct H0 as[IN[REAL UNIQUE]];eapply parent_steps_cons with(mid:=live next);[|exact IHPATH].
 unfold parent_internal,string_source;apply ParentMachine.previous_step;apply StringMachine.previous_step;apply original_step;apply internal;assumption.
Qed.
Lemma parent_guard_valid value : (0<value<=2147483647)%Z->parent_guard_bad(Some value)=false.
Proof.
 intros RANGE;unfold parent_guard_bad;apply Bool.orb_false_iff;split;[apply Z.eqb_neq|apply Z.ltb_ge];lia.
Qed.
Theorem parent_observation_reached e le before k argv ofs p bytes output value :
 e!_number=None->e!_getppid=None->e!_parent=Some(output,tulong)->le!_argv=Some(Vptr argv ofs)->
 Mem.loadv Mptr before(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 96)))=Some(address_value p)->
 number_input before(address_block p)(Ptrofs.repr(address_offset p))bytes->number_output before output Ptrofs.zero->
 decimal_number bytes=Some value->(0<value<=2147483647)%Z->
 exists count after,
 number_post before output Ptrofs.zero(Some value)after /\
 store_path main_ge(number_memory before output Ptrofs.zero(Some value))
 (State f_main(validation_suffix 15)k e le before)(9+count+parent_guard_cost(Some value)+3)
 (Callstate getppid_definition[]
 (Kcall(Some _t'15)f_main e(parent_guard_env(parent_loaded le p)(Some value))(parent_observation_cont k))after).
Proof.
 intros NUMBER GETPPID LOCAL ARGV TABLE INPUT OUTPUT PARSED RANGE.
 destruct(number_source_path main_ge before(address_block p)(Ptrofs.repr(address_offset p))bytes output Ptrofs.zero
 (parent_number_cont e(parent_loaded le p)k)INPUT OUTPUT)as[count[after[POST PATH]]].
 rewrite PARSED in POST,PATH;exists count,after;split;[exact POST|].
 replace(9+count+parent_guard_cost(Some value)+3)with(9+(count+(parent_guard_cost(Some value)+3)))by lia.
 eapply store_path_trans with(n:=9)(b:=number_initial(address_value p)(Vptr output Ptrofs.zero)(parent_number_cont e(parent_loaded le p)k)before).
 - eapply number_path_implication;[|apply parent_to_number with(argv:=argv)(ofs:=ofs);assumption];intros current EQ;left;exact EQ.
 - eapply store_path_trans with(n:=count);[exact PATH|].
   eapply number_path_implication with(P:=fun current=>current=after);[intros current EQ;subst;right;exact POST|].
   eapply store_path_trans with(n:=parent_guard_cost(Some value)).
   + apply parent_to_observe_path with(output:=output);[exact LOCAL|].
     intros found SAME;injection SAME as SAME;subst found;eapply parent_post_value;[rewrite PARSED;exact POST|exact PARSED].
   + apply parent_observe_call;[exact GETPPID|rewrite parent_guard_env_register,parent_guard_valid by exact RANGE;reflexivity].
Qed.
Theorem parent_observation_execution cell e le before k argv ofs p bytes output value :
 e!_number=None->e!_getppid=None->e!_parent=Some(output,tulong)->le!_argv=Some(Vptr argv ofs)->
 Mem.loadv Mptr before(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 96)))=Some(address_value p)->
 number_input before(address_block p)(Ptrofs.repr(address_offset p))bytes->number_output before output Ptrofs.zero->
 decimal_number bytes=Some value->(0<value<=2147483647)%Z->
 exists count after,
 number_post before output Ptrofs.zero(Some value)after /\
 forall observed waits,exists final suffix,
 parent_steps main_ge cell(live(State f_main(validation_suffix 15)k e le before))
 (repeat parent_internal count++repeat parent_wait waits++parent_observed observed::repeat parent_internal suffix)
 (live(parent_endpoint e final k after(negb(Int.eq observed(Int.repr value))))) /\
 validation_frame le final /\final!_t'15=Some(Vint observed).
Proof.
 intros NUMBER GETPPID LOCAL ARGV TABLE INPUT OUTPUT PARSED RANGE.
 destruct(parent_observation_reached e le before k argv ofs p bytes output value NUMBER GETPPID LOCAL ARGV TABLE INPUT OUTPUT PARSED RANGE)
 as[count[after[POST PREFIX]]].
 exists(9+count+parent_guard_cost(Some value)+3),after;split;[exact POST|].
 intros observed waits;set(mid:=parent_guard_env(parent_loaded le p)(Some value)).
 exists(parent_return_env mid value observed),(6+(if negb(Int.eq observed(Int.repr value))then 4 else 3)).
 split.
 - eapply parent_steps_trans;[eapply parent_store_actual;exact PREFIX|].
   induction waits;cbn;[|econstructor;[apply wait_parent|exact IHwaits]].
   econstructor;[apply observe_parent|];eapply parent_store_actual with(count:=6+(if negb(Int.eq observed(Int.repr value))then 4 else 3))(P:=fun current=>current=after).
   apply parent_return_path with(output:=output);[exact LOCAL|change(0<=value<=18446744073709551615)%Z;lia|].
   exact(proj2(parent_post_value before after output bytes value ltac:(rewrite PARSED;exact POST)PARSED)).
 - split.
   + unfold parent_return_env,mid;eapply validation_frame_trans;[apply parent_loaded_frame|].
     eapply validation_frame_trans;[apply parent_guard_env_frame|].
     eapply validation_frame_trans;[|apply ParentComparison.parent_comparison_frame].
     unfold validation_frame;split;WriteAll.lookup.
   + unfold parent_return_env;exact(proj1(ParentComparison.parent_comparison_registers _ value observed(PTree.gss _ _ _))).
Qed.
