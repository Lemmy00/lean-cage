(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.composition: Candidate source connection; integration review remains open. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine Deterministic Library ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From LeanCageMainNumber Require Import NumberStructure NumberMath NumberMemory NumberStorage NumberSource NumberSafety NumberControl NumberInitial.
From LeanCageMain Require Import Main MainStructure.
From LeanCageValidation Require Import StringRegion ValidationStructure ValidationValues.
From LeanCageParent Require Import ParentMachine ParentRegion ParentLift ParentPaths ParentStructure ParentParse ParentFinish ParentControl ParentAfterParse.
Import ListNotations.
Open Scope nat_scope.
Lemma parent_post_value before after output bytes value :
 number_post before output Ptrofs.zero(decimal_number bytes)after->decimal_number bytes=Some value->
 (0<=value<=Int64.max_unsigned)%Z /\
 Mem.loadv Mint64 after(Vptr output Ptrofs.zero)=Some(Vlong(Int64.repr value)).
Proof.
 intros POST PARSED;split.
 - apply decimal_number_exact in PARSED;unfold decimal_max in PARSED;exact(proj2(proj2(proj2 PARSED))).
 - rewrite PARSED in POST;apply number_post_store in POST.
   change(Mem.store Mint64 before output 0(Vlong(Int64.repr value))=Some after)in POST.
   change(Mem.load Mint64 after output 0=Some(Vlong(Int64.repr value))).
   rewrite(Mem.load_store_same _ _ _ _ _ _ POST);reflexivity.
Qed.
Theorem parent_source_certificate cell e le before k argv ofs p bytes output :
 e!_number=None->(parent_guard_bad(decimal_number bytes)=false->e!_getppid=None)->e!_parent=Some(output,tulong)->
 le!_argv=Some(Vptr argv ofs)->
 Mem.loadv Mptr before(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 96)))=Some(address_value p)->
 number_input before(address_block p)(Ptrofs.repr(address_offset p))bytes->
 number_output before output Ptrofs.zero->
 exists count after,number_post before output Ptrofs.zero(decimal_number bytes)after /\
 parent_certificate main_ge cell(number_memory before output Ptrofs.zero(decimal_number bytes))
 (parent_frontier e le k after(decimal_number bytes))(9+count+28)
 (State f_main(validation_suffix 15)k e le before).
Proof.
 intros NUMBER GETPPID LOCAL ARGV TABLE INPUT OUTPUT.
 destruct(number_source_path main_ge before(address_block p)(Ptrofs.repr(address_offset p))bytes
 output Ptrofs.zero(parent_number_cont e(parent_loaded le p)k)INPUT OUTPUT)as[count[after[POST PATH]]].
 exists count,after;split;[exact POST|].
 replace(9+count+28)with(9+(count+28))by lia.
 eapply parent_store_path with(last:=number_initial(address_value p)(Vptr output Ptrofs.zero)(parent_number_cont e(parent_loaded le p)k)before).
 - eapply number_path_implication;[|apply parent_to_number with(argv:=argv)(ofs:=ofs);assumption].
   intros current EQ;left;exact EQ.
 - eapply parent_store_path;[exact PATH|].
   eapply parent_convert with(P:=fun current=>current=after)
     (R:=parent_frontier e(parent_loaded le p)k after(decimal_number bytes)).
   + apply parent_after_parse with(output:=output);[exact GETPPID|exact LOCAL|].
     intros value PARSED;eapply parent_post_value;eassumption.
   + intros current EQ;subst current;right;exact POST.
   + intros endpoint RESULT;eapply parent_frontier_frame;[apply parent_loaded_frame|exact RESULT].
Qed.
Definition parent_guarantee ge cell P R n start :=
 P(memory_of start) /\
 (exists events endpoint,parent_steps ge cell(live start)events(live endpoint) /\
  parent_cost events<=n /\P(memory_of endpoint) /\R endpoint) /\
 (forall events target,parent_steps ge cell(live start)events target->
  (P(routine_memory target) /\parent_cost events<=S n /\
   (forall s,target=live s->R s \/exists ev next,parent_waiting ev=false /\ev<>parent_loss /\parent_step ge cell(live s)ev(live next))) \/
  (exists prefix endpoint rest,events=prefix++rest /\parent_cost prefix<=n /\
   parent_steps ge cell(live start)prefix(live endpoint) /\P(memory_of endpoint) /\R endpoint /\
   parent_steps ge cell(live endpoint)rest target)).
Theorem parent_certificate_guarantee ge cell P R n start :
 parent_certificate ge cell P R n start->parent_guarantee ge cell P R n start.
Proof.
 intros CERT;split;[eapply parent_memory;exact CERT|];split;[apply parent_actual;exact CERT|].
 intros events target RUN;destruct(parent_execution_split _ _ _ _ _ _ CERT _ _ RUN)as[[MEM[BOUND LIVE]]|DONE];[left|right;exact DONE].
 split;[exact MEM|];split;[exact BOUND|].
 intros s EQ;destruct(LIVE s EQ)as[remaining TAIL];eapply parent_live_progress;exact TAIL.
Qed.
Theorem parent_source cell e le before k argv ofs p bytes output :
 e!_number=None->(parent_guard_bad(decimal_number bytes)=false->e!_getppid=None)->e!_parent=Some(output,tulong)->
 le!_argv=Some(Vptr argv ofs)->
 Mem.loadv Mptr before(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 96)))=Some(address_value p)->
 number_input before(address_block p)(Ptrofs.repr(address_offset p))bytes->
 number_output before output Ptrofs.zero->
 exists count after,number_post before output Ptrofs.zero(decimal_number bytes)after /\
 parent_guarantee main_ge cell(number_memory before output Ptrofs.zero(decimal_number bytes))
 (parent_frontier e le k after(decimal_number bytes))(9+count+28)
 (State f_main(validation_suffix 15)k e le before).
Proof.
 intros NUMBER GETPPID LOCAL ARGV TABLE INPUT OUTPUT.
 destruct(parent_source_certificate cell e le before k argv ofs p bytes output NUMBER GETPPID LOCAL ARGV TABLE INPUT OUTPUT)
 as[count[after[POST CERT]]];exists count,after;split;[exact POST|apply parent_certificate_guarantee;exact CERT].
Qed.
