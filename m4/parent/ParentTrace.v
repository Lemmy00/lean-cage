(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-parent.history: Admission and mismatch retain the actual observed word. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine Library StoreSteps WriteAll.
From LeanCageMainNumber Require Import NumberStructure NumberMath NumberMemory NumberStorage NumberSource NumberControl NumberInitial.
From LeanCageMain Require Import Main MainStructure.
From LeanCageValidation Require Import StringRegion ValidationStructure ValidationValues.
From LeanCageParent Require Import ParentMachine ParentStructure ParentParse ParentWords ParentGuards
 ParentComparison ParentFinish ParentControl ParentObserve ParentAfterParse ParentSource ParentFrontier
 TraceRegion TraceExecution.
Import ListNotations.
Open Scope nat_scope.

Definition traced_parent_frontier e base k m parsed history s :=
 if parent_guard_bad parsed then history=[] /\parent_frontier e base k m parsed s
 else exists observed final,history=[observed] /\validation_frame base final /\
 final!_t'15=Some(Vint observed) /\
 s=parent_endpoint e final k m(negb(Int.eq observed(Int.repr(parent_value parsed)))).
Definition matching_history bytes history := exists value observed,
 decimal_number bytes=Some value /\(0<value<=2147483647)%Z /\history=[observed] /\Int.signed observed=value.

Lemma traced_parent_frame e base middle k m parsed history s : validation_frame base middle->
 traced_parent_frontier e middle k m parsed history s->traced_parent_frontier e base k m parsed history s.
Proof.
 intros FRAME;unfold traced_parent_frontier;destruct(parent_guard_bad parsed).
 - intros[H END];split;[exact H|eapply parent_frontier_frame;eassumption].
 - intros[observed[final[H[MORE[REG END]]]]];exists observed,final;split;[exact H|];split;[eapply validation_frame_trans;eassumption|auto].
Qed.

Theorem parent_after_parse_trace cell e le m k output parsed :
 (parent_guard_bad parsed=false->e!_getppid=None)->e!_parent=Some(output,tulong)->
 (forall value,parsed=Some value->(0<=value<=Int64.max_unsigned)%Z /\
 Mem.loadv Mint64 m(Vptr output Ptrofs.zero)=Some(Vlong(Int64.repr value)))->
 trace_certificate main_ge cell(fun after=>after=m)(traced_parent_frontier e le k m parsed)28 []
 (Returnstate(number_code parsed)(parent_number_cont e le k)m).
Proof.
 intros GLOBAL LOCAL OWN;eapply trace_weaken with(n:=parent_guard_cost parsed+14);
 [|pose proof(parent_guard_cost_bound parsed);lia].
 eapply trace_store_path;[apply parent_to_observe_path with(output:=output);assumption|].
 eapply trace_convert with(R:=traced_parent_frontier e(parent_guard_env le parsed)k m parsed).
 - unfold traced_parent_frontier;pose proof(parent_guard_env_register le parsed)as REG.
   destruct(parent_guard_bad parsed)eqn:BAD.
   + eapply trace_weaken with(n:=6);[|lia].
     replace 6 with(6+0)by lia;eapply trace_store_path;[apply parent_observe_reject;exact REG|].
     apply trace_stop;[reflexivity|];split;[reflexivity|].
     unfold parent_frontier;rewrite BAD.
     exists(PTree.set _t'14(Vint Int.one)(parent_guard_env le parsed));split;
     [unfold validation_frame;split;WriteAll.lookup|reflexivity].
   + change 14 with(3+11);eapply trace_store_path;[apply parent_observe_call;[apply GLOBAL;reflexivity|exact REG]|].
     apply trace_choice with(preferred:=Int.repr(parent_value parsed));[reflexivity|].
     intros observed;change([]++[observed])with[observed].
     assert(RANGE:(0<=parent_value parsed<=Int64.max_unsigned)%Z).
     { destruct parsed as[value|];[exact(proj1(OWN value eq_refl))|discriminate BAD]. }
     assert(LOAD:Mem.loadv Mint64 m(Vptr output Ptrofs.zero)=Some(Vlong(Int64.repr(parent_value parsed)))).
     { destruct parsed as[value|];[exact(proj2(OWN value eq_refl))|discriminate BAD]. }
     eapply trace_weaken with(n:=6+(if negb(Int.eq observed(Int.repr(parent_value parsed)))then 4 else 3));
     [|destruct(negb(Int.eq observed(Int.repr(parent_value parsed))));lia].
     replace(6+(if negb(Int.eq observed(Int.repr(parent_value parsed)))then 4 else 3))with
      ((6+(if negb(Int.eq observed(Int.repr(parent_value parsed)))then 4 else 3))+0)at 1 by lia.
     eapply trace_store_path;[apply parent_return_path with(output:=output);assumption|].
     apply trace_stop;[unfold parent_endpoint;destruct(negb(Int.eq observed(Int.repr(parent_value parsed))));reflexivity|].
     exists observed,(parent_return_env(parent_guard_env le parsed)(parent_value parsed)observed);split;[reflexivity|];split.
     * unfold parent_return_env;eapply validation_frame_trans;[|apply parent_comparison_frame].
       unfold validation_frame;split;WriteAll.lookup.
     * split;[unfold parent_return_env;exact(proj1(parent_comparison_registers _ _ _ (PTree.gss _ _ _)))|reflexivity].
 - intros current SAME;exact SAME.
 - intros history s END;apply traced_parent_frame with(middle:=parent_guard_env le parsed);[apply parent_guard_env_frame|exact END].
Qed.

Theorem parent_source_trace_certificate cell e le before k argv ofs p bytes output :
 e!_number=None->(parent_guard_bad(decimal_number bytes)=false->e!_getppid=None)->e!_parent=Some(output,tulong)->
 le!_argv=Some(Vptr argv ofs)->
 Mem.loadv Mptr before(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 96)))=Some(address_value p)->
 number_input before(address_block p)(Ptrofs.repr(address_offset p))bytes->number_output before output Ptrofs.zero->
 exists count after,number_post before output Ptrofs.zero(decimal_number bytes)after /\
 trace_certificate main_ge cell(number_memory before output Ptrofs.zero(decimal_number bytes))
 (traced_parent_frontier e le k after(decimal_number bytes))(9+count+28)[]
 (State f_main(validation_suffix 15)k e le before).
Proof.
 intros NUMBER GETPPID LOCAL ARGV TABLE INPUT OUTPUT.
 destruct(number_source_path main_ge before(address_block p)(Ptrofs.repr(address_offset p))bytes
 output Ptrofs.zero(parent_number_cont e(parent_loaded le p)k)INPUT OUTPUT)as[count[after[POST PATH]]].
 exists count,after;split;[exact POST|];replace(9+count+28)with(9+(count+28))by lia.
 eapply trace_store_path with(last:=number_initial(address_value p)(Vptr output Ptrofs.zero)(parent_number_cont e(parent_loaded le p)k)before).
 - eapply number_path_implication;[|apply parent_to_number with(argv:=argv)(ofs:=ofs);assumption].
   intros current EQ;left;exact EQ.
 - eapply trace_store_path;[exact PATH|].
   eapply trace_convert with(P:=fun current=>current=after)
     (R:=traced_parent_frontier e(parent_loaded le p)k after(decimal_number bytes)).
   + apply parent_after_parse_trace with(output:=output);[exact GETPPID|exact LOCAL|].
     intros value PARSED;eapply parent_post_value;eassumption.
   + intros current EQ;subst current;right;exact POST.
   + intros history endpoint RESULT;eapply traced_parent_frame;[apply parent_loaded_frame|exact RESULT].
Qed.

Lemma traced_parent_split e le k m bytes history s :
 traced_parent_frontier e le k m(decimal_number bytes)history s->
 (parent_rejection e le k m(decimal_number bytes)s /\
  ((parent_guard_bad(decimal_number bytes)=true /\history=[]) \/
   (exists observed,history=[observed] /\parent_guard_bad(decimal_number bytes)=false /\
    Int.eq observed(Int.repr(parent_value(decimal_number bytes)))=false))) \/
 (parent_admission e le k m(decimal_number bytes)s /\matching_history bytes history).
Proof.
 unfold traced_parent_frontier;destruct(parent_guard_bad(decimal_number bytes))eqn:BAD.
 - intros[H END];left;split;[|left;auto];split;[exact END|].
   unfold parent_frontier in END;rewrite BAD in END;destruct END as[final[FRAME LAST]];eauto.
 - intros[observed[final[H[FRAME[REG LAST]]]]].
   assert(END:parent_frontier e le k m(decimal_number bytes)s).
   { unfold parent_frontier;rewrite BAD;exists observed,final;auto. }
   destruct(Int.eq observed(Int.repr(parent_value(decimal_number bytes))))eqn:EQ.
   + right;split.
     * split;[exact END|];exists final;split;[exact FRAME|exact LAST].
     * destruct(decimal_number bytes)as[value|]eqn:PARSED;[|discriminate BAD].
       assert(RANGE:(0<value<=2147483647)%Z).
       { pose proof(proj1(decimal_number_exact bytes value)PARSED)as[NE[DIG[FOLD RANGE]]].
         unfold parent_guard_bad in BAD;apply Bool.orb_false_iff in BAD;destruct BAD as[NZ UPPER].
         apply Z.eqb_neq in NZ;apply Z.ltb_ge in UPPER;lia. }
       exists value,observed;split;[exact PARSED|];split;[exact RANGE|];split;[exact H|].
       apply(proj1(parent_match_signed value observed RANGE));exact EQ.
   + left;split;[split;[exact END|exists final;exact LAST]|right;exists observed;auto].
Qed.
