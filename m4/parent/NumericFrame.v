(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-parent.history: Preserve actual observations and ordered source memory. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine StoreSteps ScalarMemory WriteAll.
From LeanCageMainNumber Require Import NumberMath NumberMemory NumberStructure NumberStorage NumberInitial NumberSource.
From LeanCageMain Require Import Main MainStructure MainMemory MainValues MainControl MainLoop.
Import ListNotations.
Open Scope Z_scope.
Theorem numeric_loop_framed m fields argv ofs i inputs e le k :
 0<=i -> i+Z.of_nat(length inputs)=10 ->
 numeric_buffers m main_policy_block fields argv ofs i inputs ->
 numeric_locals e fields -> numeric_registers le argv ofs i ->
 exists count after final,
 policy_stores main_policy_block i m(numeric_values inputs)after /\
 numeric_registers final argv ofs(i+Z.of_nat(length(numeric_values inputs))) /\
 final!_argc=le!_argc /\
 store_path main_ge (policy_prefix main_policy_block i m(numeric_values inputs))
 (State f_main numeric_loop k e le m)count(numeric_endpoint inputs e final k after).
Proof.
 revert m i le;induction inputs as [|x rest IH];intros m i le LOW SIZE BUFFERS LOCALS REGS.
 - cbn in SIZE;assert(i=10)by lia;subst i.
   exists 5%nat,m,le;split;[constructor|]. split.
   + cbn;replace(10+0)with 10 by lia;exact REGS.
   + split;[reflexivity|];cbn[numeric_endpoint numeric_complete numeric_values];apply numeric_loop_finished with(argv:=argv)(ofs:=ofs);
      [exact REGS|apply policy_prefix_initial].
 - assert(INDEX : 0<=i<10)by(cbn in SIZE;lia).
   destruct BUFFERS as [FNE [ANE [TABLE [ARGS OUTPUT]]]].
   destruct ARGS as [INPUT [XNE [LOAD TAIL]]].
   assert(BUFFERS : numeric_buffers m main_policy_block fields argv ofs i(x::rest)).
   { split;[exact FNE|]. split;[exact ANE|]. split;[exact TABLE|].
     split;[cbn;auto|exact OUTPUT]. }
   pose proof(numeric_loaded_registers le argv ofs i x REGS)as LOADED.
   destruct(number_source_path main_ge m(input_block x)(input_offset x)(input_bytes x)
    main_policy_block(Ptrofs.repr(8*i))(numeric_number_cont e(numeric_loaded le x i)k)
    INPUT (OUTPUT i INDEX))as[n [mid [POST PARSER]]].
   destruct(decimal_number(input_bytes x))as[value|]eqn:PARSED.
   + assert(AFTER : numeric_buffers mid main_policy_block fields argv ofs(i+1)rest).
     { apply numeric_buffers_tail with(x:=x).
       eapply numeric_buffers_preserved;[right;exact POST|exact BUFFERS]. }
     destruct(IH mid(i+1)(numeric_advanced(numeric_loaded le x i)i)
      ltac:(lia) ltac:(cbn in SIZE;lia) AFTER LOCALS(numeric_advanced_registers _ _ _ _ LOADED))
      as[tailcount [after [final [STORES [FINAL [FRAME RUN]]]]]].
     exists(12+n+6+tailcount)%nat,after,final.
     cbn[numeric_values numeric_complete];rewrite PARSED;split.
     * eapply policy_stores_cons;eassumption.
     * split.
       -- change(numeric_registers final argv ofs(i+Z.of_nat(S(length(numeric_values rest)))));replace(i+Z.of_nat(S(length(numeric_values rest))))with(i+1+Z.of_nat(length(numeric_values rest)))by lia;exact FINAL.
       -- split;[rewrite FRAME;unfold numeric_advanced,numeric_returned,numeric_loaded;WriteAll.lookup|].
          unfold numeric_endpoint;cbn[numeric_complete];rewrite PARSED.
          eapply store_path_trans with(n:=(12+n+6)%nat).
          ++ eapply store_path_trans with(n:=(12+n)%nat).
             ** eapply store_path_trans with(n:=12%nat).
                --- apply numeric_to_call with(fields:=fields)(argv:=argv)(ofs:=ofs);
                    [exact LOCALS|exact REGS|exact INDEX|exact LOAD|apply TABLE;exact INDEX|apply policy_prefix_initial].
                --- eapply number_path_implication;[|exact PARSER].
                    intros current MEMORY;apply policy_prefix_head;assumption.
             ** apply numeric_after_success with(argv:=argv)(ofs:=ofs);
                [exact LOADED|exact INDEX|apply policy_prefix_head;[exact INDEX|right;exact POST]].
          ++ eapply number_path_implication;[|exact RUN].
             intros current MEMORY;eapply policy_prefix_cons;eassumption.
   + cbn[number_post]in POST;subst mid.
     exists(12+n+5)%nat,m,(numeric_returned(numeric_loaded le x i)None).
     cbn[numeric_values numeric_complete];rewrite PARSED;split;[constructor|]. split.
     * cbn;replace(i+0)with i by lia;apply numeric_returned_registers;exact LOADED.
     * split;[unfold numeric_returned,numeric_loaded;WriteAll.lookup|].
       unfold numeric_endpoint;cbn[numeric_complete];rewrite PARSED.
       eapply store_path_trans with(n:=(12+n)%nat).
       -- eapply store_path_trans with(n:=12%nat).
          ++ apply numeric_to_call with(fields:=fields)(argv:=argv)(ofs:=ofs);
             [exact LOCALS|exact REGS|exact INDEX|exact LOAD|apply TABLE;exact INDEX|apply policy_prefix_initial].
          ++ eapply number_path_implication;[|exact PARSER].
             intros current [SAME|SAME];cbn[number_post]in SAME;subst;apply policy_prefix_initial.
       -- apply numeric_after_failure;apply policy_prefix_initial.
Qed.
