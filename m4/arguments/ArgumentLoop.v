(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.arguments: Construct every accepted and first-rejected loop path. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Clight.
Require Import Machine Library.
From LeanCageMain Require Import Main MainStructure.
From LeanCageArguments Require Import StringMachine StringPath ArgumentStructure ArgumentWords
 ArgumentValues ArgumentControl ArgumentMemory.
Import ListNotations.
Open Scope Z_scope.
Definition argument_loop_endpoint result e le k m := match result with
|arguments_accepted _=>State f_main Sskip k e le m
|arguments_rejected _ _=>argument_failure_state e le k m end.
Theorem argument_loop_source cell m argv ofs argc i total inputs e le k :
 16<=i -> argc<=2147483647 -> i+Z.of_nat(length inputs)=argc ->
 0<=total<=4097*(i-16) -> guest_arguments_owned m argv ofs i inputs ->
 e!_strlen=None -> argument_registers le argv ofs argc i total ->
 exists count final,(count<=26*length inputs+5)%nat /\
 argument_registers final argv ofs argc(outcome_index argc(argument_scan i total inputs))
 (outcome_total(argument_scan i total inputs)) /\
 string_path main_ge cell(State f_main argument_loop k e le m)count
 (argument_loop_endpoint(argument_scan i total inputs)e final k m).
Proof.
 revert i total le;induction inputs as[|x rest IH];intros i total le LOW HIGH SIZE TOTAL OWN GLOBAL REGS.
 - cbn in SIZE;assert(i=argc)by lia;subst i;exists 5%nat,le;split;[cbn;lia|];split;[exact REGS|].
   apply string_store_path with(m:=m);apply argument_loop_finished with(argc:=argc);
   [exact(proj1(proj2 REGS))|exact(proj1(proj2(proj2 REGS)))|lia].
 - assert(INDEX:16<=i<argc)by(cbn in SIZE;lia).
   destruct OWN as[STRING[LOAD TAIL]].
   pose proof(argument_strlen_range _ _ _ STRING)as LENGTH.
   change(0<=guest_size x<Int64.max_unsigned)in LENGTH.
   pose proof(argument_loaded_registers _ _ _ _ _ _ (guest_pointer x) REGS)as LOADED.
   destruct(argument_bad(guest_size x))eqn:BAD.
   + exists 23%nat,(argument_checked(argument_loaded le(guest_pointer x))(guest_size x));split;[cbn;lia|].
     cbn[argument_scan];rewrite BAD;split.
     * apply argument_checked_registers;exact LOADED.
     * cbn[argument_loop_endpoint];eapply string_path_trans with(n:=10%nat).
       -- apply string_store_path with(m:=m);eapply argument_to_call;
          [exact GLOBAL|exact REGS|exact INDEX|exact HIGH|exact LOAD].
       -- eapply string_next;[apply string_strlen_edge;exact STRING|].
          apply string_store_path with(m:=m);apply argument_after_failure with(n:=guest_size x);[lia|exact BAD].
   + assert(VALID:1<=guest_size x<=4096)by(apply(argument_bad_false (guest_size x) ltac:(lia));exact BAD).
     pose proof(argument_accumulator_range i(guest_size x)total ltac:(lia)TOTAL VALID)as[NEXT RANGE].
     destruct(IH(i+1)(total+guest_size x+1)
       (argument_advanced(argument_loaded le(guest_pointer x))(guest_size x)i total)
       ltac:(lia)HIGH ltac:(cbn in SIZE;lia) NEXT TAIL GLOBAL
       (argument_advanced_registers _ _ _ _ _ _ _ LOADED))as[count[final[BOUND[REG PATH]]]].
     exists(26+count)%nat,final;split;[cbn;lia|].
     cbn[argument_scan];rewrite BAD;split;[exact REG|].
     eapply string_path_trans with(n:=10%nat).
     * apply string_store_path with(m:=m);eapply argument_to_call;
       [exact GLOBAL|exact REGS|exact INDEX|exact HIGH|exact LOAD].
     * eapply string_next;[apply string_strlen_edge;exact STRING|].
       eapply string_path_trans with(n:=15%nat).
       -- apply string_store_path with(m:=m);apply argument_after_success with(n:=guest_size x)(i:=i)(total:=total);
          [exact(proj1(proj2(proj2 LOADED)))|exact(proj2(proj2(proj2 LOADED)))|lia|exact TOTAL|exact VALID].
       -- exact PATH.
Qed.
