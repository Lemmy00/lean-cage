(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.digest: Construct the complete character scan from owned bytes. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Readers Library Machine StoreSteps.
From LeanCageMain Require Import Main MainStructure.
From LeanCageDigest Require Import DigestStructure DigestWords DigestMemory DigestValues DigestCharacter DigestControl.
Import ListNotations.
Open Scope Z_scope.
Theorem digest_loop_source m p before after le k :
 c_string m p(before++after)->length(before++after)=64%nat->
 digest_registers le p(Z.of_nat(length before))->
 exists count,(count<=32*length after+7)%nat /\
 store_path main_ge(fun result=>result=m)
 (State f_digest_text digest_loop(Kseq digest_success k)empty_env le m)count
 (Returnstate(Val.of_bool(forallb digest_hex after))(call_cont k)m).
Proof.
 revert before le;induction after as[|b after IH];intros before le OWN SIZE REGS.
 - rewrite app_nil_r in SIZE;exists 7%nat;split;[cbn;lia|].
   eapply store_path_trans with(n:=5%nat);[apply digest_loop_finished;destruct REGS as[_ INDEX];rewrite SIZE in INDEX;exact INDEX|].
   apply digest_finish.
 - assert(INDEX:0<=Z.of_nat(length before)<64)by(rewrite length_app in SIZE;cbn in SIZE;lia).
   pose proof(digest_character_read _ _ _ _ _ OWN)as LOAD.
   pose proof(digest_loop_to_character le m(Z.of_nat(length before))(Kseq digest_success k)(proj2 REGS)INDEX)as START.
   pose proof(digest_character_source le m p(Z.of_nat(length before))b
    (digest_character_cont(Kseq digest_success k))REGS ltac:(lia) LOAD)as CHAR.
   destruct(digest_hex b)eqn:HEX;cbn[forallb];rewrite HEX;cbn[andb].
   + assert(NEXTOWN:c_string m p((before++[b])++after))by(rewrite<-app_assoc;exact OWN).
     assert(NEXTSIZE:length((before++[b])++after)=64%nat)by(rewrite<-app_assoc;exact SIZE).
     assert(NEXTREG:digest_registers(digest_advanced le b(Z.of_nat(length before)))p
       (Z.of_nat(length(before++[b])))).
     { rewrite length_app,Nat2Z.inj_add;cbn;apply digest_advanced_registers;exact REGS. }
     destruct(IH _ _ NEXTOWN NEXTSIZE NEXTREG)as[count[BOUND TAIL]].
     exists(5+digest_character_count b+5+count)%nat;split.
     * pose proof(digest_character_bound b);cbn[length];lia.
     * replace(5+digest_character_count b+5+count)%nat with
       (5+(digest_character_count b+(5+count)))%nat by lia.
       eapply store_path_trans;[exact START|];eapply store_path_trans;[exact CHAR|].
       eapply store_path_trans;[apply digest_character_success;[exact(proj2 REGS)|exact INDEX|exact HEX]|exact TAIL].
   + exists(5+digest_character_count b+3)%nat;split.
     * pose proof(digest_character_bound b);cbn[length];lia.
     * replace(5+digest_character_count b+3)%nat with(5+(digest_character_count b+3))%nat by lia.
       eapply store_path_trans;[exact START|];eapply store_path_trans;[exact CHAR|].
       exact(digest_character_failure le m b(Kseq digest_success k)HEX).
Qed.
