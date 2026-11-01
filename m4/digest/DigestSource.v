(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.digest: Constructive function paths and all-execution guarantees. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Values Memory Clight.
Require Import Library Machine ClightSteps Deterministic StoreSteps.
From LeanCageMain Require Import Main MainStructure.
From LeanCageArguments Require Import StringMachine StringPath ArgumentWords.
From LeanCageDigest Require Import DigestStructure DigestWords DigestValues DigestCharacter DigestEntry DigestLoop StringControl.
Import ListNotations.
Open Scope nat_scope.
Theorem digest_source cell m p bytes k : c_string m p bytes->
 exists count,count<=2068 /\ string_path main_ge cell(digest_initial(address_value p)k m)count
 (Returnstate(Val.of_bool(digest_valid bytes))(call_cont k)m).
Proof.
 intros OWN;pose proof(argument_strlen_range _ _ _ OWN)as RANGE.
 destruct(Z.eq_dec(Z.of_nat(length bytes))64)as[SIZE|BAD].
 - assert(NATSIZE:length bytes=64)by lia.
   destruct(digest_loop_source m p [] bytes(digest_initialized(digest_env(address_value p))64)k
    OWN NATSIZE(digest_initialized_registers p 64))as[count[BOUND TAIL]].
   exists(4+1+(8+count));split;[rewrite NATSIZE in BOUND;lia|].
   unfold digest_valid;rewrite SIZE;cbn[Z.eqb andb].
   eapply string_path_trans with(n:=4);[apply string_store_path with(m:=m);apply digest_to_strlen|].
   eapply string_next;[apply string_strlen_edge;exact OWN|].
   unfold strlen_value;rewrite SIZE.
   eapply string_path_trans with(n:=8);apply string_store_path with(m:=m);
   [apply digest_good_length|exact TAIL].
 - exists 9;split;[lia|].
   assert(EQ:(Z.of_nat(length bytes)=?64)%Z=false)by(apply Z.eqb_neq;exact BAD).
   unfold digest_valid;rewrite EQ;cbn[andb].
   eapply string_path_trans with(n:=4);[apply string_store_path with(m:=m);apply digest_to_strlen|].
   eapply string_next;[apply string_strlen_edge;exact OWN|].
   apply string_store_path with(m:=m);apply digest_bad_length;[lia|exact BAD].
Qed.
Theorem digest_call_certificate cell m p bytes : c_string m p bytes->
 string_certificate main_ge cell(fun after=>after=m)
 (fun value after=>value=Val.of_bool(digest_valid bytes) /\ after=m)2068
 (digest_initial(address_value p)Kstop m).
Proof.
 intros OWN;destruct(digest_source cell m p bytes Kstop OWN)as[count[BOUND PATH]].
 eapply string_certificate_weaken;[|exact BOUND].
 replace count with(count+0)at 1 by lia.
 eapply string_path_certificate;[exact PATH|reflexivity|constructor;auto].
Qed.
Theorem digest_all_prefixes cell m p bytes events target : c_string m p bytes->
 string_steps main_ge cell(live(digest_initial(address_value p)Kstop m))events target->
 routine_memory target=m /\ string_cost events<=2069 /\
 (forall s,target=live s->exists remaining,string_certificate main_ge cell(fun after=>after=m)
 (fun value after=>value=Val.of_bool(digest_valid bytes) /\ after=m)remaining s).
Proof.
 intros OWN RUN;exact(string_certificate_all_prefixes _ _ _ _ _ _
 (digest_call_certificate _ _ _ _ OWN)_ _ RUN).
Qed.
Theorem digest_all_returns cell m p bytes events value after : c_string m p bytes->
 string_steps main_ge cell(live(digest_initial(address_value p)Kstop m))events
 (live(Returnstate value Kstop after))->
 value=Val.of_bool(digest_valid bytes) /\ after=m.
Proof.
 intros OWN RUN;exact(string_certificate_all_returns _ _ _ _ _ _ _ _ _
 (digest_call_certificate _ _ _ _ OWN)RUN).
Qed.
Theorem digest_defined_prefix cell m p bytes events s : c_string m p bytes->
 string_steps main_ge cell(live(digest_initial(address_value p)Kstop m))events(live s)->
 s=Returnstate(Val.of_bool(digest_valid bytes))Kstop m \/
 (exists ev next,string_waiting ev=false /\ ev<>string_loss /\ string_step main_ge cell(live s)ev(live next)).
Proof.
 intros OWN RUN;destruct(string_certificate_defined _ _ _ _ _ _ _ _
 (digest_call_certificate _ _ _ _ OWN)RUN)as[[v[after[SAME[VALUE MEM]]]]|PROGRESS];
 [left;subst;reflexivity|right;exact PROGRESS].
Qed.
Theorem digest_source_witnesses cell m p bytes k : c_string m p bytes->
 exists count,count<=2068 /\
 (exists events,string_cost events=count /\ string_steps main_ge cell
 (live(digest_initial(address_value p)k m))events
 (live(Returnstate(Val.of_bool(digest_valid bytes))(call_cont k)m))) /\
 (forall n,n<=count->exists events,string_cost events=n /\ string_steps main_ge cell
 (live(digest_initial(address_value p)k m))(events++[string_loss])(dead m)).
Proof.
 intros OWN;destruct(digest_source cell m p bytes k OWN)as[count[BOUND PATH]].
 exists count;split;[exact BOUND|];split;[eapply string_path_actual;exact PATH|].
 exact(string_path_loss_every_prefix _ _ _ _ _ PATH).
Qed.
Theorem digest_initial_wait_loss cell m p bytes k n : c_string m p bytes->
 exists prefix,string_cost prefix=4 /\ string_steps main_ge cell
 (live(digest_initial(address_value p)k m))(prefix++repeat string_wait n++[string_loss])(dead m).
Proof.
 intros OWN;destruct(string_path_actual main_ge cell _ 4 _
 (string_store_path main_ge cell _ _ _ m(digest_to_strlen p k m)))as[prefix[COST RUN]].
 exists prefix;split;[exact COST|];eapply string_steps_trans;[exact RUN|].
 eapply strlen_wait_then_loss;exact OWN.
Qed.
