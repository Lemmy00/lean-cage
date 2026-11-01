(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.digest: Accepted, rejected, high-byte and early-NUL source witnesses. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Values Memory Globalenvs Ctypes Clight.
Require Import Machine Library.
From LeanCageMain Require Import Main MainStructure.
From LeanCageArguments Require Import StringMachine StringPath.
From LeanCageDigest Require Import DigestStructure DigestWords DigestSource DigestWitnesses.
Import ListNotations.
Open Scope Z_scope.
Definition digest_repeat b n := repeat(Byte.repr b)n.
Definition digest_last b := digest_repeat 97 63++[Byte.repr b].
Definition digest_cases:list(list Byte.int):=
 [digest_repeat 48 64;digest_repeat 57 64;digest_repeat 97 64;digest_repeat 102 64;
 concat(repeat(map Byte.repr[48;57;97;102])16);
 [];digest_repeat 97 63;digest_repeat 97 65;digest_repeat 65 64;
 digest_last 47;digest_last 58;digest_last 96;digest_last 103;
 digest_last 128;digest_last 255;digest_last 32;
 Byte.repr 103::digest_repeat 97 63;digest_repeat 195 64].
Theorem digest_cases_admissible : forallb digest_input_admissibleb digest_cases=true.
Proof. vm_compute;reflexivity. Qed.
Theorem digest_cases_outcomes : map digest_valid digest_cases=
 [true;true;true;true;true;false;false;false;false;false;false;false;false;false;false;false;false;false].
Proof. vm_compute;reflexivity. Qed.
Theorem every_digest_case_allocated cell bytes : In bytes digest_cases->
 exists initial m p count,Genv.init_mem Main.prog=Some initial /\ c_string m p bytes /\
 (count<=2068)%nat /\ string_path main_ge cell(digest_initial(address_value p)Kstop m)count
 (Returnstate(Val.of_bool(digest_valid bytes))Kstop m).
Proof.
 intros IN;pose proof digest_cases_admissible as VALID;rewrite forallb_forall in VALID.
 destruct(allocated_digest_source cell bytes(digest_input_admissible_sound bytes(VALID bytes IN)))
 as[initial[m[p[count[INIT[OLD[OWN[BOUND PATH]]]]]]]].
 exists initial,m,p,count;auto.
Qed.
Theorem every_digest_case_loss cell bytes : In bytes digest_cases->
 exists m p count,(count<=2068)%nat /\ forall n,(n<=count)%nat->exists events,string_cost events=n /\
 string_steps main_ge cell(live(digest_initial(address_value p)Kstop m))(events++[string_loss])(dead m).
Proof.
 intros IN;destruct(every_digest_case_allocated cell bytes IN)as[initial[m[p[count[INIT[OWN[BOUND PATH]]]]]]].
 exists m,p,count;split;[exact BOUND|];exact(string_path_loss_every_prefix _ _ _ _ _ PATH).
Qed.
Theorem every_digest_case_wait cell bytes n : In bytes digest_cases->
 exists m p prefix,string_cost prefix=4%nat /\
 string_steps main_ge cell(live(digest_initial(address_value p)Kstop m))
 (prefix++repeat string_wait n++[string_loss])(dead m).
Proof.
 intros IN;destruct(every_digest_case_allocated cell bytes IN)as[initial[m[p[count[INIT[OWN[BOUND PATH]]]]]]].
 destruct(digest_initial_wait_loss cell m p bytes Kstop n OWN)as[prefix[COST RUN]].
 exists m,p,prefix;auto.
Qed.
Theorem digest_nul_boundary_cases cell n : In n[32%nat;64%nat]->
 exists initial m p count,Genv.init_mem Main.prog=Some initial /\
 Mem.loadbytes m(address_block p)(address_offset p)(Z.of_nat(n+3))=
 Some(map Byte(digest_repeat 97 n++[Byte.zero;Byte.repr 255;Byte.repr 65])) /\
 (count<=2068)%nat /\ string_path main_ge cell(digest_initial(address_value p)Kstop m)count
 (Returnstate(Val.of_bool(Nat.eqb n 64))Kstop m).
Proof.
 intros IN;assert(VALID:digest_input_admissible(digest_repeat 97 n)).
 { apply digest_input_admissible_sound;destruct IN as[EQ|[EQ|[]]];subst;vm_compute;reflexivity. }
 destruct(digest_trailing_bytes_source cell(digest_repeat 97 n)[Byte.repr 255;Byte.repr 65]VALID)
 as[initial[m[p[count[INIT[OLD[RAW[BOUND PATH]]]]]]]].
 exists initial,m,p,count;split;[exact INIT|];split.
 - unfold digest_repeat in RAW;rewrite length_app,repeat_length in RAW;exact RAW.
 - split;[exact BOUND|].
   assert(OUT:digest_valid(digest_repeat 97 n)=Nat.eqb n 64).
   { destruct IN as[EQ|[EQ|[]]];subst;vm_compute;reflexivity. }
   rewrite OUT in PATH;exact PATH.
Qed.
