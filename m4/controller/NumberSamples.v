(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.decimal: Exact source parsing, memory behavior and interruption. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata Events Clight.
Require Import Machine.
From LeanCageController Require Import NumberStructure NumberMath NumberMemory NumberStorage NumberSource NumberAllocation NumberWitnesses.
Import ListNotations.
Open Scope Z_scope.
Definition number_samples : list (list byte * option Z) := [
 (decimal_bytes [48], Some 0);
 (decimal_bytes [48;48;48;52;50], Some 42);
 (decimal_bytes [50;53;53], Some 255);
 (decimal_bytes [49;48;48;48;48;48], Some 100000);
 (decimal_bytes [52;50;57;52;57;54;55;50;57;53], Some 4294967295);
 (decimal_bytes [52;50;57;52;57;54;55;50;57;54], Some 4294967296);
 (decimal_bytes [57;50;50;51;51;55;50;48;51;54;56;53;52;55;55;53;56;48;55], Some 9223372036854775807);
 (decimal_bytes [57;50;50;51;51;55;50;48;51;54;56;53;52;55;55;53;56;48;56], Some 9223372036854775808);
 (decimal_bytes [49;56;52;52;54;55;52;52;48;55;51;55;48;57;53;53;49;54;49;53], Some 18446744073709551615);
 (decimal_bytes [49], Some 1);
 (decimal_bytes [], None);
 (decimal_bytes [45;49], None);
 (decimal_bytes [43;49], None);
 (decimal_bytes [32;49], None);
 (decimal_bytes [49;32], None);
 (decimal_bytes [49;10], None);
 (decimal_bytes [49;97], None);
 (decimal_bytes [49;128], None);
 (decimal_bytes [49;255], None);
 (decimal_bytes [49;56;52;52;54;55;52;52;48;55;51;55;48;57;53;53;49;54;49;54], None)].
Definition number_sample_valid sample :=
 Forall (fun b => b<>Byte.zero) (fst sample) /\
 Z.of_nat(length(fst sample))+9<=Ptrofs.modulus /\
 decimal_number(fst sample)=snd sample.
Definition number_sample_check (sample : list byte * option Z) :=
 forallb (fun b => negb(Byte.eq b Byte.zero)) (fst sample) &&
 (Z.of_nat(length(fst sample))+9 <=? Ptrofs.modulus) &&
 match decimal_number(fst sample),snd sample with
 | Some actual,Some expected => Z.eqb actual expected
 | None,None => true | _,_ => false end.
Lemma number_sample_check_sound sample : number_sample_check sample=true -> number_sample_valid sample.
Proof.
 unfold number_sample_check;rewrite !Bool.andb_true_iff;intros [[BYTES BOUND] VALUE].
 unfold number_sample_valid;split.
 - rewrite forallb_forall in BYTES;apply Forall_forall;intros b IN EQ.
   specialize(BYTES b IN);subst b;rewrite Byte.eq_true in BYTES;discriminate.
 - split;[now apply Z.leb_le|].
   destruct(decimal_number(fst sample)),(snd sample);try discriminate;[|reflexivity].
   apply Z.eqb_eq in VALUE;congruence.
Qed.
Theorem number_samples_pass : forallb number_sample_check number_samples=true.
Proof. vm_compute;reflexivity. Qed.
Theorem number_samples_checked : Forall number_sample_valid number_samples.
Proof.
 pose proof number_samples_pass as ALL;rewrite forallb_forall in ALL.
 apply Forall_forall;intros sample IN;apply number_sample_check_sound;exact(ALL sample IN).
Qed.
Theorem number_samples_actual_source ge cell sample : In sample number_samples ->
 (exists allocated block m count after,
 Mem.alloc Mem.empty 0 (Z.of_nat(length(number_allocation_bytes(fst sample))))=(allocated,block) /\
 Mem.storebytes allocated block 0 (map Byte(number_allocation_bytes(fst sample)))=Some m /\
 number_input m block Ptrofs.zero (fst sample) /\ number_output m block Ptrofs.zero /\
 number_post m block Ptrofs.zero (snd sample) after /\
 steps ge cell (live(number_initial (Vptr block Ptrofs.zero) (Vptr block Ptrofs.zero) Kstop m))
 (repeat (source_step E0) count) (live(Returnstate(number_code(snd sample)) Kstop after))) /\
 (exists allocated block before m out count after,
 Mem.alloc Mem.empty 0 (Z.of_nat(length(number_allocation_bytes(fst sample))))=(allocated,block) /\
 Mem.storebytes allocated block 0 (map Byte(number_allocation_bytes(fst sample)))=Some before /\
 Mem.alloc before 0 8=(m,out) /\ block<>out /\
 number_input m block Ptrofs.zero (fst sample) /\ number_output m out Ptrofs.zero /\
 number_post m out Ptrofs.zero (snd sample) after /\
 steps ge cell (live(number_initial (Vptr block Ptrofs.zero) (Vptr out Ptrofs.zero) Kstop m))
 (repeat (source_step E0) count) (live(Returnstate(number_code(snd sample)) Kstop after))).
Proof.
 intros MEMBER;pose proof number_samples_checked as ALL.
 rewrite Forall_forall in ALL; specialize(ALL sample MEMBER).
 destruct ALL as [NONZERO [BOUND VALUE]]. rewrite <- VALUE;split.
 - exact(number_overlapping_source Mem.empty ge cell (fst sample) NONZERO BOUND).
 - exact(number_separate_source Mem.empty ge cell (fst sample) NONZERO BOUND).
Qed.
