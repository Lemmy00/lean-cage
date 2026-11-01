(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.decimal: Exact source parsing, memory behavior and interruption. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata Events Clight.
Require Import Machine Deterministic.
From LeanCageController Require Import NumberStructure NumberMath NumberMemory NumberStorage NumberSource.
Import ListNotations.
Open Scope Z_scope.
Definition number_outside (output : Values.block) ofs block pos :=
 block<>output \/ pos<Ptrofs.unsigned ofs \/ Ptrofs.unsigned ofs+8<=pos.
Lemma number_post_store before output ofs value after :
 number_post before output ofs (Some value) after ->
 Mem.store Mint64 before output (Ptrofs.unsigned ofs) (Vlong(Int64.repr value))=Some after.
Proof.
 unfold number_post,Mem.storev.
 destruct(zle (Ptrofs.unsigned ofs+size_chunk Mint64) Ptrofs.modulus);[auto|discriminate].
Qed.
Lemma number_memory_outside before output ofs parsed after :
 number_memory before output ofs parsed after ->
 Mem.unchanged_on (number_outside output ofs) before after.
Proof.
 intros [SAME|POST];[subst;apply Mem.unchanged_on_refl|].
 destruct parsed as [value|];[|cbn [number_post] in POST;subst;apply Mem.unchanged_on_refl].
 eapply Mem.store_unchanged_on;[apply number_post_store;exact POST|].
 intros pos RANGE BAD;unfold number_outside in BAD;cbn in RANGE;intuition lia.
Qed.
Lemma number_memory_permissions before output ofs parsed after :
 number_memory before output ofs parsed after ->
 forall block pos kind perm, Mem.perm before block pos kind perm <-> Mem.perm after block pos kind perm.
Proof.
 intros [SAME|POST];[subst;tauto|].
 destruct parsed as [value|];[|cbn [number_post] in POST;subst;tauto].
 apply number_post_store in POST;intros;split;
 [eapply Mem.perm_store_1|eapply Mem.perm_store_2];eassumption.
Qed.
Theorem number_source_outside ge cell m block ofs bytes out outofs events target :
 number_input m block ofs bytes -> number_output m out outofs ->
 steps ge cell (live(number_initial (Vptr block ofs) (Vptr out outofs) Kstop m)) events target ->
 Mem.unchanged_on (number_outside out outofs) m (routine_memory target).
Proof.
 intros INPUT OUTPUT RUN;apply number_memory_outside with (parsed:=decimal_number bytes).
 eapply number_source_prefix;eassumption.
Qed.
Theorem number_source_permissions ge cell m block ofs bytes out outofs events target :
 number_input m block ofs bytes -> number_output m out outofs ->
 steps ge cell (live(number_initial (Vptr block ofs) (Vptr out outofs) Kstop m)) events target ->
 forall b pos kind perm, Mem.perm m b pos kind perm <-> Mem.perm (routine_memory target) b pos kind perm.
Proof.
 intros INPUT OUTPUT RUN;apply number_memory_permissions with (output:=out) (ofs:=outofs) (parsed:=decimal_number bytes).
 eapply number_source_prefix;eassumption.
Qed.
Theorem number_rejection_unchanged ge cell m block ofs bytes out outofs events target :
 number_input m block ofs bytes -> number_output m out outofs -> decimal_number bytes=None ->
 steps ge cell (live(number_initial (Vptr block ofs) (Vptr out outofs) Kstop m)) events target ->
 routine_memory target=m.
Proof.
 intros INPUT OUTPUT REJECT RUN.
 pose proof(number_source_prefix ge cell m block ofs bytes out outofs events target INPUT OUTPUT RUN) as SAFE.
 rewrite REJECT in SAFE;destruct SAFE;assumption.
Qed.
Theorem number_success_value ge cell m block ofs bytes out outofs events after :
 number_input m block ofs bytes -> number_output m out outofs ->
 steps ge cell (live(number_initial (Vptr block ofs) (Vptr out outofs) Kstop m)) events
 (live(Returnstate (Vint Int.zero) Kstop after)) ->
 exists value, decimal_number bytes=Some value /\ 0<=value<=decimal_max /\
 Mem.load Mint64 after out (Ptrofs.unsigned outofs)=Some(Vlong(Int64.repr value)).
Proof.
 intros INPUT OUTPUT RUN.
 destruct(number_source_return ge cell m block ofs bytes out outofs events (Vint Int.zero) after INPUT OUTPUT RUN) as [CODE POST].
 destruct(decimal_number bytes) as [value|] eqn:PARSED;[|discriminate].
 exists value;split;[reflexivity|]. split.
 - apply decimal_number_exact in PARSED;tauto.
 - apply number_post_store in POST.
   exact (Mem.load_store_same _ _ _ _ _ _ POST).
Qed.
Theorem number_completed_acceptance ge cell m block ofs bytes out outofs events value after :
 number_input m block ofs bytes -> number_output m out outofs ->
 steps ge cell (live(number_initial (Vptr block ofs) (Vptr out outofs) Kstop m)) events
 (live(Returnstate value Kstop after)) ->
 (value=Vint Int.zero <-> bytes<>[] /\ Forall decimal_digit_ok bytes /\ decimal_fold 0 bytes<=decimal_max).
Proof.
 intros INPUT OUTPUT RUN.
 destruct(number_source_return ge cell m block ofs bytes out outofs events value after INPUT OUTPUT RUN) as [CODE POST].
 rewrite CODE;destruct(decimal_number bytes) as [parsed|] eqn:PARSED.
 - apply decimal_number_exact in PARSED;unfold number_code;split;intros;[destruct PARSED as [NE [DIG [VALUE RANGE]]];subst;tauto|reflexivity].
 - split;[discriminate|]. intros [NE [DIG BOUND]].
   assert (OK : decimal_number bytes=Some(decimal_fold 0 bytes)).
   { apply decimal_number_exact;split;[exact NE|]. split;[exact DIG|]. split;[reflexivity|].
     split;[apply decimal_fold_increasing;[lia|exact DIG]|exact BOUND]. }
   congruence.
Qed.
