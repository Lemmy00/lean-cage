(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.decimal: Exact source parsing, memory behavior and interruption. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata.
Require Import Readers WriteMemory.
From LeanCageController Require Import NumberMath NumberMemory.
Import ListNotations.
Open Scope Z_scope.
Definition number_allocation_bytes bytes := (bytes++[Byte.zero])++repeat Byte.zero 8.
Theorem number_overlapping_allocation base bytes :
 Forall (fun b => b<>Byte.zero) bytes ->
 Z.of_nat(length bytes)+9<=Ptrofs.modulus ->
 exists allocated block m,
 Mem.alloc base 0 (Z.of_nat(length(number_allocation_bytes bytes)))=(allocated,block) /\
 Mem.storebytes allocated block 0 (map Byte (number_allocation_bytes bytes))=Some m /\
 number_input m block Ptrofs.zero bytes /\ number_output m block Ptrofs.zero.
Proof.
 intros NONZERO BOUND.
 destruct(allocated_bytes base (number_allocation_bytes bytes)) as [allocated [block [m [ALLOC [STORE LOAD]]]]].
 assert (SIZE : Z.of_nat(length(number_allocation_bytes bytes))=Z.of_nat(length bytes)+9).
 { unfold number_allocation_bytes;rewrite !length_app,repeat_length;cbn;lia. }
 exists allocated,block,m;split;[exact ALLOC|]. split;[exact STORE|]. split.
 - unfold number_input;change (Ptrofs.unsigned Ptrofs.zero) with 0.
   split;[rewrite length_app;cbn;lia|]. split;[exact NONZERO|].
   exact(load_first m block 0 (bytes++[Byte.zero]) (repeat Byte.zero 8) LOAD).
 - unfold number_output;change (Ptrofs.unsigned Ptrofs.zero) with 0.
   split;[change Ptrofs.modulus with 18446744073709551616;lia|].
   eapply Mem.storebytes_valid_access_1;[exact STORE|].
   eapply Mem.valid_access_implies with (p1:=Freeable);[|constructor].
   eapply Mem.valid_access_alloc_same;[exact ALLOC|lia|cbn;rewrite SIZE;lia|].
   exists 0;reflexivity.
Qed.
Theorem number_separate_allocation (base : mem) bytes :
 Forall (fun b => b<>Byte.zero) bytes ->
 Z.of_nat(length bytes)+9<=Ptrofs.modulus ->
 exists allocated block before m out,
 Mem.alloc base 0 (Z.of_nat(length(number_allocation_bytes bytes)))=(allocated,block) /\
 Mem.storebytes allocated block 0 (map Byte (number_allocation_bytes bytes))=Some before /\
 Mem.alloc before 0 8=(m,out) /\
 block<>out /\ number_input m block Ptrofs.zero bytes /\ number_output m out Ptrofs.zero.
Proof.
 intros NONZERO BOUND.
 destruct(number_overlapping_allocation base bytes NONZERO BOUND)
 as [allocated [block [before [ALLOC [STORE [INPUT OUTPUT]]]]]].
 destruct(Mem.alloc before 0 8) as [m out] eqn:OUT.
 assert (VALID : Mem.valid_block before block).
 { eapply Mem.storebytes_valid_block_1;[exact STORE|]. eapply Mem.valid_new_block;exact ALLOC. }
 exists allocated,block,before,m,out;split;[exact ALLOC|]. split;[exact STORE|]. split;[exact OUT|]. split.
 - intros EQ;subst out. eapply Mem.fresh_block_alloc;[exact OUT|exact VALID].
 - split.
   + destruct INPUT as [SIZE [NE LOAD]]. split;[exact SIZE|]. split;[exact NE|].
     rewrite (Mem.loadbytes_alloc_unchanged _ _ _ _ _ OUT _ _ _ VALID);exact LOAD.
   + unfold number_output;change(Ptrofs.unsigned Ptrofs.zero) with 0.
     split;[change Ptrofs.modulus with 18446744073709551616;lia|].
     eapply Mem.valid_access_implies with (p1:=Freeable);[|constructor].
     eapply Mem.valid_access_alloc_same;[exact OUT|lia|cbn;lia|exists 0;reflexivity].
Qed.
