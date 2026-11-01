(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.decimal: Exact source parsing, memory behavior and interruption. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata Events Clight.
Require Import Machine.
From LeanCageController Require Import NumberStructure NumberMath NumberMemory NumberStorage NumberSource NumberAllocation.
Import ListNotations.
Open Scope Z_scope.
Theorem number_overlapping_source base ge cell bytes :
 Forall (fun b => b<>Byte.zero) bytes -> Z.of_nat(length bytes)+9<=Ptrofs.modulus ->
 exists allocated block m count after,
 Mem.alloc base 0 (Z.of_nat(length(number_allocation_bytes bytes)))=(allocated,block) /\
 Mem.storebytes allocated block 0 (map Byte(number_allocation_bytes bytes))=Some m /\
 number_input m block Ptrofs.zero bytes /\ number_output m block Ptrofs.zero /\
 number_post m block Ptrofs.zero (decimal_number bytes) after /\
 steps ge cell (live(number_initial (Vptr block Ptrofs.zero) (Vptr block Ptrofs.zero) Kstop m))
 (repeat (source_step E0) count) (live(Returnstate (number_code(decimal_number bytes)) Kstop after)).
Proof.
 intros NE SIZE.
 destruct(number_overlapping_allocation base bytes NE SIZE)
 as [allocated [block [m [ALLOC [STORE [INPUT OUTPUT]]]]]].
 destruct(number_source_execution ge cell m block Ptrofs.zero bytes block Ptrofs.zero Kstop INPUT OUTPUT)
 as [count [after [POST RUN]]].
 exists allocated,block,m,count,after;repeat first [assumption|split].
Qed.
Theorem number_separate_source base ge cell bytes :
 Forall (fun b => b<>Byte.zero) bytes -> Z.of_nat(length bytes)+9<=Ptrofs.modulus ->
 exists allocated block before m out count after,
 Mem.alloc base 0 (Z.of_nat(length(number_allocation_bytes bytes)))=(allocated,block) /\
 Mem.storebytes allocated block 0 (map Byte(number_allocation_bytes bytes))=Some before /\
 Mem.alloc before 0 8=(m,out) /\ block<>out /\
 number_input m block Ptrofs.zero bytes /\ number_output m out Ptrofs.zero /\
 number_post m out Ptrofs.zero (decimal_number bytes) after /\
 steps ge cell (live(number_initial (Vptr block Ptrofs.zero) (Vptr out Ptrofs.zero) Kstop m))
 (repeat (source_step E0) count) (live(Returnstate(number_code(decimal_number bytes)) Kstop after)).
Proof.
 intros NE SIZE.
 destruct(number_separate_allocation base bytes NE SIZE)
 as [allocated [block [before [m [out [ALLOC [STORE [OUT [DIFFERENT [INPUT OUTPUT]]]]]]]]]].
 destruct(number_source_execution ge cell m block Ptrofs.zero bytes out Ptrofs.zero Kstop INPUT OUTPUT)
 as [count [after [POST RUN]]].
 exists allocated,block,before,m,out,count,after;repeat first [assumption|split].
Qed.
