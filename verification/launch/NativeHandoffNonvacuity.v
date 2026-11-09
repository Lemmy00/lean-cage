(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.acceptance: The actual loader and source guest admit a concrete useful image path. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffArguments NativeHandoffAllocation
  NativeHandoffInput NativeHandoffStructure NativeHandoffInitial NativeHandoffMemory NativeHandoffLoop NativeHandoffExec NativeHandoffGuest
  NativeHandoffUseful NativeHandoffInputWitness.
From LeanCageMainNumber Require Import NumberMath.
Import ListNotations.
Open Scope Z_scope.
Local Opaque handoff_ge handoff_symbol.

Definition handoff_admitted_example_encode index :=
  if Z.eqb index 3 then map Byte.repr[54;48] else[Byte.repr(52+index)].
Definition handoff_admitted_example_words :=
  handoff_original_words(Int.repr 4)(Int.repr 5)(Int.repr 6)(Int.repr 60).
Lemma handoff_admitted_example_checked : handoff_descriptors_checked handoff_admitted_example_words 4.
Proof.
  intros index BOUND;assert(CASES:index=0 \/index=1 \/index=2 \/index=3)by lia.
  destruct CASES as[EQ|[EQ|[EQ|EQ]]];subst index;split;try(solve[vm_compute;discriminate]).
  all:intros previous PREVIOUS;assert(CASES:previous=0 \/previous=1 \/previous=2)by lia.
  all:destruct CASES as[EQ|[EQ|EQ]];subst previous;vm_compute;reflexivity||lia.
Qed.
Lemma handoff_admitted_example_encoding : handoff_useful_encoding handoff_admitted_example_words handoff_admitted_example_encode.
Proof.
  intros index BOUND;assert(CASES:index=0 \/index=1 \/index=2 \/index=3)by lia.
  destruct CASES as[EQ|[EQ|[EQ|EQ]]];subst index;vm_compute.
  all:split;[lia|]. all:split;[repeat constructor;discriminate|reflexivity].
Qed.

Theorem handoff_source_useful_image : exists initial cell input before b after caller prefix,
  Genv.init_mem EntrySource.prog=Some initial /\handoff_borrowed_input cell before input /\
  handoff_image_snapshot cell input(Int.repr 4)(Int.repr 5)(Int.repr 6)(Int.repr 60)
    (Callstate entry_exec_definition
      [Vptr(handoff_symbol EntrySource.___stringlit_111)Ptrofs.zero;
       Vptr(handoff_arguments b)Ptrofs.zero;Vptr(handoff_environment b)Ptrofs.zero]
      (handoff_exec_cont(handoff_locals_env b)caller(Kseq(guest_tail 24(fn_body EntrySource.f_guest))Kstop))after) /\
  entry_handoff_steps handoff_ge cell
    (live(Callstate(Internal EntrySource.f_guest)
      [Vint(Int.repr 4);Vint(Int.repr 5);Vint(Int.repr 6);Vint(Int.repr 60)]Kstop before))
    (prefix++[entry_image(Vptr(handoff_symbol EntrySource.___stringlit_111)Ptrofs.zero)
      (Vptr(handoff_arguments b)Ptrofs.zero)(Vptr(handoff_environment b)Ptrofs.zero)])(dead after).
Proof.
  destruct handoff_actual_input_exists as[initial[cell[input[before[INITIAL[INPUT[MODE UID]]]]]]].
  destruct handoff_example_uid_correct as[LENGTH[NONZERO PARSED]].
  assert(UIDBOUND:100000<=Int.unsigned(handoff_borrowed_uid input)<=100999)
    by(rewrite UID;change(100000<=100000<=100999);lia).
  assert(UIDPARSED:decimal_number handoff_example_uid=Some(Int.unsigned(handoff_borrowed_uid input)))
    by(rewrite UID;exact PARSED).
  destruct(handoff_useful_image cell input before(Int.repr 4)(Int.repr 5)(Int.repr 6)(Int.repr 60)Kstop
    handoff_example_uid handoff_admitted_example_encode INPUT MODE UIDBOUND handoff_admitted_example_checked
    LENGTH NONZERO UIDPARSED handoff_admitted_example_encoding)
    as[b[after[caller[prefix[SNAPSHOT[PREFIX RUN]]]]]].
  exists initial,cell,input,before,b,after,caller,prefix;split;[exact INITIAL|].
  split;[exact INPUT|]. split;assumption.
Qed.
