(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.values: Import the same actual descriptor identities and flags into ordinary Lean. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers Values.
From LeanImport Require Import Lean.
Require Import ArgumentsImport ArgumentValues.
From EntryNamespace Require Import NamespaceObjects.
Import ListNotations.
Local Close Scope lean_scope.
Local Open Scope nat_scope.

Definition descriptor_object_code object : nat:=match object with
  |ordinary_object identity=>identity*3
  |release_endpoint channel parent_endpoint=>channel*3+1
  |release_endpoint channel child_endpoint=>channel*3+2 end.
Definition native_descriptor_object object : Lean.Nat:=match object with
  |ordinary_object identity=>LeanCage_Entry_PhysicalHandoff_objectCode Nat_zero(Nat_of_nat identity)
  |release_endpoint channel parent_endpoint=>LeanCage_Entry_PhysicalHandoff_objectCode(Nat_of_nat 1)(Nat_of_nat channel)
  |release_endpoint channel child_endpoint=>LeanCage_Entry_PhysicalHandoff_objectCode(Nat_of_nat 2)(Nat_of_nat channel) end.
Definition native_descriptor_flag (flag:bool):ArgumentsImport.Bool:=if flag then Bool_true else Bool_false.

Lemma native_three : nat_of_Nat (OfNat_ofNat_inst1 Lean.Nat 3 (instOfNatNat 3))=3.
Proof. reflexivity. Qed.

Theorem native_descriptor_object_exact object:
  nat_of_Nat(native_descriptor_object object)=descriptor_object_code object.
Proof.
  destruct object as[identity|channel side];[|destruct side];
    unfold native_descriptor_object,LeanCage_Entry_PhysicalHandoff_objectCode;
    rewrite argument_add_exact,argument_mul_exact,!nat2Natid,native_three;
    cbn[descriptor_object_code nat_of_Nat];lia.
Qed.

Theorem native_descriptor_object_injective first second:
  native_descriptor_object first=native_descriptor_object second ->first=second.
Proof.
  intro SAME;apply(f_equal nat_of_Nat)in SAME;rewrite !native_descriptor_object_exact in SAME.
  destruct first as[a|a first_side],second as[b|b second_side];
    try destruct first_side;try destruct second_side;cbn[descriptor_object_code]in SAME;
    try(f_equal;lia);exfalso;lia.
Qed.

Definition native_table_objects(table:DescriptorTable)(fd:Lean.Nat):Option_inst1 Lean.Nat:=
  if Z.leb(Z.of_nat(nat_of_Nat fd))Int.max_signed then
    match table(Int.repr(Z.of_nat(nat_of_Nat fd)))with
    |Some binding=>Option_some_inst1 Lean.Nat(native_descriptor_object(descriptor_object binding))
    |None=>Option_none_inst1 Lean.Nat end
  else Option_none_inst1 Lean.Nat.
Definition native_table_cloexec(table:DescriptorTable)(fd:Lean.Nat):ArgumentsImport.Bool:=
  if Z.leb(Z.of_nat(nat_of_Nat fd))Int.max_signed then
    match table(Int.repr(Z.of_nat(nat_of_Nat fd)))with
    |Some binding=>native_descriptor_flag(descriptor_cloexec binding)
    |None=>Bool_false end
  else Bool_false.
Definition native_descriptor_number(fd:int):Lean.Nat:=Nat_of_nat(Z.to_nat(Int.unsigned fd)).

Theorem native_descriptor_number_signed fd:
  (0<=Int.signed fd)%Z ->
  native_descriptor_number fd=Nat_of_nat(Z.to_nat(Int.signed fd)).
Proof.
  intro NONNEGATIVE;unfold native_descriptor_number.
  rewrite Int.signed_eq_unsigned;[reflexivity|apply Int.signed_positive;lia].
Qed.

Lemma native_descriptor_number_valid fd:
  (0<=Int.signed fd)%Z ->
  Z.leb(Z.of_nat(nat_of_Nat(native_descriptor_number fd)))Int.max_signed=true /\
  Int.repr(Z.of_nat(nat_of_Nat(native_descriptor_number fd)))=fd.
Proof.
  intro NONNEGATIVE;unfold native_descriptor_number;rewrite nat2Natid.
  pose proof(Int.unsigned_range fd)as RANGE.
  assert(BOUND:(Int.unsigned fd<=Int.max_signed)%Z).
  { apply Int.signed_positive;lia. }
  split.
  - apply Z.leb_le;rewrite Z2Nat.id by lia;exact BOUND.
  - rewrite Z2Nat.id by lia;apply Int.repr_unsigned.
Qed.

Theorem actual_descriptor_produces_ordinary_binding table fd binding:
  (0<=Int.signed fd)%Z ->table fd=Some binding ->
  LeanCage_Entry_PhysicalHandoff_binding(native_table_objects table)(native_table_cloexec table)
    (native_descriptor_number fd)(native_descriptor_object(descriptor_object binding))
    (native_descriptor_flag(descriptor_cloexec binding)).
Proof.
  intros NONNEGATIVE PRESENT.
  destruct(native_descriptor_number_valid fd NONNEGATIVE)as[BOUND NUMBER].
  unfold LeanCage_Entry_PhysicalHandoff_binding,native_table_objects,native_table_cloexec.
  rewrite BOUND,NUMBER,PRESENT;constructor;constructor.
Qed.

Theorem absent_descriptor_produces_ordinary_none table fd:
  (0<=Int.signed fd)%Z ->table fd=None ->
  native_table_objects table(native_descriptor_number fd)=Option_none_inst1 Lean.Nat.
Proof.
  intros NONNEGATIVE ABSENT.
  destruct(native_descriptor_number_valid fd NONNEGATIVE)as[BOUND NUMBER].
  unfold native_table_objects;rewrite BOUND,NUMBER,ABSENT;reflexivity.
Qed.

Theorem handoff_owned_slot_survives table input output errors failure fd binding:
  table fd=Some binding ->In fd[input;output;errors;failure] ->fd<>Int.one ->
  exec_table(handoff_stdio_table table input output errors failure)fd=
    Some{|descriptor_object:=descriptor_object binding;descriptor_cloexec:=false|}.
Proof.
  intros PRESENT MEMBER NONSTDOUT.
  assert(STDOUT:Int.eq fd(Int.repr 1)=false)by(apply Int.eq_false;exact NONSTDOUT).
  destruct MEMBER as[SAME|[SAME|[SAME|[SAME|IMPOSSIBLE]]]];try contradiction;subst fd.
  all:unfold exec_table,handoff_stdio_table,handoff_flagged_table,descriptor_flags;
    rewrite PRESENT;
    repeat first[progress(cbn[descriptor_object descriptor_cloexec])|rewrite STDOUT|
      rewrite Int.eq_true|match goal with|-context[Int.eq ?a ?b]=>
        let E:=fresh "EQ" in destruct(Int.eq a b)eqn:E;try congruence end];reflexivity.
Qed.

Theorem handoff_owned_slot_produces_ordinary_binding table input output errors failure fd binding:
  table fd=Some binding ->In fd[input;output;errors;failure] ->fd<>Int.one ->
  (0<=Int.signed fd)%Z ->
  LeanCage_Entry_PhysicalHandoff_binding
    (native_table_objects(exec_table(handoff_stdio_table table input output errors failure)))
    (native_table_cloexec(exec_table(handoff_stdio_table table input output errors failure)))
    (native_descriptor_number fd)(native_descriptor_object(descriptor_object binding))Bool_false.
Proof.
  intros PRESENT MEMBER NONSTDOUT NONNEGATIVE.
  pose proof(handoff_owned_slot_survives _ _ _ _ _ _ _ PRESENT MEMBER NONSTDOUT)as SURVIVES.
  exact(actual_descriptor_produces_ordinary_binding _ _ _ NONNEGATIVE SURVIVES).
Qed.

Theorem handoff_owned_slot_produces_signed_binding table input output errors failure fd binding:
  table fd=Some binding ->In fd[input;output;errors;failure] ->fd<>Int.one ->
  (0<=Int.signed fd)%Z ->
  LeanCage_Entry_PhysicalHandoff_binding
    (native_table_objects(exec_table(handoff_stdio_table table input output errors failure)))
    (native_table_cloexec(exec_table(handoff_stdio_table table input output errors failure)))
    (Nat_of_nat(Z.to_nat(Int.signed fd)))(native_descriptor_object(descriptor_object binding))Bool_false.
Proof.
  intros PRESENT MEMBER NONSTDOUT NONNEGATIVE.
  rewrite <-(native_descriptor_number_signed fd NONNEGATIVE).
  eapply handoff_owned_slot_produces_ordinary_binding;eassumption.
Qed.
