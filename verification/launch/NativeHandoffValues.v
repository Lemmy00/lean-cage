(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.values: The actual source's bytes determine the imported worker values. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory.
From LeanImport Require Import Lean.
Require Import ArgumentsImport ArgumentConnection ArgumentValues.
From EntryNative Require Import NativeValues.
From LeanCageMainNumber Require Import NumberMath.
Import ListNotations.
Local Close Scope lean_scope.
Local Open Scope Z_scope.

Fixpoint argument_byte_lists (strings:list(list Byte.int)) : List_inst1(List_inst1 UInt8) :=
  match strings with
  | []=>List_nil_inst1(List_inst1 UInt8)
  | bytes::rest=>List_cons_inst1(List_inst1 UInt8)(argument_bytes bytes)(argument_byte_lists rest)
  end.

Definition handoff_value_agreement uid input output errors failure mode root fault argv
    uidword inputword outputword errorsword failureword modem rootm faultm argvm :=
  And(Lean.eq uid(Nat_of_nat(Z.to_nat uidword)))
    (And(Lean.eq input(Nat_of_nat(Z.to_nat inputword)))
      (And(Lean.eq output(Nat_of_nat(Z.to_nat outputword)))
        (And(Lean.eq errors(Nat_of_nat(Z.to_nat errorsword)))
          (And(Lean.eq failure(Nat_of_nat(Z.to_nat failureword)))
            (And(Lean.eq mode(argument_bytes modem))
              (And(Lean.eq root(argument_bytes rootm))
                (And(Lean.eq fault(argument_bytes faultm))
                  (Lean.eq argv(argument_byte_lists argvm))))))))).

Theorem handoff_decoded_value bytes word limit decoded :
  decimal_number bytes=Some word ->
  Lean.eq(LeanCage_Entry_Arguments_unsigned limit(argument_bytes bytes))(Option_some_inst1 Lean.Nat decoded) ->
  Lean.eq decoded(Nat_of_nat(Z.to_nat word)).
Proof.
  intros NUMBER PARSED.
  destruct(proj1(decimal_number_exact bytes word)NUMBER)as[NONEMPTY[DIGITS[VALUE RANGE]]].
  assert(EQUAL:decoded=Nat_of_nat(Z.to_nat word)).
  { apply argument_nat_injective;rewrite nat2Natid.
    pose proof(argument_unsigned_value _ _ _ PARSED)as DECODED.
    pose proof(argument_fold_native bytes 0 DIGITS)as NATIVE.
    change(Z.of_nat(argument_fold 0(argument_bytes bytes))=decimal_fold 0 bytes)in NATIVE.
    rewrite <- VALUE in NATIVE.
    rewrite DECODED;apply Nat2Z.inj;rewrite Z2Nat.id by lia;exact NATIVE. }
  rewrite EQUAL;constructor.
Qed.

(* The conclusion stays in SProp, like the strictly imported Lean proposition.
   In particular no existential witness is extracted from SProp into data. *)
Theorem handoff_imported_byte_values uidbytes inputbytes outputbytes errorsbytes failurebytes
    uidword inputword outputword errorsword failureword
    modem rootm faultm argvm uid input output errors failure mode root fault argv :
  decimal_number uidbytes=Some uidword ->
  decimal_number inputbytes=Some inputword ->
  decimal_number outputbytes=Some outputword ->
  decimal_number errorsbytes=Some errorsword ->
  decimal_number failurebytes=Some failureword ->
  LeanCage_Entry_ArgumentMeaning_byteValues uid input output errors failure mode root fault argv
    (argument_byte_lists(modem::uidbytes::rootm::inputbytes::outputbytes::errorsbytes::
      failurebytes::faultm::argvm)) ->
  handoff_value_agreement uid input output errors failure mode root fault argv
    uidword inputword outputword errorsword failureword modem rootm faultm argvm.
Proof.
  intros UID INPUT OUTPUT ERRORS FAILURE MEANING.
  unfold LeanCage_Entry_ArgumentMeaning_byteValues in MEANING.
  destruct MEANING as[ut MEANING];destruct MEANING as[it MEANING];
    destruct MEANING as[ot MEANING];destruct MEANING as[et MEANING];destruct MEANING as[ft MEANING].
  destruct MEANING as[WIRE MEANING];destruct MEANING as[UP MEANING];
    destruct MEANING as[IP MEANING];destruct MEANING as[OP MEANING];destruct MEANING as[EP FP].
  assert(SAME:argument_byte_lists(modem::uidbytes::rootm::inputbytes::outputbytes::errorsbytes::
    failurebytes::faultm::argvm)=
    List_cons_inst1 _ mode(List_cons_inst1 _ ut(List_cons_inst1 _ root(List_cons_inst1 _ it
      (List_cons_inst1 _ ot(List_cons_inst1 _ et(List_cons_inst1 _ ft(List_cons_inst1 _ fault argv)))))))).
  { destruct WIRE;reflexivity. }
  cbn[argument_byte_lists]in SAME;inversion SAME;subst.
  constructor;[eapply handoff_decoded_value;[exact UID|exact UP]|].
  constructor;[eapply handoff_decoded_value;[exact INPUT|exact IP]|].
  constructor;[eapply handoff_decoded_value;[exact OUTPUT|exact OP]|].
  constructor;[eapply handoff_decoded_value;[exact ERRORS|exact EP]|].
  constructor;[eapply handoff_decoded_value;[exact FAILURE|exact FP]|].
  repeat constructor.
Qed.

Theorem handoff_imported_native_values uidbytes inputbytes outputbytes errorsbytes failurebytes
    uidword inputword outputword errorsword failureword modem rootm faultm argvm :
  decimal_number uidbytes=Some uidword ->
  decimal_number inputbytes=Some inputword ->
  decimal_number outputbytes=Some outputword ->
  decimal_number errorsbytes=Some errorsword ->
  decimal_number failurebytes=Some failureword ->
  LeanCage_Entry_ArgumentMeaning_nativeValues
    (Nat_of_nat(Z.to_nat uidword))(Nat_of_nat(Z.to_nat inputword))(Nat_of_nat(Z.to_nat outputword))
    (Nat_of_nat(Z.to_nat errorsword))(Nat_of_nat(Z.to_nat failureword))
    (argument_bytes modem)(argument_bytes rootm)(argument_bytes faultm)(argument_byte_lists argvm)
    (argument_byte_lists(modem::uidbytes::rootm::inputbytes::outputbytes::errorsbytes::failurebytes::faultm::argvm)).
Proof.
  intros UID INPUT OUTPUT ERRORS FAILURE.
  unfold LeanCage_Entry_ArgumentMeaning_nativeValues.
  intros uid input output errors failure mode root fault argv MEANING.
  exact(handoff_imported_byte_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    UID INPUT OUTPUT ERRORS FAILURE MEANING).
Qed.
