(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-receiver.classification: Source result-constructor boundaries and owned private error-byte reads. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs
  Ctypes Ctypesdefs Cop Clight.
Require Import Slice Machine ClightSteps StoreSteps WriteAll LocalAccess CallAccess CallPaths Library Readers
  ResultLayout ResultSource FrameBytes SourceReach DecoderControl ReceiverSource ReceiverReadSource
  ReceiverReadMemory ReceiverChoice.
Import ListNotations.
Open Scope Z_scope.

Definition receiver_choice_copy choice :=
  Sassign(Evar _result__1 result_type)(Evar(receiver_choice_ident choice)result_type).
Definition receiver_choice_cont b choice le k := Kcall None f_m4_collect_failure(receiver_env b)le
  (Kseq(receiver_choice_copy choice)(Kseq receiver_copy_return k)).
Definition receiver_choice_call b choice le k m :=
  Callstate(Internal f_result_of)
    (result_args(receiver_choice_block b choice)0(rc_kind choice)(rc_stage choice)(rc_detail choice)(rc_entry choice))
    (receiver_choice_cont b choice le k)m.
Definition receiver_selection_boundary b choice original k m s :=
  exists le,s=receiver_choice_call b choice le k m /\ receiver_kept original le.

Theorem receiver_result_symbol : exists symbol,
  Genv.find_symbol result_ge _result_of=Some symbol /\
  Genv.find_funct result_ge(Vptr symbol Ptrofs.zero)=Some(Internal f_result_of).
Proof. eexists;split;vm_compute;reflexivity. Qed.
Theorem receiver_reader_symbol : exists symbol,
  Genv.find_symbol result_ge _get32=Some symbol /\
  Genv.find_funct result_ge(Vptr symbol Ptrofs.zero)=Some(Internal f_get32).
Proof. eexists;split;vm_compute;reflexivity. Qed.

Lemma receiver_addrof : forall ge e le m a ty b ofs,
  location_value ge e le m a b ofs -> expression_value ge e le m(Eaddrof a ty)(Vptr b ofs).
Proof.
  intros ge e le m a ty b ofs[REAL UNIQUE];split;[constructor;exact REAL|].
  intros other EV;inversion EV;subst.
  - match goal with LV : eval_lvalue _ _ _ _ a _ _ _ |- _=>
      destruct(UNIQUE _ _ _ LV)as[BL[OFF BF]];subst end;reflexivity.
  - match goal with LV : eval_lvalue _ _ _ _(Eaddrof _ _) _ _ _ |- _=>inversion LV end.
Qed.

Lemma receiver_buffer_readable : forall cell b m bytes,
  receiver_buffer cell b m bytes ->
  readable_bytes m{|address_block:=rb_bytes b;address_offset:=0|}bytes.
Proof.
  intros cell b m bytes[LEN[TLS[NE[PERMS LOAD]]]];split;[|exact LOAD].
  change(0<=0<Ptrofs.modulus /\ 0+Z.of_nat(length bytes)<=Ptrofs.modulus /\
    Z.of_nat(length bytes)<=Int64.max_unsigned).
  change Ptrofs.modulus with 18446744073709551616;change Int64.max_unsigned with 18446744073709551615;lia.
Qed.

Lemma receiver_eight_from_word : forall (bytes : list Byte.int),
  (length bytes<=9)%nat ->
  Int64.eq(Int64.repr(Z.of_nat(length bytes)))(Int64.repr 8)=true -> length bytes=8%nat.
Proof.
  intros bytes BOUND EQ;apply Int64.same_if_eq in EQ;apply(f_equal Int64.unsigned)in EQ.
  rewrite !unsigned_small in EQ by lia;lia.
Qed.

Ltac receiver_choice_expression := first
  [solve[receiver_expression]
  |eapply receiver_addrof;receiver_location
  |eapply binary_expression_value;[receiver_choice_expression|receiver_choice_expression|reflexivity]
  |eapply cast_expression_value;[receiver_choice_expression|reflexivity]].
Ltac receiver_choice_arguments := first
  [apply no_argument_values
  |eapply cons_argument_values;[receiver_choice_expression|reflexivity|receiver_choice_arguments]].
Ltac receiver_choice_route := eapply source_reaches_prepend;
  [reflexivity|apply unchanged_store_edge;WriteAll.structural|].
Ltac receiver_choice_set := eapply source_reaches_prepend;
  [reflexivity|apply unchanged_store_edge;eapply edge_set;decoder_control_expression|].
Ltac receiver_choice_if := eapply source_reaches_prepend;
  [reflexivity|apply unchanged_store_edge;eapply edge_if;
    [decoder_control_expression|first[apply boolean_condition|apply boolean_typed_condition|reflexivity]]|].
Ltac receiver_choice_source_call symbol function :=
  eapply source_reaches_prepend;[reflexivity| |];
  [eapply certified_call_edge;[reflexivity|
    apply old_expression_value;eapply value_function;
      [unfold receiver_env;cbn;reflexivity|exact symbol|reflexivity]|
    receiver_choice_arguments|exact function|reflexivity]|].
