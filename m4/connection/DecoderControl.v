(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-decoder.source: Actual local free and boolean evaluations for all frame branches. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Slice Machine ClightSteps StoreSteps LocalAccess CallAccess GlobalReads ResultLayout ResultSource
  DecoderSource SourceReach.
Import ListNotations.
Open Scope Z_scope.

Lemma decoder_free_list : forall m local after,
  Mem.free m local 0 144 = Some after ->
  Mem.free_list m (blocks_of_env result_ge (decoder_env local)) = Some after.
Proof.
  intros. unfold decoder_env, result_env, blocks_of_env.
  cbn [PTree.elements PTree.xelements PTree.set PTree.set' PTree.empty empty_env].
  change (match Mem.free m local 0 144 with Some after => Some after | None => None end = Some after).
  rewrite H; reflexivity.
Qed.
Lemma decoder_local_return : forall a k local le m v w after,
  expression_value result_ge (decoder_env local) le m a v ->
  sem_cast v (typeof a) tint m = Some w ->
  Mem.free m local 0 144 = Some after ->
  store_edge result_ge (State f_decode_frame (Sreturn (Some a)) k (decoder_env local) le m)
    (Returnstate w (call_cont k) after).
Proof.
  intros. eapply certified_local_return_edge; [eassumption|exact H0|apply decoder_free_list; exact H1].
Qed.
Lemma cast_boolean_boolean : forall b m,
  sem_cast (Val.of_bool b) tint tbool m = Some (Val.of_bool b).
Proof. destruct b; reflexivity. Qed.
Lemma boolean_condition : forall b m,
  bool_val (Val.of_bool b) tint m = Some b.
Proof. destruct b; reflexivity. Qed.
Lemma boolean_typed_condition : forall b m,
  bool_val (Val.of_bool b) tbool m = Some b.
Proof. destruct b; reflexivity. Qed.

Ltac decoder_control_expression := first
  [apply value_int
  | eapply value_temp; WriteAll.lookup
  | eapply value_binary; [decoder_control_expression|decoder_control_expression|reflexivity]
  | eapply value_unary; [decoder_control_expression|reflexivity]
  | eapply value_cast; [decoder_control_expression|first [reflexivity|apply cast_boolean_boolean|apply bool_int_cast]]].
Ltac decoder_reach_route := eapply source_reaches_prepend;
  [first [assumption|left;reflexivity]|apply unchanged_store_edge; WriteAll.structural|].
Ltac decoder_reach_set := eapply source_reaches_prepend;
  [first [assumption|left;reflexivity]|apply unchanged_store_edge; eapply edge_set; decoder_control_expression|].
Ltac decoder_reach_if := eapply source_reaches_prepend;
  [first [assumption|left;reflexivity]|apply unchanged_store_edge; eapply edge_if;
    [decoder_control_expression|first [apply boolean_condition|apply boolean_typed_condition|reflexivity]]|].

Lemma cast_bool_zero_test : forall (b : bool),
  Int.eq (if b then Int.repr 0 else Int.repr 1) (Int.repr 0) = b.
Proof. destruct b; reflexivity. Qed.
Lemma bool_value_zero_test : forall (b : bool),
  Int.eq (if b then Int.repr 1 else Int.repr 0) (Int.repr 0) = negb b.
Proof. destruct b; reflexivity. Qed.
