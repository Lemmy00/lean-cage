(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.finish: Intended detail bounds make the returned exit status an exact small integer. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers Values Memory Clight.
Require Import Machine LibraryMachine ResultLayout FrameRecord SenderProgram FinishSource FinishProgram.
Open Scope Z_scope.
Definition finish_valid_detail r :=
  (fr_kind r=Int.zero -> Int.unsigned (fr_detail r)<=255) /\
  (fr_kind r=Int.repr 2 -> 1<=Int.unsigned (fr_detail r)<=64).
Theorem finish_exit_word_bounds : forall r,
  finish_valid_detail r -> 0<=Int.signed (finish_exit_word r)<=255.
Proof.
  intros r [EXIT SIGNAL];unfold finish_exit_word.
  destruct (Int.eq (fr_kind r) (Int.repr 7));[change (0<=0<=255);lia|].
  destruct (Int.eq (fr_kind r) Int.zero) eqn:KIND.
  - specialize (EXIT (Int.same_if_eq _ _ KIND));pose proof (Int.unsigned_range (fr_detail r)).
    rewrite <- (Int.repr_unsigned (fr_detail r)),Int.signed_repr;
      [lia|change Int.min_signed with (-2147483648);change Int.max_signed with 2147483647;lia].
  - destruct (Int.eq (fr_kind r) (Int.repr 2)) eqn:SIG.
    + specialize (SIGNAL (Int.same_if_eq _ _ SIG));unfold Int.add.
      rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295;lia).
      rewrite Int.signed_repr;[lia|change Int.min_signed with (-2147483648);change Int.max_signed with 2147483647;lia].
    + destruct (Int.eq (fr_kind r) Int.one), (Int.eq (fr_kind r) (Int.repr 3));vm_compute;repeat split;discriminate.
Qed.
Theorem finish_returned_exit_status : forall cell base input ofs r digest mode mode_bytes locations events value after,
  sender_input cell base input ofs r digest mode mode_bytes locations -> finish_valid_detail r ->
  library_steps result_ge cell (live (finish_initial input ofs Kstop base)) events (live (Returnstate value Kstop after)) ->
  value=Vint (finish_exit_word r) /\ 0<=Int.signed (finish_exit_word r)<=255.
Proof.
  intros;split;[exact (proj1 (finish_all_returns _ _ _ _ _ _ _ _ _ _ _ _ H H1))|apply finish_exit_word_bounds;exact H0].
Qed.
