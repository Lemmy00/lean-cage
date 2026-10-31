(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.encoding: Segment algebra preserves the unconstrained digest bytes. *)
From Coq Require Import Arith List Lia.
From compcert Require Import Integers.
Require Import BytePatch.
Import ListNotations.
Lemma patch_bytes_segment : forall prefix old replacement suffix,
  length old=length replacement ->
  patch_bytes (prefix++old++suffix) (length prefix) replacement=prefix++replacement++suffix.
Proof.
  intros prefix old replacement suffix LEN;unfold patch_bytes.
  rewrite firstn_app,firstn_all,Nat.sub_diag;cbn [firstn];rewrite app_nil_r.
  rewrite skipn_app,skipn_all2 by lia;cbn [app].
  replace (length prefix+length replacement-length prefix)%nat with (length old) by lia.
  rewrite skipn_app,skipn_all,Nat.sub_diag;cbn [skipn app];reflexivity.
Qed.
Lemma patch_zero_tail : forall prefix replacement rest,
  patch_bytes (prefix++repeat Byte.zero (length replacement+rest)) (length prefix) replacement=
    prefix++replacement++repeat Byte.zero rest.
Proof.
  intros;rewrite repeat_app;apply patch_bytes_segment;apply repeat_length.
Qed.
