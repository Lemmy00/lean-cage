(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual UInt64 loop index advances without wrapping after
   its strict guard and reaches exactly the validated machine-width container count. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers.
Open Scope Z_scope.

Lemma gateway_array_index_increment index size:
  Int64.ltu index size=true->Int64.unsigned(Int64.add index Int64.one)=Int64.unsigned index+1 /\
    Int64.unsigned(Int64.add index Int64.one)<=Int64.unsigned size.
Proof.
  intro LESS;pose proof(Int64.ltu_inv _ _ LESS)as RANGE;pose proof(Int64.unsigned_range size)as SIZE.
  rewrite Int64.add_unsigned;change(Int64.unsigned(Int64.repr(Int64.unsigned index+1))=Int64.unsigned index+1 /\
    Int64.unsigned(Int64.repr(Int64.unsigned index+1))<=Int64.unsigned size).
  rewrite Int64.unsigned_repr;[split;[reflexivity|lia]|unfold Int64.max_unsigned;lia].
Qed.

Lemma gateway_array_index_exhausted index size:
  Int64.unsigned index<=Int64.unsigned size->Int64.ltu index size=false->index=size.
Proof.
  intros BOUND;unfold Int64.ltu;destruct(zlt(Int64.unsigned index)(Int64.unsigned size));[discriminate|].
  intro ZERO;rewrite<-(Int64.repr_unsigned index),<-(Int64.repr_unsigned size);f_equal;lia.
Qed.
