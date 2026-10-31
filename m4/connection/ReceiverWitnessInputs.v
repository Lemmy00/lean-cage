(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-receiver.input: Allocated caller, globals and TLS witnesses without a Linux initialization claim. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata Globalenvs Clight.
Require Import Slice IO Machine ProcessEffects FreshMemory ResultLayout ResultSource ResultSafety ResultWitnesses
  ReceiverInput.
Open Scope Z_scope.
Theorem receiver_inputs_inhabited : forall run uid,
  exists cell base output,receiver_input cell base output 0 run uid.
Proof.
  intros run uid;destruct(arbitrary_result_source_input run uid)as[m[output[DEST[rb[ub[RS[US[RUN UID]]]]]]]].
  destruct(Mem.alloc m 0 4)as[base local]eqn:ALLOC.
  assert(FRESH : ~Mem.valid_block m local)by(eapply Mem.fresh_block_alloc;exact ALLOC).
  set(cell:={|tls_block:=local;tls_offset:=0|}).
  assert(TLS : tls_ready cell base).
  { unfold tls_ready,cell;cbn;split;[lia|]. split;[change(4<=18446744073709551616);lia|].
    split;[|exists 0;reflexivity]. intros pos RANGE;eapply Mem.perm_implies;
      [eapply Mem.perm_alloc_2;[exact ALLOC|exact RANGE]|constructor]. }
  exists cell,base,output;split.
  - destruct DEST as[LOW[HIGH[ALIGN PERMS]]];split;[exact LOW|]. split;[exact HIGH|].
    split;[exact ALIGN|]. intros pos RANGE;eapply Mem.perm_alloc_1;[exact ALLOC|apply PERMS;exact RANGE].
  - split;[exact TLS|]. exists rb,ub;split;[exact RS|]. split;[exact US|]. split.
    + split;eapply Mem.load_alloc_other;eassumption.
    + split;intro EQ;unfold cell in EQ;cbn in EQ;subst;
        apply FRESH;eapply Mem.perm_valid_block with(ofs:=0);
        [apply(proj1(Mem.load_valid_access _ _ _ _ _ RUN))|apply(proj1(Mem.load_valid_access _ _ _ _ _ UID))];cbn;lia.
Qed.
