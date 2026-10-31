(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-receiver.memory: Actual terminal result copies retain all fields and arbitrary padding. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata Ctypes Clight.
Require Import ResultLayout ResultSafety WriteBytes.
Import ListNotations.
Open Scope Z_scope.

Theorem receiver_result_copy : forall before src dst ofs kind stage detail entry uid run,
  result_contents before src 0 kind stage detail entry uid run ->
  Mem.range_perm before src 0 144 Cur Readable -> result_destination before dst ofs -> src<>dst ->
  exists after values,
    Mem.loadbytes before src 0 144=Some values /\
    Mem.storebytes before dst ofs values=Some after /\
    assign_loc result_ge result_type before dst(Ptrofs.repr ofs)Full(Vptr src Ptrofs.zero)after /\
    result_contents after dst ofs kind stage detail entry uid run /\
    Mem.unchanged_on(outside_bytes dst ofs 144)before after.
Proof.
  intros before src dst ofs kind stage detail entry uid run CONTENT READ [LOW[HIGH[ALIGN WRITE]]] NE.
  destruct(Mem.range_perm_loadbytes before src 0 144 READ)as[values LOAD].
  assert(LEN : Z.of_nat(length values)=144)by(rewrite(Mem.loadbytes_length _ _ _ _ _ LOAD);reflexivity).
  assert(WRITE' : Mem.range_perm before dst ofs(ofs+Z.of_nat(length values))Cur Writable)by(rewrite LEN;exact WRITE).
  destruct(Mem.range_perm_storebytes _ _ _ _ WRITE')as[after STORE].
  assert(REP : Ptrofs.unsigned(Ptrofs.repr ofs)=ofs)by(apply Ptrofs.unsigned_repr;unfold Ptrofs.max_unsigned;lia).
  exists after,values;split;[exact LOAD|]. split;[exact STORE|]. split.
  - eapply assign_loc_copy with(bytes:=values).
    + reflexivity.
    + intros;exists 0;reflexivity.
    + intros;rewrite REP;exact ALIGN.
    + left;exact NE.
    + exact LOAD.
    + rewrite REP;exact STORE.
  - split;[eapply result_struct_copy_fields;eassumption|].
    eapply Mem.storebytes_unchanged_on;[exact STORE|].
    intros pos RANGE;rewrite LEN in RANGE;unfold outside_bytes;lia.
Qed.
