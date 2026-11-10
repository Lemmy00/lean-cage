(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: An Outcome data-cell store cannot overwrite a live bytes payload. *)
From Stdlib Require Import ZArith Lia List.
From compcert Require Import Integers AST Values Memory Memdata Clight.
From HostGateway Require Import GatewayPython GatewayObjects.
Open Scope Z_scope.

Definition gateway_outcome_cell_separate python object :Prop:=
  forall value bytes,python_values python value=Some(python_byte_value bytes) ->
    (0<python_strong python value)%nat ->python_bytes_block bytes<>object.

Lemma gateway_store_weak_valid before after chunk object offset value candidate position :
  Mem.store chunk before object offset value=Some after ->
  Mem.weak_valid_pointer before candidate position=true ->Mem.weak_valid_pointer after candidate position=true.
Proof.
  intros STORE POINTER;unfold Mem.weak_valid_pointer,Mem.valid_pointer in *.
  repeat match goal with |-context[Mem.perm_dec after ?b ?ofs ?kind ?permission]=>
    destruct(Mem.perm_dec after b ofs kind permission)end;
    repeat match goal with H:context[Mem.perm_dec before ?b ?ofs ?kind ?permission]|-_=>
      destruct(Mem.perm_dec before b ofs kind permission)end;
    cbn in *;try discriminate;try reflexivity;
    exfalso;match goal with PERM:Mem.perm before _ _ _ _,DENIED:~Mem.perm after _ _ _ _|-_=>
      apply DENIED;eapply Mem.perm_store_1;[exact STORE|exact PERM]end.
Qed.

Lemma gateway_store_preserves_bytes before after chunk object offset value bytes :
  Mem.store chunk before object offset value=Some after ->
  python_bytes_block bytes<>object ->python_bytes_loaded before bytes ->python_bytes_loaded after bytes.
Proof.
  intros STORE SEPARATE[LOW[BOUND[PERMISSIONS CONTENTS]]].
  split;[exact LOW|]. split;[exact BOUND|]. split.
  - intros position RANGE;eapply Mem.perm_store_1;[exact STORE|apply PERMISSIONS;exact RANGE].
  - rewrite(Mem.loadbytes_store_other _ _ _ _ _ _ STORE)by(left;exact SEPARATE).
    exact CONTENTS.
Qed.

Theorem gateway_outcome_store_python_valid python before after object offset value :
  python_world_valid python before ->gateway_outcome_cell_separate python object ->
  Mem.store Mptr before object offset value=Some after ->python_world_valid python after.
Proof.
  intros[COUNTS[BYTES[BLOCKS OBJECTS]]]SEPARATE STORE.
  split;[exact COUNTS|]. split.
  - intros result bytes DESCRIPTION STRONG;eapply gateway_store_preserves_bytes;
      [exact STORE|exact(SEPARATE result bytes DESCRIPTION STRONG)|exact(BYTES result bytes DESCRIPTION STRONG)].
  - split;[|exact OBJECTS]. intros block OWNED;eapply Mem.store_valid_block_1;
      [exact STORE|apply BLOCKS;exact OWNED].
Qed.

Theorem gateway_outcome_store_objects_ready python heap before after object offset value :
  gateway_objects_ready python heap before ->gateway_outcome_cell_separate python object ->
  Mem.store Mptr before object offset value=Some after ->gateway_objects_ready python heap after.
Proof.
  intros[[WORLD[ROOTS[BYTES[DICTIONARIES POINTERS]]]][GIL CLEAR]]SEPARATE STORE.
  split;[|split;assumption]. split.
  - eapply gateway_outcome_store_python_valid;eassumption.
  - split;[exact ROOTS|]. split;[exact BYTES|]. split;[exact DICTIONARIES|].
    intros result ROOT;destruct(POINTERS result ROOT)as(block &ofs &RESULT &POINTER).
    exists block,ofs;split;[exact RESULT|].
    eapply gateway_store_weak_valid;eassumption.
Qed.
