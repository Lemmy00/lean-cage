(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The source initializes eight typed cells in its real stream allocation. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers Floats AST Values Memory Memdata.
From HostGateway Require Import GatewayStreamInterface GatewayStreamMemory.
Import ListNotations.
Open Scope Z_scope.

Record gateway_stream_initial_cell:Type:={
  stream_initial_offset:Z;
  stream_initial_chunk:memory_chunk;
  stream_initial_value:val
}.
Definition stream_initial_cells stream:list gateway_stream_initial_cell:=
  [{|stream_initial_offset:=0;stream_initial_chunk:=Mint32;stream_initial_value:=Vint(stream_descriptor stream)|};
   {|stream_initial_offset:=4;stream_initial_chunk:=Mint32;stream_initial_value:=Vint(stream_control stream)|};
   {|stream_initial_offset:=8;stream_initial_chunk:=Mint32;stream_initial_value:=Vint(stream_cancel_sent stream)|};
   {|stream_initial_offset:=12;stream_initial_chunk:=Mint32;stream_initial_value:=Vint(stream_cli stream)|};
   {|stream_initial_offset:=16;stream_initial_chunk:=Mptr;stream_initial_value:=stream_cancellation stream|};
   {|stream_initial_offset:=24;stream_initial_chunk:=Mint64;stream_initial_value:=Vlong(stream_remaining stream)|};
   {|stream_initial_offset:=32;stream_initial_chunk:=Mint64;stream_initial_value:=Vlong(stream_nodes stream)|};
   {|stream_initial_offset:=40;stream_initial_chunk:=Mfloat64;stream_initial_value:=Vfloat(stream_deadline stream)|}].
Definition stream_initial_cell stream index:=nth index(stream_initial_cells stream)
  {|stream_initial_offset:=0;stream_initial_chunk:=Mint32;stream_initial_value:=Vundef|}.
Definition gateway_stream_prefix memory object stream count:Prop:=forall index,(index<count)%nat->
  Mem.load(stream_initial_chunk(stream_initial_cell stream index))memory object(stream_initial_offset(stream_initial_cell stream index))=
    Some(stream_initial_value(stream_initial_cell stream index)).

Lemma stream_initial_cell_bounds stream index:
  (index<8)%nat->0<=stream_initial_offset(stream_initial_cell stream index) /\
  stream_initial_offset(stream_initial_cell stream index)+size_chunk(stream_initial_chunk(stream_initial_cell stream index))<=48 /\
  (align_chunk(stream_initial_chunk(stream_initial_cell stream index))|stream_initial_offset(stream_initial_cell stream index)).
Proof.
  intro BOUND;destruct index as[|[|[|[|[|[|[|[|index]]]]]]]];try lia.
  all:cbn[stream_initial_cell stream_initial_cells nth stream_initial_offset stream_initial_chunk size_chunk align_chunk
    Mptr Archi.ptr64 Archi.align_int64 Archi.align_float64];repeat split;try lia.
  all:cbv[Archi.align_int64 Archi.align_float64];apply Z.mod_divide;[lia|reflexivity].
Qed.

Lemma stream_initial_cells_apart stream first second:
  (first<second)%nat->(second<8)%nat->
  stream_initial_offset(stream_initial_cell stream first)+size_chunk(stream_initial_chunk(stream_initial_cell stream first))<=
    stream_initial_offset(stream_initial_cell stream second).
Proof.
  intros ORDER BOUND.
  assert(POINTER:size_chunk Mptr=8)by reflexivity.
  do 8(destruct first as[|first];[do 8(destruct second as[|second];[cbn in *;rewrite ?POINTER in *;lia|]);lia|]);lia.
Qed.

Lemma gateway_stream_prefix_store before after object stream index:
  (index<8)%nat->gateway_stream_prefix before object stream index->
  (exists object offset,stream_cancellation stream=Vptr object offset) \/
    (exists value,stream_cancellation stream=Vlong value)->
  Mem.store(stream_initial_chunk(stream_initial_cell stream index))before object
    (stream_initial_offset(stream_initial_cell stream index))(stream_initial_value(stream_initial_cell stream index))=Some after->
  gateway_stream_prefix after object stream(S index).
Proof.
  intros BOUND PREFIX POINTER STORE previous PREVIOUS.
  destruct(Nat.eq_dec previous index)as[SAME|EARLIER].
  - subst previous;rewrite(Mem.load_store_same _ _ _ _ _ _ STORE).
    destruct index as[|[|[|[|[|[|[|[|index]]]]]]]];try lia.
    all:cbn[stream_initial_cell stream_initial_cells nth stream_initial_value stream_initial_chunk];try reflexivity.
    destruct POINTER as[[held[offset POINTER]]|[value POINTER]];rewrite POINTER;reflexivity.
  - assert(ORDER:(previous<index)%nat)by lia.
    rewrite(Mem.load_store_other _ _ _ _ _ _ STORE).
    + apply PREFIX;exact ORDER.
    + right;left;exact(stream_initial_cells_apart stream previous index ORDER BOUND).
Qed.

Theorem gateway_stream_prefix_complete memory object stream:
  gateway_stream_prefix memory object stream 8->gateway_stream_memory memory object Ptrofs.zero stream.
Proof.
  intro PREFIX;unfold gateway_stream_memory,gateway_stream_slot,Mem.loadv.
  repeat split;rewrite Ptrofs.add_zero_l;cbn.
  all:first[exact(PREFIX 0%nat ltac:(lia))|exact(PREFIX 1%nat ltac:(lia))|exact(PREFIX 2%nat ltac:(lia))|
    exact(PREFIX 3%nat ltac:(lia))|exact(PREFIX 4%nat ltac:(lia))|exact(PREFIX 5%nat ltac:(lia))|
    exact(PREFIX 6%nat ltac:(lia))|exact(PREFIX 7%nat ltac:(lia))].
Qed.

Lemma gateway_stream_prefix_unchanged before after object stream count:
  (count<=8)%nat->gateway_stream_prefix before object stream count->
  Mem.unchanged_on(gateway_stream_region object Ptrofs.zero)before after->gateway_stream_prefix after object stream count.
Proof.
  intros COUNT PREFIX FRAME index INDEX;destruct(stream_initial_cell_bounds stream index ltac:(lia))as[LOW[HIGH ALIGN]].
  eapply Mem.load_unchanged_on;[exact FRAME| |apply PREFIX;exact INDEX].
  intros position RANGE;split;[reflexivity|];change(0<=position<48);lia.
Qed.

Lemma gateway_stream_initial_store before object stream index:
  (index<8)%nat->Mem.range_perm before object 0 48 Cur Writable->
  exists after,Mem.store(stream_initial_chunk(stream_initial_cell stream index))before object
    (stream_initial_offset(stream_initial_cell stream index))(stream_initial_value(stream_initial_cell stream index))=Some after.
Proof.
  intros BOUND WRITABLE.
  assert(ACCESS:Mem.valid_access before(stream_initial_chunk(stream_initial_cell stream index))object
    (stream_initial_offset(stream_initial_cell stream index))Writable).
  { destruct(stream_initial_cell_bounds stream index BOUND)as[LOW[HIGH ALIGN]];split;[|exact ALIGN].
    intros position RANGE;apply WRITABLE;lia. }
  destruct(Mem.valid_access_store before(stream_initial_chunk(stream_initial_cell stream index))object
    (stream_initial_offset(stream_initial_cell stream index))(stream_initial_value(stream_initial_cell stream index))ACCESS)
    as[after STORE];exists after;exact STORE.
Qed.
