(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Native word receipts retain actual bytes and the shared codec. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata Events Clight.
From LeanImport Require Import Lean.
Require Import Writers Readers WriteBytes WriteMemory.
From HostGateway Require Import GatewaySource GatewayImport GatewayMachine GatewayFrames
  GatewayWordsMemory GatewayWordsMath GatewayWordData GatewayWords GatewayReads.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Definition gateway_native_bytes (values:list int) : list Byte.int :=
  map(fun value=>Byte.repr(Int.unsigned value))values.
Definition gateway_byte_naturals (bytes:list Byte.int) : list nat :=
  map(fun byte=>Z.to_nat(Byte.unsigned byte))bytes.

Lemma gateway_native_memvals values : map Byte(gateway_native_bytes values)=map byte_encoding values.
Proof. unfold gateway_native_bytes,byte_encoding;rewrite map_map;reflexivity. Qed.

Lemma gateway_native_naturals values :
  Forall(fun value=>0<=Int.unsigned value<256)values ->
  gateway_byte_naturals(gateway_native_bytes values)=gateway_int_bytes values.
Proof.
  intro BOUNDS;induction BOUNDS;[reflexivity|].
  cbn[gateway_byte_naturals gateway_native_bytes gateway_int_bytes map].
  rewrite Byte.unsigned_repr by(change Byte.max_unsigned with 255;lia).
  f_equal;exact IHBOUNDS.
Qed.

Definition gateway_words32_bounded value :=
  Forall(fun byte=>0<=Int.unsigned byte<256)(put32_values value).
Definition gateway_words64_bounded value :=
  Forall(fun byte=>0<=Int.unsigned byte<256)(put64_values value).

Lemma gateway_words32_bound value : gateway_words32_bounded value.
Proof. apply Forall_forall;intros byte MEMBER;unfold put32_values in MEMBER;
  apply in_map_iff in MEMBER;destruct MEMBER as[index[SAME _]];subst;apply gateway_put32_byte_range. Qed.
Lemma gateway_words64_bound value : gateway_words64_bounded value.
Proof. apply Forall_forall;intros byte MEMBER;unfold put64_values in MEMBER;
  apply in_map_iff in MEMBER;destruct MEMBER as[index[SAME _]];subst;apply gateway_put64_byte_range. Qed.

(* The constructor packages, rather than assumes, the source-produced shared codec proposition. *)
Inductive gateway_encoded_memory memory block offset width value : Prop :=
| gateway_encoded_memory_intro : forall bytes,
    Mem.loadbytes memory block offset(Z.of_nat width)=Some(map Byte bytes) ->
    LeanCage_Host_GatewayWords_Encoding(Nat_of_nat width)(Nat_of_nat value)
      (gateway_imported_nats(gateway_byte_naturals bytes)) ->
    gateway_encoded_memory memory block offset width value.

Theorem gateway_put32_shared {World Event}(backend:gateway_backend World Event)ge active
    block ofs value before world events returned after final_world :
  gateway_private_contract backend(gateway_byte_region block(Ptrofs.unsigned ofs)4)active ->
  active world -> Ptrofs.unsigned ofs+4<=Ptrofs.modulus ->
  Mem.range_perm before block(Ptrofs.unsigned ofs)(Ptrofs.unsigned ofs+4)Cur Writable ->
  gateway_steps backend ge
    (gateway_live(writer_initial f_host_put32 block ofs(Vint value)Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)final_world) ->
  returned=Vundef /\ gateway_encoded_memory after block(Ptrofs.unsigned ofs)4
    (Z.to_nat(Int.unsigned value)) /\ active final_world.
Proof.
  intros LAW ACTIVE BOUND OWN RUN.
  destruct(gateway_put32_actual backend ge active block ofs value before world events returned after final_world
    LAW ACTIVE BOUND OWN RUN)as[VALUE[BYTES NEXT]].
  split;[exact VALUE|];split;[|exact NEXT].
  eapply gateway_encoded_memory_intro with(bytes:=gateway_native_bytes(put32_values value)).
  - rewrite gateway_native_memvals;exact BYTES.
  - rewrite gateway_native_naturals by apply gateway_words32_bound;apply gateway_put32_encoding.
Qed.

Theorem gateway_put64_shared {World Event}(backend:gateway_backend World Event)ge active
    block ofs value before world events returned after final_world :
  gateway_private_contract backend(gateway_byte_region block(Ptrofs.unsigned ofs)8)active ->
  active world -> Ptrofs.unsigned ofs+8<=Ptrofs.modulus ->
  Mem.range_perm before block(Ptrofs.unsigned ofs)(Ptrofs.unsigned ofs+8)Cur Writable ->
  gateway_steps backend ge
    (gateway_live(writer_initial f_host_put64 block ofs(Vlong value)Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)final_world) ->
  returned=Vundef /\ gateway_encoded_memory after block(Ptrofs.unsigned ofs)8
    (Z.to_nat(Int64.unsigned value)) /\ active final_world.
Proof.
  intros LAW ACTIVE BOUND OWN RUN.
  destruct(gateway_put64_actual backend ge active block ofs value before world events returned after final_world
    LAW ACTIVE BOUND OWN RUN)as[VALUE[BYTES NEXT]].
  split;[exact VALUE|];split;[|exact NEXT].
  eapply gateway_encoded_memory_intro with(bytes:=gateway_native_bytes(put64_values value)).
  - rewrite gateway_native_memvals;exact BYTES.
  - rewrite gateway_native_naturals by apply gateway_words64_bound;apply gateway_put64_encoding.
Qed.

Lemma gateway_ready_actual_bytes block ofs values memory :
  Ptrofs.unsigned ofs+Z.of_nat(length values)<=Ptrofs.modulus ->
  gateway_read_ready block ofs values memory ->
  Mem.loadbytes memory block(Ptrofs.unsigned ofs)(Z.of_nat(length values))=
    Some(map Byte(gateway_native_bytes values)).
Proof.
  intros BOUND READY;rewrite gateway_native_memvals;apply gateway_loadbytes_from_loads.
  intros index value SELECTED;specialize(READY index value SELECTED).
  assert(INDEX:(index<length values)%nat)by(apply nth_error_Some;rewrite SELECTED;discriminate).
  unfold Mem.loadv in READY;destruct(zle _ _);[|discriminate].
  rewrite(gateway_pointer_index ofs(length values)index BOUND INDEX)in READY;exact READY.
Qed.

Theorem gateway_get64_shared {World Event}(backend:gateway_backend World Event)ge active
    block ofs values before world events returned after final_world :
  gateway_private_contract backend(gateway_byte_region block(Ptrofs.unsigned ofs)(length values))active ->
  active world -> (length values<=8)%nat ->
  Ptrofs.unsigned ofs+Z.of_nat(length values)<=Ptrofs.modulus -> gateway_read_ready block ofs values before ->
  gateway_steps backend ge(gateway_live(gateway_get_initial block ofs(length values)Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)final_world) ->
  exists bytes,
    Mem.loadbytes before block(Ptrofs.unsigned ofs)(Z.of_nat(length values))=Some(map Byte bytes) /\
    Mem.loadbytes after block(Ptrofs.unsigned ofs)(Z.of_nat(length values))=Some(map Byte bytes) /\
    returned=Vlong(Int64.repr(Z.of_nat(nat_of_Nat(LeanCage_Host_GatewayWords_decode
      (gateway_imported_nats(gateway_byte_naturals bytes)))))) /\ active final_world.
Proof.
  intros LAW ACTIVE WIDTH BOUND READY RUN.
  destruct(gateway_get64_actual backend ge active block ofs values before world events returned after final_world
    LAW ACTIVE WIDTH BOUND READY RUN)as[VALUE[POST NEXT]].
  exists(gateway_native_bytes values);repeat split.
  - apply gateway_ready_actual_bytes;assumption.
  - apply gateway_ready_actual_bytes;assumption.
  - rewrite gateway_native_naturals by(eapply gateway_read_ready_bounds;exact READY).
    rewrite gateway_shared_decode;exact VALUE.
  - exact NEXT.
Qed.

(* §FS-host-boundary.caller: Independent writable storage produces a full real source execution. *)
Theorem gateway_put64_useful {World Event}(backend:gateway_backend World Event)ge block ofs value before world :
  Ptrofs.unsigned ofs+8<=Ptrofs.modulus ->
  Mem.range_perm before block(Ptrofs.unsigned ofs)(Ptrofs.unsigned ofs+8)Cur Writable ->
  exists events after,
    gateway_steps backend ge
      (gateway_live(writer_initial f_host_put64 block ofs(Vlong value)Kstop before)world)events
      (gateway_live(Returnstate Vundef Kstop after)world) /\
    gateway_encoded_memory after block(Ptrofs.unsigned ofs)8(Z.to_nat(Int64.unsigned value)).
Proof.
  intros BOUND OWN.
  destruct(gateway_framed_execution backend ge _ _ _ _ _
    (gateway_put64_framed ge block ofs value before BOUND)before world
    (gateway_bytes_initial block(Ptrofs.unsigned ofs)8 before OWN))as[events[after[RUN BYTES]]].
  exists events,after;split;[exact RUN|].
  eapply gateway_encoded_memory_intro with(bytes:=gateway_native_bytes(put64_values value)).
  - rewrite gateway_native_memvals;exact BYTES.
  - rewrite gateway_native_naturals by apply gateway_words64_bound;apply gateway_put64_encoding.
Qed.

Lemma gateway_read_ready_from_bytes memory block ofs bytes :
  Ptrofs.unsigned ofs+Z.of_nat(length bytes)<=Ptrofs.modulus ->
  Mem.loadbytes memory block(Ptrofs.unsigned ofs)(Z.of_nat(length bytes))=Some(map Byte bytes) ->
  gateway_read_ready block ofs(map byte_word bytes)memory.
Proof.
  intros BOUND FULL index value SELECTED.
  rewrite nth_error_map in SELECTED.
  destruct(nth_error bytes index)as[byte|]eqn:BYTE;[|discriminate].
  inversion SELECTED;subst value.
  assert(INDEX:(index<length bytes)%nat)by(apply nth_error_Some;rewrite BYTE;discriminate).
  apply nth_error_split in BYTE;destruct BYTE as[earlier[later[SAME LENGTH]]].
  rewrite SAME in FULL.
  pose proof(load_suffix memory block(Ptrofs.unsigned ofs)earlier(byte::later)FULL)as SUFFIX.
  pose proof(load_first memory block(Ptrofs.unsigned ofs+Z.of_nat(length earlier))[byte]later SUFFIX)as SINGLE.
  assert(LOAD:Mem.load Mint8unsigned memory block(Ptrofs.unsigned ofs+Z.of_nat index)=Some(Vint(byte_word byte))).
  { rewrite<-decode_byte;eapply Mem.loadbytes_load;[rewrite<-LENGTH;exact SINGLE|apply Z.divide_1_l]. }
  unfold Mem.loadv.
  rewrite(gateway_pointer_index ofs(length bytes)index BOUND INDEX).
  destruct(zle _ _);[exact LOAD|cbn[size_chunk]in *;lia].
Qed.

(* §FS-host-boundary.caller: Freshly allocated writable storage inhabits the actual uint64 writer. *)
Theorem gateway_put64_allocated {World Event}(backend:gateway_backend World Event)ge base value world :
  exists allocated block events after,
    Mem.alloc base 0 8=(allocated,block) /\
    gateway_steps backend ge
      (gateway_live(writer_initial f_host_put64 block Ptrofs.zero(Vlong value)Kstop allocated)world)events
      (gateway_live(Returnstate Vundef Kstop after)world) /\
    gateway_encoded_memory after block 0 8(Z.to_nat(Int64.unsigned value)).
Proof.
  destruct(Mem.alloc base 0 8)as[allocated block]eqn:ALLOC.
  assert(OWN:Mem.range_perm allocated block 0 8 Cur Writable).
  { intros position RANGE;eapply Mem.perm_implies;[eapply Mem.perm_alloc_2;eauto|constructor]. }
  destruct(gateway_put64_useful backend ge block Ptrofs.zero value allocated world
    ltac:(change(0+8<=18446744073709551616);lia)OWN)as[events[after[RUN ENCODED]]].
  exists allocated,block,events,after;auto.
Qed.
