(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Publish exact bytes, length, kind and retained owner into real C fields. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Errors
  Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayPython GatewayAllocation GatewayPrefix
  GatewayFieldGuard GatewayFieldRoot.
Import ListNotations.
Open Scope Z_scope.

Definition field_pointer_type:=tptr(Tstruct _host_field noattr).
Definition field_member(member:ident)(ty:type):expr:=
  Efield(Ederef(Etempvar _field field_pointer_type)(Tstruct _host_field noattr))member ty.

Definition field_member_layout(ge:Clight.genv)member delta:Prop:=
  exists composite,(genv_cenv ge)!_host_field=Some composite /\
    field_offset ge member(co_members composite)=OK(delta,Full).

Lemma actual_field_member_location ge environment temporaries memory object offset member ty delta :
  temporaries!_field=Some(Vptr object offset) ->field_member_layout ge member delta ->
  location_value ge environment temporaries memory(field_member member ty)object
    (Ptrofs.add offset(Ptrofs.repr delta)).
Proof.
  intros TARGET[composite[LAYOUT MEMBER]].
  eapply struct_location_value with(id:=_host_field)(co:=composite)(att:=noattr)(delta:=delta).
  - eapply location_read_value with(b:=object)(ofs:=offset).
    + apply pointer_location_value;apply old_expression_value;apply value_temp;exact TARGET.
    + apply deref_loc_copy;reflexivity.
  - reflexivity.
  - exact LAYOUT.
  - exact MEMBER.
Qed.

Lemma actual_field_assignment ge function environment temporaries before object offset
    member ty delta chunk expression value converted after continuation :
  temporaries!_field=Some(Vptr object offset) ->field_member_layout ge member delta ->
  access_mode ty=By_value chunk ->
  expression_value ge environment temporaries before expression value ->
  sem_cast value(typeof expression)ty before=Some converted ->
  Mem.storev chunk before(Vptr object(Ptrofs.add offset(Ptrofs.repr delta)))converted=Some after ->
  store_edge ge
    (State function(Sassign(field_member member ty)expression)continuation environment temporaries before)
    (State function Sskip continuation environment temporaries after).
Proof.
  intros TARGET LAYOUT ACCESS VALUE CAST STORE.
  eapply assignment_source_edge with(b:=object)(ofs:=Ptrofs.add offset(Ptrofs.repr delta))
    (v:=value)(w:=converted).
  - apply actual_field_member_location;[exact TARGET|exact LAYOUT].
  - exact VALUE.
  - exact CAST.
  - eapply assign_loc_value;[exact ACCESS|exact STORE].
Qed.

Definition field_wire_cells memory object offset kind size pointer owner :Prop:=
  Mem.loadv Mint32 memory(Vptr object(Ptrofs.add offset(Ptrofs.repr 0)))=Some(Vint kind) /\
  Mem.loadv Mint64 memory(Vptr object(Ptrofs.add offset(Ptrofs.repr 8)))=Some(Vlong size) /\
  Mem.loadv Mptr memory(Vptr object(Ptrofs.add offset(Ptrofs.repr 16)))=Some pointer /\
  Mem.loadv Mptr memory(Vptr object(Ptrofs.add offset(Ptrofs.repr 24)))=Some owner.

Definition field_store_sequence before object offset kind size pointer owner after :Prop:=
  exists first second third,
    Mem.storev Mint32 before(Vptr object(Ptrofs.add offset(Ptrofs.repr 0)))(Vint kind)=Some first /\
    Mem.storev Mint64 first(Vptr object(Ptrofs.add offset(Ptrofs.repr 8)))(Vlong size)=Some second /\
    Mem.storev Mptr second(Vptr object(Ptrofs.add offset(Ptrofs.repr 16)))pointer=Some third /\
    Mem.storev Mptr third(Vptr object(Ptrofs.add offset(Ptrofs.repr 24)))owner=Some after.

Lemma field_store_read_other chunk before object offset value after other read_chunk position :
  Mem.storev chunk before(Vptr object offset)value=Some after ->other<>object ->
  Mem.load read_chunk after other position=Mem.load read_chunk before other position.
Proof.
  unfold Mem.storev;destruct(zle(Ptrofs.unsigned offset+size_chunk chunk)Ptrofs.modulus);
    [|discriminate].
  intros STORE OTHER;eapply Mem.load_store_other;[exact STORE|auto].
Qed.

Lemma field_slot_no_wrap offset delta :
  0<=delta<40 ->Ptrofs.unsigned offset+40<=Ptrofs.modulus ->
  Ptrofs.unsigned(Ptrofs.add offset(Ptrofs.repr delta))=Ptrofs.unsigned offset+delta.
Proof.
  intros DELTA BOUND.
  pose proof(Ptrofs.unsigned_range offset)as RANGE.
  rewrite Ptrofs.add_unsigned.
  rewrite(Ptrofs.unsigned_repr delta)by(unfold Ptrofs.max_unsigned;lia).
  apply Ptrofs.unsigned_repr;unfold Ptrofs.max_unsigned;lia.
Qed.

Ltac field_arithmetic :=
  try(change(size_chunk Mptr)with 8);
  try(change Ptrofs.modulus with 18446744073709551616);
  cbn;lia.

Theorem actual_field_store_contents before object offset kind size pointer owner after :
  Ptrofs.unsigned offset+40<=Ptrofs.modulus ->
  (exists block position,pointer=Vptr block position) ->
  (exists block position,owner=Vptr block position) ->
  field_store_sequence before object offset kind size pointer owner after ->
  field_wire_cells after object offset kind size pointer owner.
Proof.
  intros BOUND[buffer[buffer_offset POINTER]][held[held_offset OWNER]]
    [first[second[third[KIND[SIZE[DATA ROOT]]]]]].
  subst pointer owner.
  pose proof BOUND as RAWBOUND.
  change Ptrofs.modulus with 18446744073709551616 in BOUND.
  cbn in BOUND.
  unfold Mem.storev in KIND,SIZE,DATA,ROOT.
  rewrite !field_slot_no_wrap in KIND,SIZE,DATA,ROOT by lia.
  rewrite zle_true in KIND,SIZE,DATA,ROOT by field_arithmetic.
  unfold field_wire_cells,Mem.loadv.
  rewrite !field_slot_no_wrap by lia.
  repeat rewrite zle_true by field_arithmetic.
  split.
  - rewrite(Mem.load_store_other _ _ _ _ _ _ ROOT)by(right;left;field_arithmetic).
    rewrite(Mem.load_store_other _ _ _ _ _ _ DATA)by(right;left;field_arithmetic).
    rewrite(Mem.load_store_other _ _ _ _ _ _ SIZE)by(right;left;field_arithmetic).
    exact(Mem.load_store_same _ _ _ _ _ _ KIND).
  - split.
    + rewrite(Mem.load_store_other _ _ _ _ _ _ ROOT)by(right;left;field_arithmetic).
      rewrite(Mem.load_store_other _ _ _ _ _ _ DATA)by(right;left;field_arithmetic).
      exact(Mem.load_store_same _ _ _ _ _ _ SIZE).
    + split.
      * rewrite(Mem.load_store_other _ _ _ _ _ _ ROOT)by(right;left;field_arithmetic).
        exact(Mem.load_store_same _ _ _ _ _ _ DATA).
      * exact(Mem.load_store_same _ _ _ _ _ _ ROOT).
Qed.
