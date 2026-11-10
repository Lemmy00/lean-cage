(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Stream expressions use actual ABI fields and actual loaded cells. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Ctypesdefs Cop Clight.
Require Import LocalAccess StoreSteps CallAccess ClightSteps.
From HostGateway Require Import GatewaySource GatewayStreamInterface GatewayStreamLayout.

Definition stream_pointer_type:=tptr(Tstruct _host_stream noattr).
Definition stream_member(member:ident)(ty:type):expr:=
  Efield(Ederef(Etempvar _stream stream_pointer_type)(Tstruct _host_stream noattr))member ty.

Lemma actual_stream_member_location ge environment temporaries memory block offset member ty delta :
  temporaries!_stream=Some(Vptr block offset) ->stream_member_layout ge member delta ->
  location_value ge environment temporaries memory(stream_member member ty)block
    (Ptrofs.add offset(Ptrofs.repr delta)).
Proof.
  intros TARGET[composite[LAYOUT MEMBER]].
  eapply struct_location_value with(id:=_host_stream)(co:=composite)(att:=noattr)(delta:=delta).
  - eapply location_read_value with(b:=block)(ofs:=offset).
    + apply pointer_location_value;apply old_expression_value;apply ClightSteps.value_temp;exact TARGET.
    + apply deref_loc_copy;reflexivity.
  - reflexivity.
  - exact LAYOUT.
  - exact MEMBER.
Qed.

Lemma actual_stream_member_read ge environment temporaries memory block offset member ty delta chunk value :
  temporaries!_stream=Some(Vptr block offset) ->stream_member_layout ge member delta ->
  access_mode ty=By_value chunk ->
  Mem.loadv chunk memory(gateway_stream_slot block offset delta)=Some value ->
  expression_value ge environment temporaries memory(stream_member member ty)value.
Proof.
  intros TARGET LAYOUT ACCESS LOAD.
  eapply location_read_value;[eapply actual_stream_member_location;eassumption|].
  eapply deref_loc_value;[exact ACCESS|exact LOAD].
Qed.

Lemma actual_stream_member_store ge function environment temporaries before block offset member ty delta
    chunk expression value converted after continuation :
  temporaries!_stream=Some(Vptr block offset) ->stream_member_layout ge member delta ->
  access_mode ty=By_value chunk ->
  expression_value ge environment temporaries before expression value ->
  sem_cast value(typeof expression)ty before=Some converted ->
  Mem.storev chunk before(gateway_stream_slot block offset delta)converted=Some after ->
  store_edge ge
    (State function(Sassign(stream_member member ty)expression)continuation environment temporaries before)
    (State function Sskip continuation environment temporaries after).
Proof.
  intros TARGET LAYOUT ACCESS VALUE CAST STORE.
  eapply assignment_source_edge with(b:=block)(ofs:=Ptrofs.add offset(Ptrofs.repr delta))(v:=value)(w:=converted).
  - apply actual_stream_member_location;[exact TARGET|exact LAYOUT].
  - exact VALUE.
  - exact CAST.
  - eapply assign_loc_value;[exact ACCESS|exact STORE].
Qed.
