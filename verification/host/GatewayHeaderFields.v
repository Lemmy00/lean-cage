(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Descriptor words use the actual eight host_field entries. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Errors
  Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayHeaderInitialization GatewayHeaderMarshal
  GatewayHeaderExpression GatewayFieldStores GatewayHeaderPacket GatewayHeaderRuntime GatewayThreadRuntime.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Definition header_fields_sequence:=match header_source_after 114 with Ssequence first _=>first|_=>Sskip end.
Definition header_fields_after:=match header_source_after 114 with Ssequence _ rest=>rest|_=>Sskip end.
Definition header_fields_loop:=match header_fields_sequence with Ssequence _ rest=>rest|_=>Sskip end.
Definition header_fields_iteration:=match header_fields_loop with Sloop first _=>first|_=>Sskip end.
Definition header_fields_increment:=match header_fields_loop with Sloop _ second=>second|_=>Sskip end.
Definition header_fields_body:=match header_fields_iteration with Ssequence _ rest=>rest|_=>Sskip end.
Definition header_fields_kind:=match header_fields_body with Ssequence first _=>first|_=>Sskip end.
Definition header_fields_size:=match header_fields_body with Ssequence _ rest=>rest|_=>Sskip end.
Definition header_fields_kind_call:=match header_fields_kind with Ssequence _ rest=>rest|_=>Sskip end.
Definition header_fields_size_call:=match header_fields_size with Ssequence _ rest=>rest|_=>Sskip end.
Definition header_fields_kind_expr:=match header_fields_kind with Ssequence(Sset _ expression)_=>expression|_=>Econst_int Int.zero tint end.
Definition header_fields_size_expr:=match header_fields_size with Ssequence(Sset _ expression)_=>expression|_=>Econst_int Int.zero tint end.
Definition header_fields_pointer base:=Ebinop Oadd(header_pointer_expr base)
  (Ebinop Omul(Econst_int(Int.repr 12)tint)(Etempvar _index tuint)tuint)(tptr tuchar).
Definition header_fields_test:=Ebinop Olt(Etempvar _index tuint)(Econst_int(Int.repr 8)tint)tint.
Definition header_fields_cont:=Kloop1 header_fields_iteration header_fields_increment(Kseq header_fields_after Kstop).
Definition header_field_pointer:=Ebinop Oadd(Etempvar _fields(tptr(Tstruct _host_field noattr)))
  (Etempvar _index tuint)(tptr(Tstruct _host_field noattr)).
Definition header_field_expr member ty:=Efield(Ederef header_field_pointer(Tstruct _host_field noattr))member ty.

Theorem actual_header_fields_structure:
  header_source_after 114=Ssequence header_fields_sequence header_fields_after /\
  header_fields_sequence=Ssequence(Sset _index(Econst_int Int.zero tint))header_fields_loop /\
  header_fields_loop=Sloop header_fields_iteration header_fields_increment /\
  header_fields_iteration=Ssequence(Sifthenelse header_fields_test Sskip Sbreak)header_fields_body /\
  header_fields_body=Ssequence header_fields_kind header_fields_size /\
  header_fields_kind=Ssequence(Sset _t'72(header_field_expr _kind tuint))header_fields_kind_call /\
  header_fields_size=Ssequence(Sset _t'71(header_field_expr _size tulong))header_fields_size_call /\
  header_fields_increment=Sset _index(Ebinop Oadd(Etempvar _index tuint)(Econst_int Int.one tint)tuint) /\
  header_fields_kind_expr=header_field_expr _kind tuint /\header_fields_size_expr=header_field_expr _size tulong /\
  (forall value,header_fields_kind_call=header_expression_statement(gateway_packet32 value)
    (header_fields_pointer 16)(Etempvar _t'72 tuint)) /\
  (forall value,header_fields_size_call=header_expression_statement(gateway_packet64 value)
    (header_fields_pointer 20)(Etempvar _t'71 tulong)).
Proof. repeat split;reflexivity. Qed.

Lemma actual_header_field_pointer ge environment temporaries memory object offset index:
  sizeof(genv_cenv ge)(Tstruct _host_field noattr)=40->
  temporaries!_fields=Some(Vptr object offset)->temporaries!_index=Some(Vint(Int.repr(Z.of_nat index)))->
  (index<=8)%nat->
  expression_value ge environment temporaries memory header_field_pointer
    (Vptr object(Ptrofs.add offset(Ptrofs.repr(40*Z.of_nat index)))).
Proof.
  intros SIZE FIELDS INDEX BOUND;unfold header_field_pointer;eapply binary_expression_value.
  - apply old_expression_value,value_temp;exact FIELDS.
  - apply old_expression_value,value_temp;exact INDEX.
  - change(Some(Vptr object(Ptrofs.add offset(Ptrofs.mul(Ptrofs.repr(sizeof(genv_cenv ge)(Tstruct _host_field noattr)))
      (Ptrofs.of_intu(Int.repr(Z.of_nat index))))))=
      Some(Vptr object(Ptrofs.add offset(Ptrofs.repr(40*Z.of_nat index))))).
    rewrite SIZE;unfold Ptrofs.of_intu,Ptrofs.of_int;rewrite Int.unsigned_repr by(change Int.max_unsigned with 4294967295;lia).
    unfold Ptrofs.mul;rewrite !Ptrofs.unsigned_repr by(change Ptrofs.max_unsigned with 18446744073709551615;lia);reflexivity.
Qed.

Lemma actual_header_field_value ge environment temporaries memory object offset index member ty delta chunk value:
  sizeof(genv_cenv ge)(Tstruct _host_field noattr)=40->field_member_layout ge member delta->
  access_mode ty=By_value chunk->
  temporaries!_fields=Some(Vptr object offset)->temporaries!_index=Some(Vint(Int.repr(Z.of_nat index)))->
  (index<8)%nat->0<=delta /\delta+size_chunk chunk<=40->Ptrofs.unsigned offset+320<=Ptrofs.modulus->
  Mem.load chunk memory object(Ptrofs.unsigned offset+40*Z.of_nat index+delta)=Some value->
  expression_value ge environment temporaries memory(header_field_expr member ty)value.
Proof.
  intros SIZE[composite[LAYOUT MEMBER]]ACCESS FIELDS INDEX BOUND DELTA SPAN LOAD.
  eapply location_read_value with(b:=object)
    (ofs:=Ptrofs.add(Ptrofs.add offset(Ptrofs.repr(40*Z.of_nat index)))(Ptrofs.repr delta)).
  - unfold header_field_expr;eapply struct_location_value with(id:=_host_field)(co:=composite)(att:=noattr)(delta:=delta).
    + eapply location_read_value with(b:=object)(ofs:=Ptrofs.add offset(Ptrofs.repr(40*Z.of_nat index))).
      * apply pointer_location_value;apply actual_header_field_pointer;try assumption;lia.
      * apply deref_loc_copy;reflexivity.
    + reflexivity.
    + exact LAYOUT.
    + exact MEMBER.
  - apply deref_loc_value with(chunk:=chunk);[exact ACCESS|].
    pose proof(Ptrofs.unsigned_range offset)as OFFSET.
    change Ptrofs.modulus with 18446744073709551616 in SPAN,OFFSET.
    pose proof(size_chunk_pos chunk)as CHUNK.
    unfold Mem.loadv;rewrite !Ptrofs.add_unsigned.
    rewrite(Ptrofs.unsigned_repr(40*Z.of_nat index))by(change Ptrofs.max_unsigned with 18446744073709551615;lia).
    rewrite(Ptrofs.unsigned_repr delta)by(change Ptrofs.max_unsigned with 18446744073709551615;lia).
    rewrite(Ptrofs.unsigned_repr(Ptrofs.unsigned offset+40*Z.of_nat index))by
      (change Ptrofs.max_unsigned with 18446744073709551615;lia).
    rewrite(Ptrofs.unsigned_repr(Ptrofs.unsigned offset+40*Z.of_nat index+delta))by
      (change Ptrofs.max_unsigned with 18446744073709551615;lia).
    rewrite zle_true by(change Ptrofs.modulus with 18446744073709551616;lia);exact LOAD.
Qed.

Lemma actual_header_fields_pointer ge environment temporaries memory object base index:
  environment!_header=Some(object,tarray tuchar 112)->temporaries!_index=Some(Vint(Int.repr(Z.of_nat index)))->
  0<=base<=20->(index<8)%nat->
  expression_value ge environment temporaries memory(header_fields_pointer base)
    (Vptr object(Ptrofs.repr(base+12*Z.of_nat index))).
Proof.
  intros ARRAY INDEX BASE BOUND;unfold header_fields_pointer;eapply binary_expression_value.
  - apply actual_header_pointer_value;[exact ARRAY|lia].
  - eapply binary_expression_value.
    + apply old_expression_value;constructor.
    + apply old_expression_value,value_temp;exact INDEX.
    + reflexivity.
  - change(Some(Vptr object(Ptrofs.add(Ptrofs.repr base)
      (Ptrofs.mul(Ptrofs.repr 1)(Ptrofs.of_intu(Int.mul(Int.repr 12)(Int.repr(Z.of_nat index)))))))=
      Some(Vptr object(Ptrofs.repr(base+12*Z.of_nat index)))).
    rewrite Ptrofs.mul_commut,Ptrofs.mul_one;unfold Ptrofs.of_intu,Ptrofs.of_int,Int.mul.
    rewrite(Int.unsigned_repr 12)by(change Int.max_unsigned with 4294967295;lia).
    rewrite(Int.unsigned_repr(Z.of_nat index))by(change Int.max_unsigned with 4294967295;lia).
    rewrite(Int.unsigned_repr(12*Z.of_nat index))by(change Int.max_unsigned with 4294967295;lia).
    unfold Ptrofs.add;rewrite !Ptrofs.unsigned_repr by(change Ptrofs.max_unsigned with 18446744073709551615;lia);reflexivity.
Qed.
