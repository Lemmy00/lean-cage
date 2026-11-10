(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Real bounded array indices locate the original field ABI cells. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Errors Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayFieldStores.
Open Scope Z_scope.

Definition gateway_indexed_field_pointer index_identifier:=Ebinop Oadd
  (Etempvar _fields(tptr(Tstruct _host_field noattr)))(Etempvar index_identifier tuint)(tptr(Tstruct _host_field noattr)).
Definition gateway_indexed_field_expr index_identifier member ty:=
  Efield(Ederef(gateway_indexed_field_pointer index_identifier)(Tstruct _host_field noattr))member ty.

Lemma gateway_indexed_field_pointer_value ge environment temporaries memory object offset index_identifier index:
  sizeof(genv_cenv ge)(Tstruct _host_field noattr)=40->
  temporaries!_fields=Some(Vptr object offset)->temporaries!index_identifier=Some(Vint(Int.repr(Z.of_nat index)))->
  (index<=8)%nat->
  expression_value ge environment temporaries memory (gateway_indexed_field_pointer index_identifier)
    (Vptr object(Ptrofs.add offset(Ptrofs.repr(40*Z.of_nat index)))).
Proof.
  intros SIZE FIELDS INDEX BOUND;unfold gateway_indexed_field_pointer;eapply binary_expression_value.
  - apply old_expression_value,value_temp;exact FIELDS.
  - apply old_expression_value,value_temp;exact INDEX.
  - change(Some(Vptr object(Ptrofs.add offset(Ptrofs.mul(Ptrofs.repr(sizeof(genv_cenv ge)(Tstruct _host_field noattr)))
      (Ptrofs.of_intu(Int.repr(Z.of_nat index))))))=
      Some(Vptr object(Ptrofs.add offset(Ptrofs.repr(40*Z.of_nat index))))).
    rewrite SIZE;unfold Ptrofs.of_intu,Ptrofs.of_int;rewrite Int.unsigned_repr by(change Int.max_unsigned with 4294967295;lia).
    unfold Ptrofs.mul;rewrite !Ptrofs.unsigned_repr by(change Ptrofs.max_unsigned with 18446744073709551615;lia);reflexivity.
Qed.

Lemma gateway_indexed_field_value ge environment temporaries memory object offset index_identifier index member ty delta chunk value:
  sizeof(genv_cenv ge)(Tstruct _host_field noattr)=40->field_member_layout ge member delta->
  access_mode ty=By_value chunk->
  temporaries!_fields=Some(Vptr object offset)->temporaries!index_identifier=Some(Vint(Int.repr(Z.of_nat index)))->
  (index<8)%nat->0<=delta /\delta+size_chunk chunk<=40->Ptrofs.unsigned offset+320<=Ptrofs.modulus->
  Mem.load chunk memory object(Ptrofs.unsigned offset+40*Z.of_nat index+delta)=Some value->
  expression_value ge environment temporaries memory(gateway_indexed_field_expr index_identifier member ty)value.
Proof.
  intros SIZE[composite[LAYOUT MEMBER]]ACCESS FIELDS INDEX BOUND DELTA SPAN LOAD.
  eapply location_read_value with(b:=object)
    (ofs:=Ptrofs.add(Ptrofs.add offset(Ptrofs.repr(40*Z.of_nat index)))(Ptrofs.repr delta)).
  - unfold gateway_indexed_field_expr;eapply struct_location_value with(id:=_host_field)(co:=composite)(att:=noattr)(delta:=delta).
    + eapply location_read_value with(b:=object)(ofs:=Ptrofs.add offset(Ptrofs.repr(40*Z.of_nat index))).
      * apply pointer_location_value;apply gateway_indexed_field_pointer_value;try assumption;lia.
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
