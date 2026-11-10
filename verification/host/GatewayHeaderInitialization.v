(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual request header initializes all 112 owned bytes. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayMemoryPrefixes GatewayFramedRuntime
  GatewayHeaderRuntime GatewayThreadRuntime GatewayStreamInterface GatewayWordsMemory GatewaySpawnVectors.
Import ListNotations.
Open Scope Z_scope.

Fixpoint gateway_find_header_initialization(body:statement):option statement:=
  match body with
  |Ssequence first rest=>
    match first with
    |Sassign(Ederef(Ebinop Oadd(Evar identifier _) _ _)_) _=>
      if Pos.eqb identifier _header then Some body else gateway_find_header_initialization rest
    |_=>match gateway_find_header_initialization first with
      |Some found=>Some found|None=>gateway_find_header_initialization rest end
    end
  |_=>None
  end.
Definition header_source_start:=Eval vm_compute in
  match gateway_find_header_initialization(fn_body f_host_exchange)with Some found=>found|None=>Sskip end.
Fixpoint header_source_after(count:nat):statement:=match count with
  |O=>header_source_start|S prior=>match header_source_after prior with Ssequence _ rest=>rest|_=>Sskip end end.
Definition header_source_assignment index:=match header_source_after index with Ssequence first _=>first|_=>Sskip end.
Definition header_source_cell index:=Ederef(Ebinop Oadd(Evar _header(tarray tuchar 112))
  (Econst_int(Int.repr(Z.of_nat index))tint)(tptr tuchar))tuchar.
Definition header_initial_bytes:list Z:=[76;67;72;82;69;81;49;0]++repeat 0 104.
Definition header_initial_values:=map Int.repr header_initial_bytes.
Definition header_initial_byte index:=nth index header_initial_values Int.zero.
Definition header_initial_prefix index:=firstn index header_initial_values.

Theorem actual_header_initialization_table:
  Forall(fun index=>
    (match header_source_after index with Ssequence _ _=>True|_=>False end) /\
    header_source_assignment index=Sassign(header_source_cell index)
      (Econst_int(header_initial_byte index)tint) /\
    header_initial_prefix(S index)=header_initial_prefix index++[header_initial_byte index] /\
    length(header_initial_prefix index)=index /\
    Int.zero_ext 8(header_initial_byte index)=header_initial_byte index)(seq 0 112).
Proof.
  apply Forall_forall;intros index MEMBER;apply in_seq in MEMBER.
  do 112(destruct index as[|index];[solve[repeat split;reflexivity]|]);lia.
Qed.
Lemma actual_header_source_tail index:
  (index<112)%nat->header_source_after index=Ssequence(header_source_assignment index)(header_source_after(S index)).
Proof.
  intro INDEX.
  pose proof((proj1(Forall_forall _ _))actual_header_initialization_table index ltac:(apply in_seq;lia))as[SEQUENCE REST].
  change(header_source_after index=Ssequence
    (match header_source_after index with Ssequence first _=>first|_=>Sskip end)
    (match header_source_after index with Ssequence _ rest=>rest|_=>Sskip end)).
  destruct(header_source_after index);cbn in SEQUENCE;try contradiction;reflexivity.
Qed.
Theorem actual_header_initialization_length:length header_initial_values=112%nat.
Proof. reflexivity. Qed.

Lemma actual_header_source_cell ge environment temporaries memory object index:
  environment!_header=Some(object,tarray tuchar 112)->(index<112)%nat->
  location_value ge environment temporaries memory(header_source_cell index)object(Ptrofs.repr(Z.of_nat index)).
Proof.
  intros ARRAY INDEX;unfold header_source_cell;apply pointer_location_value;eapply binary_expression_value.
  - eapply location_read_value;[apply local_location_value;exact ARRAY|].
    apply deref_loc_reference;reflexivity.
  - apply old_expression_value;constructor.
  - change(Some(Vptr object(Ptrofs.add Ptrofs.zero
      (Ptrofs.mul(Ptrofs.repr 1)(Ptrofs.of_ints(Int.repr(Z.of_nat index))))))=
      Some(Vptr object(Ptrofs.repr(Z.of_nat index)))).
    rewrite Ptrofs.mul_commut,Ptrofs.mul_one,Ptrofs.add_zero_l.
    unfold Ptrofs.of_ints;rewrite Int.signed_repr;[reflexivity|].
    change Int.min_signed with(-2147483648);change Int.max_signed with 2147483647;lia.
Qed.
