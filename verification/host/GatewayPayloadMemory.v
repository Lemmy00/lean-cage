(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Payload expressions retain the original selected field cells and bytes. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine LocalAccess.
From HostGateway Require Import GatewaySource GatewayStreamInterface GatewayArrayField GatewayFieldStores GatewaySendState
  GatewaySendInterface GatewayReadContext GatewayTransportFrame GatewayPayloadPaths.
Import ListNotations.
Open Scope Z_scope.

Record gateway_payload_row:Type:={
  gateway_payload_pointer:val;
  gateway_payload_size:int64;
  gateway_payload_bytes:list Byte.int
}.
Definition gateway_payload_address(pointer:val):Prop:=
  match pointer with Vptr _ _|Vlong _=>True|_=>False end.
Definition gateway_payload_field_cells memory object offset(rows:nat->gateway_payload_row):Prop:=
  forall index,(index<8)%nat->
    Mem.load Mptr memory object(Ptrofs.unsigned offset+40*Z.of_nat index+16)=Some(gateway_payload_pointer(rows index)) /\
    Mem.load Mint64 memory object(Ptrofs.unsigned offset+40*Z.of_nat index+8)=Some(Vlong(gateway_payload_size(rows index))).
Definition gateway_payload_rows_readable readonly reference(rows:nat->gateway_payload_row):Prop:=
  forall index,(index<8)%nat->gateway_payload_address(gateway_payload_pointer(rows index)) /\
    gateway_payload_cells readonly(gateway_payload_pointer(rows index))(Int64.unsigned(gateway_payload_size(rows index))) /\
    gateway_sent_payload reference(gateway_payload_pointer(rows index))(Int64.unsigned(gateway_payload_size(rows index)))
      (gateway_payload_bytes(rows index)).

Lemma gateway_payload_address_cast pointer memory:
  gateway_payload_address pointer->sem_cast pointer(tptr tschar)(tptr tvoid)memory=Some pointer.
Proof. destruct pointer;cbn;intros;try contradiction;reflexivity. Qed.

Lemma gateway_payload_field_cells_retained before after object offset rows readonly:
  gateway_payload_field_cells before object offset rows->Mem.unchanged_on readonly before after->
  (forall position,Ptrofs.unsigned offset<=position<Ptrofs.unsigned offset+320->readonly object position)->
  gateway_payload_field_cells after object offset rows.
Proof.
  intros CELLS FRAME COVER index INDEX;destruct(CELLS index INDEX)as[DATA SIZE];split.
  - eapply Mem.load_unchanged_on;[exact FRAME| |exact DATA].
    intros position RANGE;apply COVER;change(size_chunk Mptr)with 8 in RANGE;lia.
  - eapply Mem.load_unchanged_on;[exact FRAME| |exact SIZE].
    intros position RANGE;apply COVER;cbn[size_chunk]in RANGE;lia.
Qed.

Lemma gateway_payload_bytes_retained before after readonly pointer amount bytes:
  gateway_payload_cells readonly pointer amount->gateway_sent_payload before pointer amount bytes->
  Mem.unchanged_on readonly before after->gateway_sent_payload after pointer amount bytes.
Proof.
  intros COVER[[ZERO EMPTY]|[object[offset[POINTER BYTES]]]]FRAME;[left;split;assumption|].
  right;exists object,offset;split;[exact POINTER|].
  destruct COVER as[ZERO|[other[base[OTHER[BOUND COVER]]]]].
  - rewrite ZERO,Mem.loadbytes_empty in BYTES|-*by lia;exact BYTES.
  - rewrite POINTER in OTHER;inversion OTHER;subst other base.
    eapply Mem.loadbytes_unchanged_on;[exact FRAME|exact COVER|exact BYTES].
Qed.

Section Expressions.
Context {World}(native:World->block->Prop)(stable:World->block->Z->Prop)
  (discipline:option val->mem->World->Prop).
Variables(stream:Values.block)(readonly:Values.block->Z->Prop)(reference:mem)(origin:World)(initial:gateway_stream_values)
  (ge:Clight.genv)(environment:env)(temporaries:temp_env)(object:Values.block)(offset:ptrofs)
  (rows:nat->gateway_payload_row)(index:nat).
Hypotheses(SIZEOF:sizeof(genv_cenv ge)(Tstruct _host_field noattr)=40)
  (DATA:field_member_layout ge _data 16)(SIZE:field_member_layout ge _size 8)
  (FIELDS:temporaries!_fields=Some(Vptr object offset))
  (INDEX:temporaries!_index__1=Some(Vint(Int.repr(Z.of_nat index))))(BOUND:(index<8)%nat)
  (SPAN:Ptrofs.unsigned offset+320<=Ptrofs.modulus)(CELLS:gateway_payload_field_cells reference object offset rows)
  (COVER:forall position,Ptrofs.unsigned offset<=position<Ptrofs.unsigned offset+320->readonly object position).

Theorem gateway_payload_current_data memory world:
  gateway_sending_state native stable discipline stream readonly reference origin initial memory world->
  expression_value ge environment temporaries memory payload_data_expression(gateway_payload_pointer(rows index)).
Proof.
  intros[current[RAW[TRANSPORT HISTORY]]].
  pose proof(gateway_payload_field_cells_retained reference memory object offset rows readonly CELLS
    (gateway_transport_readonly _ _ _ _ _ _ _ _ _ _ _ HISTORY)COVER)as CURRENT.
  change(expression_value ge environment temporaries memory(gateway_indexed_field_expr _index__1 _data(tptr tschar))
    (gateway_payload_pointer(rows index))).
  eapply gateway_indexed_field_value with(delta:=16)(chunk:=Mptr);
    [exact SIZEOF|exact DATA|reflexivity|exact FIELDS|exact INDEX|exact BOUND|change(size_chunk Mptr)with 8;lia
    |exact SPAN|exact(proj1(CURRENT index BOUND))].
Qed.

Theorem gateway_payload_current_size memory world:
  gateway_sending_state native stable discipline stream readonly reference origin initial memory world->
  expression_value ge environment temporaries memory payload_size_expression(Vlong(gateway_payload_size(rows index))).
Proof.
  intros[current[RAW[TRANSPORT HISTORY]]].
  pose proof(gateway_payload_field_cells_retained reference memory object offset rows readonly CELLS
    (gateway_transport_readonly _ _ _ _ _ _ _ _ _ _ _ HISTORY)COVER)as CURRENT.
  change(expression_value ge environment temporaries memory(gateway_indexed_field_expr _index__1 _size tulong)
    (Vlong(gateway_payload_size(rows index)))).
  eapply gateway_indexed_field_value with(delta:=8)(chunk:=Mint64);
    [exact SIZEOF|exact SIZE|reflexivity|exact FIELDS|exact INDEX|exact BOUND|cbn[size_chunk];lia
    |exact SPAN|exact(proj2(CURRENT index BOUND))].
Qed.
End Expressions.
