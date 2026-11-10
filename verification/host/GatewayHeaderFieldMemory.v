(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Descriptor loads retain the exact original caller field cells. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events
  Ctypes Ctypesdefs Cop Clight.
Require Import Machine LocalAccess.
From HostGateway Require Import GatewaySource GatewayHeaderFields GatewayFieldStores
  GatewayHeaderPacket GatewayHeaderRuntime GatewayThreadRuntime GatewayHeaderExpression.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Definition gateway_header_field_cells memory object offset(rows:nat->int*int64):Prop:=
  forall index,(index<8)%nat->
    Mem.load Mint32 memory object(Ptrofs.unsigned offset+40*Z.of_nat index)=Some(Vint(fst(rows index))) /\
    Mem.load Mint64 memory object(Ptrofs.unsigned offset+40*Z.of_nat index+8)=Some(Vlong(snd(rows index))).

Lemma gateway_header_field_cells_retained before after object offset rows readonly:
  gateway_header_field_cells before object offset rows->Mem.unchanged_on readonly before after->
  (forall position,Ptrofs.unsigned offset<=position<Ptrofs.unsigned offset+320->readonly object position)->
  gateway_header_field_cells after object offset rows.
Proof.
  intros CELLS FRAME COVER index INDEX;destruct(CELLS index INDEX)as[KIND SIZE];split.
  - eapply Mem.load_unchanged_on;[exact FRAME| |exact KIND].
    intros position RANGE;apply COVER;cbn[size_chunk]in RANGE;lia.
  - eapply Mem.load_unchanged_on;[exact FRAME| |exact SIZE].
    intros position RANGE;apply COVER;cbn[size_chunk]in RANGE;lia.
Qed.

Section Values.
Context {World}(native:World->block->Prop)(stable:World->block->Z->Prop)
  (discipline:option val->mem->World->Prop).
Variables(mode:option val)(header:Values.block)(held:list Values.block)(readonly:Values.block->Z->Prop)
  (reference:mem)(origin:World)(ge:Clight.genv)(environment:env)(temporaries:temp_env)
  (object:Values.block)(offset:ptrofs)(rows:nat->int*int64)(index:nat).
Hypotheses(SIZEOF:sizeof(genv_cenv ge)(Tstruct _host_field noattr)=40)
  (KIND:field_member_layout ge _kind 0)(SIZE:field_member_layout ge _size 8)
  (FIELDS:temporaries!_fields=Some(Vptr object offset))
  (INDEX:temporaries!_index=Some(Vint(Int.repr(Z.of_nat index))))(BOUND:(index<8)%nat)
  (SPAN:Ptrofs.unsigned offset+320<=Ptrofs.modulus)
  (CELLS:gateway_header_field_cells reference object offset rows)
  (COVER:forall position,Ptrofs.unsigned offset<=position<Ptrofs.unsigned offset+320->readonly object position).

Theorem gateway_header_current_kind bytes memory world:
  gateway_header_packet native stable discipline mode header held readonly reference origin bytes memory world->
  expression_value ge environment temporaries memory header_fields_kind_expr(Vint(fst(rows index))).
Proof.
  intros[RESOURCES WRITABLE LENGTH BYTES].
  pose proof(gateway_header_field_cells_retained reference memory object offset rows readonly CELLS
    (gateway_header_frame _ _ _ _ _ _ _ _ _ _ _ RESOURCES)COVER)as CURRENT.
  change(expression_value ge environment temporaries memory(header_field_expr _kind tuint)(Vint(fst(rows index)))).
  eapply actual_header_field_value with(delta:=0)(chunk:=Mint32);
    [exact SIZEOF|exact KIND|reflexivity|exact FIELDS|exact INDEX|exact BOUND|cbn[size_chunk];lia|exact SPAN|].
  rewrite Z.add_0_r;exact(proj1(CURRENT index BOUND)).
Qed.

Theorem gateway_header_current_size bytes memory world:
  gateway_header_packet native stable discipline mode header held readonly reference origin bytes memory world->
  expression_value ge environment temporaries memory header_fields_size_expr(Vlong(snd(rows index))).
Proof.
  intros[RESOURCES WRITABLE LENGTH BYTES].
  pose proof(gateway_header_field_cells_retained reference memory object offset rows readonly CELLS
    (gateway_header_frame _ _ _ _ _ _ _ _ _ _ _ RESOURCES)COVER)as CURRENT.
  change(expression_value ge environment temporaries memory(header_field_expr _size tulong)(Vlong(snd(rows index)))).
  eapply actual_header_field_value with(delta:=8)(chunk:=Mint64);
    [exact SIZEOF|exact SIZE|reflexivity|exact FIELDS|exact INDEX|exact BOUND|cbn[size_chunk];lia|exact SPAN|exact(proj2(CURRENT index BOUND))].
Qed.
End Values.
