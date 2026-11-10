(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The real numeric scan preserves its initialized null result
   temporary until the checked constructor guard, including every rejected byte. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayValueEntry GatewayValueExpressions GatewayScalarContext
  GatewayScalarTerminate GatewayScalarBytesPath GatewaySourceSegments GatewaySourceDynamic GatewayFramedRuntime
  GatewayIntegerCanonical GatewayIntegerLoop GatewayIntegerScan.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_integer_loop_step_retained {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)slots parameters continuation object index count(valid:bool)byte memory:
  gateway_ambient_closed backend property->0<=index /\index<count /\count<=32->
  parameters!_bytes=Some(Vptr object Ptrofs.zero)->parameters!_index=Some(Vlong(Int64.repr index))->
  parameters!_valid=Some(Vint(if valid then Int.one else Int.zero))->
  (forall memory world,property memory world->Mem.loadv Mint64 memory(Vptr(gateway_value_size_slot slots)Ptrofs.zero)=Some(Vlong(Int64.repr count)))->
  (forall memory world,property memory world->Mem.loadv Mint8signed memory(Vptr object(Ptrofs.repr index))=
    Some(Vint(Int.repr(Byte.signed byte))))->
  exists next_parameters,
    gateway_source_segment backend ge property
      (State f_host_value gateway_integer_loop continuation(gateway_value_environment slots)parameters memory)
      (State f_host_value gateway_integer_loop continuation(gateway_value_environment slots)next_parameters memory)property /\
    next_parameters!_bytes=Some(Vptr object Ptrofs.zero) /\
    next_parameters!_index=Some(Vlong(Int64.repr(index+1))) /\
    next_parameters!_valid=Some(Vint(if valid&&gateway_integer_digit byte then Int.one else Int.zero)) /\
    next_parameters!_value=parameters!_value.
Proof.
  intros CLOSED INDEX BYTES POSITION VALID SIZE CHARACTER.
  assert(LESS:Int64.ltu(Int64.repr index)(Int64.repr count)=true).
  { unfold Int64.ltu;rewrite !Int64.unsigned_repr by(change Int64.max_unsigned with 18446744073709551615;lia);apply zlt_true;lia. }
  destruct(zlt(Byte.signed byte)48)as[LOW|NOT_LOW];
    [|destruct(zlt 57(Byte.signed byte))as[HIGH|NOT_HIGH]];eexists;split.
  all:lazymatch goal with
  | |-gateway_source_segment _ _ _ _ _ _=>
    rewrite gateway_integer_loop_actual;
    eapply gateway_segment_same with(next:=State f_host_value gateway_integer_loop_body
      (Kloop1 gateway_integer_loop_body gateway_integer_loop_increment continuation)(gateway_value_environment slots)parameters memory);
      [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_loop|];
    unfold gateway_integer_loop_body,gateway_integer_loop_increment;
    gateway_integer_segment_to_loop CLOSED
      ltac:(fun _=>first[apply gateway_value_size_expression;eapply SIZE;eassumption|
        eapply gateway_integer_character with(index:=index)(byte:=byte)(object:=object);[lia|repeat rewrite PTree.gso by discriminate;exact BYTES|
          repeat rewrite PTree.gso by discriminate;exact POSITION|eapply CHARACTER;eassumption]|
        match goal with |-?GOAL=>idtac "UNHANDLED LOAD" GOAL;fail 1 end])
      ltac:(fun _=>cbn -[Int64.ltu Int64.unsigned Int64.repr Int64.add Int.signed Int.repr Int.lt];unfold Int.lt;
        repeat rewrite Int.signed_repr by(pose proof(gateway_integer_signed_range byte);
          change Int.min_signed with (-2147483648);change Int.max_signed with 2147483647;lia);
        try rewrite LESS;
        repeat first[rewrite zlt_true by lia|rewrite zlt_false by lia];
        first[reflexivity|match goal with |-?GOAL=>idtac "UNHANDLED REDUCE" GOAL;fail 1 end])
  | _=>idtac end.
  all:repeat split;try solve[repeat rewrite PTree.gso by discriminate;exact BYTES].
  all:repeat rewrite PTree.gso by discriminate;try rewrite PTree.gss;try reflexivity.
  all:try solve[rewrite Int64.add_unsigned;rewrite !Int64.unsigned_repr by
    (change Int64.max_unsigned with 18446744073709551615;lia);reflexivity].
  all:rewrite gateway_integer_digit_signed.
  all:destruct(48<=?Byte.signed byte)eqn:FROM;destruct(Byte.signed byte<=?57)eqn:TO;
    first[apply Z.leb_le in FROM|apply Z.leb_gt in FROM];
    first[apply Z.leb_le in TO|apply Z.leb_gt in TO];try lia;cbn;
    destruct valid;first[reflexivity|exact VALID].
Qed.

Theorem gateway_integer_scan_segment_retained {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)slots continuation object count memory:
  gateway_ambient_closed backend property->0<=count<=32->
  (forall memory world,property memory world->Mem.loadv Mint64 memory(Vptr(gateway_value_size_slot slots)Ptrofs.zero)=Some(Vlong(Int64.repr count)))->
  forall remaining parameters index(valid:bool),0<=index->index+Z.of_nat(length remaining)=count->
  parameters!_bytes=Some(Vptr object Ptrofs.zero)->parameters!_index=Some(Vlong(Int64.repr index))->
  parameters!_valid=Some(Vint(if valid then Int.one else Int.zero))->
  (forall offset byte,nth_error remaining offset=Some byte->forall memory world,property memory world->
    Mem.loadv Mint8signed memory(Vptr object(Ptrofs.repr(index+Z.of_nat offset)))=Some(Vint(Int.repr(Byte.signed byte))))->
  exists final_parameters,
    gateway_source_segment backend ge property
      (State f_host_value gateway_integer_loop continuation(gateway_value_environment slots)parameters memory)
      (State f_host_value Sskip continuation(gateway_value_environment slots)final_parameters memory)property /\
    final_parameters!_bytes=Some(Vptr object Ptrofs.zero) /\
    final_parameters!_index=Some(Vlong(Int64.repr count)) /\
    final_parameters!_valid=Some(Vint(if valid&&forallb gateway_integer_digit remaining then Int.one else Int.zero)) /\
    final_parameters!_value=parameters!_value.
Proof.
  intros CLOSED COUNT SIZE remaining;induction remaining as[|byte rest IH];
    intros parameters index valid INDEX LENGTH BYTES POSITION VALID LOADS.
  - cbn in LENGTH;rewrite Z.add_0_r in LENGTH;subst index.
    exists(PTree.set _t'67(Vlong(Int64.repr count))parameters);split.
    + eapply gateway_integer_loop_exit;eassumption.
    + repeat split;rewrite PTree.gso by discriminate;try assumption;try reflexivity.
      cbn;destruct valid;exact VALID.
  - change(index+Z.of_nat(S(length rest))=count)in LENGTH.
    assert(STEP_INDEX:0<=index /\index<count /\count<=32).
    { rewrite Nat2Z.inj_succ in LENGTH;lia. }
    destruct(gateway_integer_loop_step_retained backend ge property slots parameters continuation object index count valid byte memory CLOSED STEP_INDEX
      BYTES POSITION VALID SIZE ltac:(intros current world GOOD;specialize(LOADS 0%nat byte eq_refl current world GOOD);
        cbn in LOADS;rewrite Z.add_0_r in LOADS;exact LOADS))
      as(next_parameters &STEP &NEXT_BYTES &NEXT_POSITION &NEXT_VALID &NEXT_VALUE).
    destruct(IH next_parameters(index+1)(valid&&gateway_integer_digit byte)ltac:(lia)
      ltac:(rewrite Nat2Z.inj_succ in LENGTH;lia)NEXT_BYTES NEXT_POSITION NEXT_VALID
      ltac:(intros offset selected SELECTED current world GOOD;specialize(LOADS(S offset)selected SELECTED current world GOOD);
        rewrite Nat2Z.inj_succ in LOADS;replace(index+Z.succ(Z.of_nat offset))with(index+1+Z.of_nat offset)in LOADS by lia;exact LOADS))
      as(final_parameters &TAIL &FINAL_BYTES &FINAL_POSITION &FINAL_VALID &FINAL_VALUE).
    exists final_parameters;split;[eapply gateway_integer_segments_append;eassumption|].
    split;[exact FINAL_BYTES|]. split;[exact FINAL_POSITION|].
    split;[cbn;rewrite andb_assoc;exact FINAL_VALID|rewrite FINAL_VALUE;exact NEXT_VALUE].
Qed.
