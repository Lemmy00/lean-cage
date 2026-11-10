(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Every actual digit-loop position is checked before the source
   exits to its constructor/error guard; the same native byte loads justify the final flag. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayValueEntry GatewayScalarContext GatewaySourceSegments
  GatewaySourceTactics GatewayIntegerCanonical GatewayIntegerLoop GatewayFramedRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_integer_loop_test:=match gateway_integer_loop_body with Ssequence first _=>first|_=>Sskip end.
Definition gateway_integer_loop_iteration:=match gateway_integer_loop_body with Ssequence _ rest=>rest|_=>Sskip end.
Definition gateway_integer_loop_guard:=match gateway_integer_loop_test with Ssequence _ rest=>rest|_=>Sskip end.

Lemma gateway_integer_segments_append {World Event}(backend:gateway_backend World Event)ge
    property first middle between last result:
  gateway_source_segment backend ge property first middle between->
  gateway_source_segment backend ge between middle last result->
  gateway_source_segment backend ge property first last result.
Proof.
  intro PREFIX;induction PREFIX;intro SUFFIX;[exact SUFFIX|].
  eapply gateway_segment_next;[exact H|exact H0|exact H1|apply IHPREFIX;exact SUFFIX].
Qed.

Theorem gateway_integer_loop_exit {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)slots parameters continuation count memory:
  gateway_ambient_closed backend property->parameters!_index=Some(Vlong(Int64.repr count))->
  (forall memory world,property memory world->Mem.loadv Mint64 memory(Vptr(gateway_value_size_slot slots)Ptrofs.zero)=Some(Vlong(Int64.repr count)))->
  gateway_source_segment backend ge property
    (State f_host_value gateway_integer_loop continuation(gateway_value_environment slots)parameters memory)
    (State f_host_value Sskip continuation(gateway_value_environment slots)(PTree.set _t'67(Vlong(Int64.repr count))parameters)memory)property.
Proof.
  intros CLOSED INDEX SIZE.
  change gateway_integer_loop with(Sloop gateway_integer_loop_body gateway_integer_loop_increment).
  eapply gateway_segment_same with(next:=State f_host_value gateway_integer_loop_body
    (Kloop1 gateway_integer_loop_body gateway_integer_loop_increment continuation)(gateway_value_environment slots)parameters memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_loop|].
  change gateway_integer_loop_body with(Ssequence gateway_integer_loop_test gateway_integer_loop_iteration).
  gateway_segment_seq CLOSED.
  change gateway_integer_loop_test with(Ssequence(Sset _t'67(Evar _size tulong))gateway_integer_loop_guard).
  gateway_segment_seq CLOSED.
  eapply gateway_segment_same with(next:=State f_host_value Sskip
    (Kseq gateway_integer_loop_guard(Kseq gateway_integer_loop_iteration
      (Kloop1 gateway_integer_loop_body gateway_integer_loop_increment continuation)))
    (gateway_value_environment slots)(PTree.set _t'67(Vlong(Int64.repr count))parameters)memory).
  - exact CLOSED.
  - cbn;tauto.
  - intros;apply certified_set_edge,gateway_value_size_expression;eapply SIZE;eassumption.
  - gateway_segment_skip CLOSED.
    eapply gateway_segment_same with(next:=State f_host_value Sbreak
      (Kseq gateway_integer_loop_iteration(Kloop1 gateway_integer_loop_body gateway_integer_loop_increment continuation))
      (gateway_value_environment slots)(PTree.set _t'67(Vlong(Int64.repr count))parameters)memory).
    + exact CLOSED.
    + cbn;tauto.
    + intros;eapply certified_if_edge with(b:=false).
      * apply old_expression_value;eapply value_binary with(v:=Vlong(Int64.repr count))(w:=Vlong(Int64.repr count))(result:=Vint Int.zero).
        -- apply value_temp;rewrite PTree.gso by discriminate;exact INDEX.
        -- apply value_temp;apply PTree.gss.
        -- change(Some(Val.of_bool(Int64.ltu(Int64.repr count)(Int64.repr count)))=Some(Vint Int.zero)).
           unfold Int64.ltu;rewrite zlt_false by lia;reflexivity.
      * reflexivity.
    + eapply gateway_segment_same with(next:=State f_host_value Sbreak
        (Kloop1 gateway_integer_loop_body gateway_integer_loop_increment continuation)
        (gateway_value_environment slots)(PTree.set _t'67(Vlong(Int64.repr count))parameters)memory);
        [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_break_seq|].
      eapply gateway_segment_same with(next:=State f_host_value Sskip continuation
        (gateway_value_environment slots)(PTree.set _t'67(Vlong(Int64.repr count))parameters)memory);
        [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_break_loop1|apply gateway_segment_here].
Qed.

Theorem gateway_integer_scan_segment {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
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
    final_parameters!_valid=Some(Vint(if valid&&forallb gateway_integer_digit remaining then Int.one else Int.zero)).
Proof.
  intros CLOSED COUNT SIZE remaining;induction remaining as[|byte rest IH];
    intros parameters index valid INDEX LENGTH BYTES POSITION VALID LOADS.
  - cbn in LENGTH;rewrite Z.add_0_r in LENGTH;subst index.
    exists(PTree.set _t'67(Vlong(Int64.repr count))parameters);split.
    + eapply gateway_integer_loop_exit;eassumption.
    + repeat split;rewrite PTree.gso by discriminate;try assumption.
      cbn;destruct valid;exact VALID.
  - change(index+Z.of_nat(S(length rest))=count)in LENGTH.
    assert(STEP_INDEX:0<=index /\index<count /\count<=32).
    { rewrite Nat2Z.inj_succ in LENGTH;lia. }
    destruct(gateway_integer_loop_step backend ge property slots parameters continuation object index count valid byte memory CLOSED STEP_INDEX
      BYTES POSITION VALID SIZE ltac:(intros current world GOOD;specialize(LOADS 0%nat byte eq_refl current world GOOD);
        cbn in LOADS;rewrite Z.add_0_r in LOADS;exact LOADS))
      as(next_parameters &STEP &NEXT_BYTES &NEXT_POSITION &NEXT_VALID).
    destruct(IH next_parameters(index+1)(valid&&gateway_integer_digit byte)ltac:(lia)
      ltac:(rewrite Nat2Z.inj_succ in LENGTH;lia)NEXT_BYTES NEXT_POSITION NEXT_VALID
      ltac:(intros offset selected SELECTED current world GOOD;specialize(LOADS(S offset)selected SELECTED current world GOOD);
        rewrite Nat2Z.inj_succ in LOADS;replace(index+Z.succ(Z.of_nat offset))with(index+1+Z.of_nat offset)in LOADS by lia;exact LOADS))
      as(final_parameters &TAIL &FINAL_BYTES &FINAL_POSITION &FINAL_VALID).
    exists final_parameters;split;[eapply gateway_integer_segments_append;eassumption|].
    split;[exact FINAL_BYTES|]. split;[exact FINAL_POSITION|].
    cbn;rewrite andb_assoc;exact FINAL_VALID.
Qed.
