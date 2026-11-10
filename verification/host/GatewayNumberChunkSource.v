(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual nine-digit loop retains all operand source places
   and computes the checked decimal chunk before its real SDK constructor call. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayNumber GatewayIntegerScan GatewaySourceSegments GatewayFramedRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_chunk_parameters_retained(before after:temp_env):Prop:=
  forall identifier,identifier<>_offset->identifier<>_chunk->identifier<>_t'23->after!identifier=before!identifier.
Lemma gateway_chunk_parameters_refl parameters:gateway_chunk_parameters_retained parameters parameters.
Proof. unfold gateway_chunk_parameters_retained;intros;reflexivity. Qed.
Lemma gateway_chunk_parameters_trans first second third:
  gateway_chunk_parameters_retained first second->gateway_chunk_parameters_retained second third->gateway_chunk_parameters_retained first third.
Proof. unfold gateway_chunk_parameters_retained;intros FIRST SECOND identifier A B C;rewrite SECOND,FIRST;auto. Qed.
Lemma gateway_chunk_parameters_next parameters accumulator offset digit:
  gateway_chunk_parameters_retained parameters(gateway_number_chunk_next parameters accumulator offset digit).
Proof. unfold gateway_chunk_parameters_retained;intros identifier A B C;unfold gateway_number_chunk_next;repeat rewrite PTree.gso by congruence;reflexivity. Qed.

Theorem gateway_number_chunk_iteration_segment {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)environment parameters memory continuation object ofs index width offset accumulator digit:
  gateway_ambient_closed backend property->0<=index<=65536->0<=offset<width->width<=9->48<=digit<=57->
  gateway_number_chunk_state parameters object ofs index width offset accumulator->
  (forall memory current,property memory current->Mem.loadv Mint8signed memory(Vptr object(Ptrofs.add ofs(Ptrofs.repr(index+offset))))=Some(Vint(Int.repr digit)))->
  gateway_source_segment backend ge property
    (State f_host_json_number gateway_number_chunk_loop continuation environment parameters memory)
    (State f_host_json_number gateway_number_chunk_loop continuation environment(gateway_number_chunk_next parameters accumulator offset digit)memory)property.
Proof.
  intros CLOSED INDEX OFFSET WIDTH DIGIT[BYTES[POSITION[LIMIT[WITHIN ACCUMULATOR]]]]LOAD.
  set(loop_cont:=Kloop1 gateway_number_chunk_body gateway_number_chunk_increment continuation).
  set(after_guard:=Ssequence(Sset _t'23 gateway_number_chunk_read)(Sset _chunk gateway_chunk_expression)).
  eapply gateway_segment_same with(next:=State f_host_json_number gateway_number_chunk_body loop_cont environment parameters memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_loop|].
  eapply gateway_segment_same with(next:=State f_host_json_number(Sifthenelse gateway_number_offset_test Sskip Sbreak)
    (Kseq after_guard loop_cont)environment parameters memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_segment_same with(next:=State f_host_json_number Sskip(Kseq after_guard loop_cont)environment parameters memory).
  - exact CLOSED.
  - cbn;tauto.
  - intros;eapply certified_if_edge with(b:=true).
    + pose proof(gateway_number_offset_guard ge environment parameters memory0 offset width ltac:(lia)ltac:(lia)WITHIN LIMIT)as TEST.
      rewrite zlt_true in TEST by lia;exact TEST.
    + reflexivity.
  - eapply gateway_segment_same with(next:=State f_host_json_number after_guard loop_cont environment parameters memory);
      [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
    eapply gateway_segment_same with(next:=State f_host_json_number(Sset _t'23 gateway_number_chunk_read)
      (Kseq(Sset _chunk gateway_chunk_expression)loop_cont)environment parameters memory);
      [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
    set(with_digit:=PTree.set _t'23(Vint(Int.repr digit))parameters).
    eapply gateway_segment_same with(next:=State f_host_json_number Sskip(Kseq(Sset _chunk gateway_chunk_expression)loop_cont)environment with_digit memory).
    + exact CLOSED.
    + cbn;tauto.
    + intros;apply certified_set_edge;eapply gateway_actual_chunk_character;try eassumption;try lia;eapply LOAD;eassumption.
    + eapply gateway_segment_same with(next:=State f_host_json_number(Sset _chunk gateway_chunk_expression)loop_cont environment with_digit memory);
        [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
      set(with_chunk:=PTree.set _chunk(Vlong(Int64.repr(10*accumulator+digit-48)))with_digit).
      eapply gateway_segment_same with(next:=State f_host_json_number Sskip loop_cont environment with_chunk memory).
      * exact CLOSED.
      * cbn;tauto.
      * intros;apply gateway_actual_chunk_step with(accumulator:=accumulator)(digit:=digit).
        -- exact DIGIT.
        -- unfold with_digit;rewrite PTree.gso by discriminate;exact ACCUMULATOR.
        -- unfold with_digit;apply PTree.gss.
      * eapply gateway_segment_same with(next:=State f_host_json_number gateway_number_chunk_increment
          (Kloop2 gateway_number_chunk_body gateway_number_chunk_increment continuation)environment with_chunk memory);
          [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_loop1|].
        eapply gateway_segment_same with(next:=State f_host_json_number Sskip
          (Kloop2 gateway_number_chunk_body gateway_number_chunk_increment continuation)environment
          (gateway_number_chunk_next parameters accumulator offset digit)memory).
        -- exact CLOSED.
        -- cbn;tauto.
        -- intros;apply certified_set_edge;eapply binary_expression_value.
           ++ apply old_expression_value,value_temp;unfold with_chunk,with_digit;repeat rewrite PTree.gso by discriminate;exact WITHIN.
           ++ apply old_expression_value,value_int.
           ++ apply gateway_number_offset_increment.
        -- eapply gateway_segment_same with(next:=State f_host_json_number gateway_number_chunk_loop continuation environment
             (gateway_number_chunk_next parameters accumulator offset digit)memory);
             [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_loop2|apply gateway_segment_here].
Qed.

Theorem gateway_number_chunk_exit_segment {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)environment parameters memory continuation width:
  gateway_ambient_closed backend property->0<=width<=9->parameters!_width=Some(Vlong(Int64.repr width))->
  parameters!_offset=Some(Vlong(Int64.repr width))->
  gateway_source_segment backend ge property
    (State f_host_json_number gateway_number_chunk_loop continuation environment parameters memory)
    (State f_host_json_number Sskip continuation environment parameters memory)property.
Proof.
  intros CLOSED WIDTH LIMIT POSITION.
  set(loop_cont:=Kloop1 gateway_number_chunk_body gateway_number_chunk_increment continuation).
  set(after_guard:=Ssequence(Sset _t'23 gateway_number_chunk_read)(Sset _chunk gateway_chunk_expression)).
  eapply gateway_segment_same with(next:=State f_host_json_number gateway_number_chunk_body loop_cont environment parameters memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_loop|].
  eapply gateway_segment_same with(next:=State f_host_json_number(Sifthenelse gateway_number_offset_test Sskip Sbreak)
    (Kseq after_guard loop_cont)environment parameters memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_segment_same with(next:=State f_host_json_number Sbreak(Kseq after_guard loop_cont)environment parameters memory).
  - exact CLOSED.
  - cbn;tauto.
  - intros;eapply certified_if_edge with(b:=false).
    + pose proof(gateway_number_offset_guard ge environment parameters memory0 width width WIDTH WIDTH POSITION LIMIT)as TEST.
      rewrite zlt_false in TEST by lia;exact TEST.
    + reflexivity.
  - eapply gateway_segment_same with(next:=State f_host_json_number Sbreak loop_cont environment parameters memory);
      [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_break_seq|].
    eapply gateway_segment_same with(next:=State f_host_json_number Sskip continuation environment parameters memory);
      [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_break_loop1|apply gateway_segment_here].
Qed.

Theorem gateway_number_chunk_segment {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)environment continuation object ofs index width memory:
  gateway_ambient_closed backend property->0<=index<=65536->0<=width<=9->
  forall bytes parameters offset accumulator,
    Forall(fun byte=>48<=Byte.unsigned byte<=57)bytes->0<=offset->offset+Z.of_nat(length bytes)=width->
    gateway_number_chunk_state parameters object ofs index width offset accumulator->
    (forall position byte,nth_error bytes position=Some byte->forall memory current,property memory current->
      Mem.loadv Mint8signed memory(Vptr object(Ptrofs.add ofs(Ptrofs.repr(index+offset+Z.of_nat position))))=Some(Vint(Int.repr(Byte.unsigned byte))))->
  exists final,
    gateway_source_segment backend ge property
      (State f_host_json_number gateway_number_chunk_loop continuation environment parameters memory)
      (State f_host_json_number Sskip continuation environment final memory)property /\
    gateway_number_chunk_state final object ofs index width width(gateway_number_fold accumulator bytes) /\
    gateway_chunk_parameters_retained parameters final.
Proof.
  intros CLOSED INDEX WIDTH bytes;induction bytes as[|byte rest IH];intros parameters offset accumulator DIGITS OFFSET COUNT STATE LOADS.
  - cbn in COUNT;rewrite Z.add_0_r in COUNT;subst offset;exists parameters;split.
    + eapply gateway_number_chunk_exit_segment;[exact CLOSED|exact WIDTH|exact(proj1(proj2(proj2 STATE)))|exact(proj1(proj2(proj2(proj2 STATE))))].
    + split;[exact STATE|apply gateway_chunk_parameters_refl].
  - apply Forall_cons_iff in DIGITS;destruct DIGITS as[DIGIT REST].
    assert(LESS:offset<width)by(change(offset+Z.of_nat(S(length rest))=width)in COUNT;rewrite Nat2Z.inj_succ in COUNT;lia).
    pose proof(gateway_number_chunk_iteration_segment backend ge property environment parameters memory continuation object ofs index width offset accumulator(Byte.unsigned byte)
      CLOSED INDEX(conj OFFSET LESS)(proj2 WIDTH)DIGIT STATE
      ltac:(intros current world GOOD;specialize(LOADS 0%nat byte eq_refl current world GOOD);cbn in LOADS;rewrite Z.add_0_r in LOADS;exact LOADS))as STEP.
    pose proof(gateway_number_chunk_next_state parameters object ofs index width offset accumulator(Byte.unsigned byte)STATE)as NEXT_STATE.
    destruct(IH(gateway_number_chunk_next parameters accumulator offset(Byte.unsigned byte))(offset+1)(10*accumulator+Byte.unsigned byte-48)
      REST ltac:(lia)ltac:(change(offset+Z.of_nat(S(length rest))=width)in COUNT;rewrite Nat2Z.inj_succ in COUNT;lia)NEXT_STATE
      ltac:(intros position character SELECTED current world GOOD;specialize(LOADS(S position)character SELECTED current world GOOD);
        rewrite Nat2Z.inj_succ in LOADS;replace(index+(offset+1)+Z.of_nat position)with(index+offset+Z.succ(Z.of_nat position))by lia;exact LOADS))
      as(final &TAIL &FINAL_STATE &RETAINED).
    exists final;split;[eapply GatewayIntegerScan.gateway_integer_segments_append;eassumption|].
    split;[exact FINAL_STATE|]. eapply gateway_chunk_parameters_trans;[apply gateway_chunk_parameters_next|exact RETAINED].
Qed.
