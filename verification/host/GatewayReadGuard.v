(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: A successful native read passed the actual remaining-length
   guard. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs
  Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayPure GatewayFrames
  GatewayInstructions GatewayPoints GatewayCalls GatewayStreamInterface GatewayStreamLayout GatewayStreamAccess
  GatewayStreamMemory GatewayCallPath.
Import ListNotations.
Open Scope Z_scope.

Definition read_parameters stream data amount:=
  PTree.set _size(Vlong(Int64.repr amount))(PTree.set _data data
    (PTree.set _stream stream(create_undef_temps(fn_temps f_host_read)))).
Definition read_guard:=match fn_body f_host_read with Ssequence guard _=>guard|_=>Sskip end.
Definition read_tail:=match fn_body f_host_read with Ssequence _ tail=>tail|_=>Sskip end.
Definition read_load:=match read_guard with Ssequence load _=>load|_=>Sskip end.
Definition read_test:=match read_guard with Ssequence _ test=>test|_=>Sskip end.
Definition read_error:=match read_test with Sifthenelse _ error _=>error|_=>Sskip end.
Definition read_transfer_sequence:=match read_tail with Ssequence first _=>first|_=>Sskip end.
Definition read_after_transfer:=match read_tail with Ssequence _ rest=>rest|_=>Sskip end.
Definition read_transfer_call:=match read_transfer_sequence with Ssequence call _=>call|_=>Sskip end.
Definition read_transfer_test:=match read_transfer_sequence with Ssequence _ test=>test|_=>Sskip end.
Definition read_guard_values stream data amount remaining:=
  PTree.set _t'3(Vlong remaining)(read_parameters stream data amount).
Definition read_transfer_cont stream data amount remaining:=
  Kcall(Some _t'1)f_host_read empty_env(read_guard_values stream data amount remaining)
    (Kseq read_transfer_test(Kseq read_after_transfer Kstop)).

Lemma read_source_shape:fn_body f_host_read=Ssequence read_guard read_tail /\
  read_guard=Ssequence read_load read_test /\
  read_tail=Ssequence read_transfer_sequence read_after_transfer /\
  read_transfer_sequence=Ssequence read_transfer_call read_transfer_test.
Proof. repeat split;reflexivity. Qed.

Lemma actual_read_guard_comparison ge environment temporaries memory amount remaining :
  0<=amount<=Int64.max_unsigned ->temporaries!_size=Some(Vlong(Int64.repr amount)) ->
  temporaries!_t'3=Some(Vlong remaining) ->
  expression_value ge environment temporaries memory
    (Ebinop Ogt(Etempvar _size tulong)(Etempvar _t'3 tulong)tint)
    (Vint(if zlt(Int64.unsigned remaining)amount then Int.one else Int.zero)).
Proof.
  intros BOUND SIZE REMAINING;apply old_expression_value;eapply value_binary.
  - apply value_temp;exact SIZE.
  - apply value_temp;exact REMAINING.
  - change(Some(Val.of_bool(Int64.ltu remaining(Int64.repr amount)))=
      Some(Vint(if zlt(Int64.unsigned remaining)amount then Int.one else Int.zero))).
    unfold Int64.ltu;rewrite(Int64.unsigned_repr amount)by exact BOUND.
    destruct(zlt(Int64.unsigned remaining)amount);reflexivity.
Qed.

Lemma actual_read_transfer_call (ge:Clight.genv) stream_block stream_offset data_block data_offset
    amount remaining memory symbol :
  Genv.find_symbol ge _host_transfer=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some(Internal f_host_transfer) ->
  store_edge ge
    (State f_host_read read_transfer_call(Kseq read_transfer_test(Kseq read_after_transfer Kstop))empty_env
      (read_guard_values(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount remaining)memory)
    (Callstate(Internal f_host_transfer)
      [Vptr stream_block stream_offset;Vptr data_block data_offset;Vlong(Int64.repr amount);Vint Int.zero]
      (read_transfer_cont(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount remaining)memory).
Proof.
  intros SYMBOL FUNCTION.
  eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
  - eapply cons_argument_values with(v:=Vptr stream_block stream_offset).
    + apply old_expression_value;apply value_temp;reflexivity.
    + reflexivity.
    + eapply cons_argument_values with(v:=Vptr data_block data_offset).
      * apply old_expression_value;apply value_temp;reflexivity.
      * reflexivity.
      * eapply cons_argument_values with(v:=Vlong(Int64.repr amount)).
        -- apply old_expression_value;apply value_temp;reflexivity.
        -- reflexivity.
        -- eapply cons_argument_values with(v:=Vint Int.zero).
           ++ apply old_expression_value;constructor.
           ++ reflexivity.
           ++ apply no_argument_values.
  - cbn;exact FUNCTION.
  - reflexivity.
Qed.

Lemma actual_read_guard_transfer_path (ge:Clight.genv) stream_block stream_offset data_block data_offset
    amount remaining memory symbol :
  0<=amount<=Int64.max_unsigned ->amount<=Int64.unsigned remaining ->
  Genv.find_symbol ge _host_transfer=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some(Internal f_host_transfer) ->
  gateway_retained_call_path ge(Internal f_host_transfer)
    [Vptr stream_block stream_offset;Vptr data_block data_offset;Vlong(Int64.repr amount);Vint Int.zero]
    (read_transfer_cont(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount remaining)
    (State f_host_read read_test(Kseq read_tail Kstop)empty_env
      (read_guard_values(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount remaining)memory).
Proof.
  intros AMOUNT FITS SYMBOL FUNCTION.
  eapply gateway_retained_next with(next:=State f_host_read Sskip(Kseq read_tail Kstop)empty_env
    (read_guard_values(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount remaining)memory).
  - cbn;tauto.
  - intro another;apply certified_if_edge with(v:=Vint Int.zero)(b:=false).
    + pose proof(actual_read_guard_comparison ge empty_env
        (read_guard_values(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount remaining)
        another amount remaining AMOUNT eq_refl eq_refl)as VALUE.
      destruct(zlt(Int64.unsigned remaining)amount);[lia|exact VALUE].
    + reflexivity.
  - eapply gateway_retained_next with(next:=State f_host_read read_tail Kstop empty_env
      (read_guard_values(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount remaining)memory).
    + cbn;tauto.
    + intro another;apply unchanged_store_edge,edge_skip_seq.
    + eapply gateway_retained_next with(next:=State f_host_read read_transfer_sequence
        (Kseq read_after_transfer Kstop)empty_env
        (read_guard_values(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount remaining)memory).
      * cbn;tauto.
      * intro another;apply unchanged_store_edge,edge_seq.
      * eapply gateway_retained_next with(next:=State f_host_read read_transfer_call
          (Kseq read_transfer_test(Kseq read_after_transfer Kstop))empty_env
          (read_guard_values(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount remaining)memory).
        -- cbn;tauto.
        -- intro another;apply unchanged_store_edge,edge_seq.
        -- eapply gateway_retained_next with(next:=Callstate(Internal f_host_transfer)
            [Vptr stream_block stream_offset;Vptr data_block data_offset;Vlong(Int64.repr amount);Vint Int.zero]
            (read_transfer_cont(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount remaining)memory).
           ++ cbn;tauto.
           ++ intro another;apply actual_read_transfer_call with(symbol:=symbol);assumption.
           ++ constructor.
Qed.

Lemma actual_read_body_guard_path (ge:Clight.genv) stream_block stream_offset data amount initial before :
  stream_member_layout ge _remaining 24 ->Ptrofs.unsigned stream_offset+48<=Ptrofs.modulus ->
  gateway_point_path ge(gateway_stream_region stream_block stream_offset)
    (State f_host_read read_test(Kseq read_tail Kstop)empty_env
      (read_guard_values(Vptr stream_block stream_offset)data amount(stream_remaining initial))before)
    (fun memory=>gateway_stream_memory memory stream_block stream_offset initial)
    (fun memory=>gateway_stream_memory memory stream_block stream_offset initial)
    (State f_host_read(fn_body f_host_read)Kstop empty_env
      (read_parameters(Vptr stream_block stream_offset)data amount)before).
Proof.
  intros LAYOUT BOUND.
  pose proof(gateway_stream_memory_closed stream_block stream_offset initial BOUND)as CLOSED.
  eapply gateway_point_same with(next:=State f_host_read read_guard(Kseq read_tail Kstop)empty_env
    (read_parameters(Vptr stream_block stream_offset)data amount)before).
  - exact CLOSED.
  - cbn;tauto.
  - intros memory CELLS;apply unchanged_store_edge,edge_seq.
  - eapply gateway_point_same with(next:=State f_host_read read_load(Kseq read_test(Kseq read_tail Kstop))empty_env
      (read_parameters(Vptr stream_block stream_offset)data amount)before).
    + exact CLOSED.
    + cbn;tauto.
    + intros memory CELLS;apply unchanged_store_edge,edge_seq.
    + eapply gateway_point_same with(next:=State f_host_read Sskip(Kseq read_test(Kseq read_tail Kstop))empty_env
        (read_guard_values(Vptr stream_block stream_offset)data amount(stream_remaining initial))before).
      * exact CLOSED.
      * cbn;tauto.
      * intros memory CELLS;apply certified_set_edge.
        eapply actual_stream_member_read with(block:=stream_block)(offset:=stream_offset)(delta:=24)(chunk:=Mint64).
        -- reflexivity.
        -- exact LAYOUT.
        -- reflexivity.
        -- exact(proj1(proj2(proj2(proj2(proj2(proj2 CELLS)))))).
      * eapply gateway_point_same with(next:=State f_host_read read_test(Kseq read_tail Kstop)empty_env
          (read_guard_values(Vptr stream_block stream_offset)data amount(stream_remaining initial))before).
        -- exact CLOSED.
        -- cbn;tauto.
        -- intros memory CELLS;apply unchanged_store_edge,edge_skip_seq.
        -- change(gateway_point_path ge(gateway_stream_region stream_block stream_offset)
            (State f_host_read read_test(Kseq read_tail Kstop)empty_env
              (read_guard_values(Vptr stream_block stream_offset)data amount(stream_remaining initial))before)
            (fun memory=>gateway_stream_memory memory stream_block stream_offset initial)
            (fun memory=>gateway_stream_memory memory stream_block stream_offset initial)
            (gateway_replace_memory(State f_host_read read_test(Kseq read_tail Kstop)empty_env
              (read_guard_values(Vptr stream_block stream_offset)data amount(stream_remaining initial))before)before)).
           constructor;[exact CLOSED|auto].
Qed.

Lemma actual_read_excess_test_returns_failure {World Event}(backend:gateway_backend World Event)ge
    stream data amount remaining before world events returned after next :
  0<=amount<=Int64.max_unsigned ->Int64.unsigned remaining<amount ->
  gateway_steps backend ge
    (gateway_live(State f_host_read read_test(Kseq read_tail Kstop)empty_env
      (read_guard_values stream data amount remaining)before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->returned=Vint(Int.neg Int.one).
Proof.
  intros AMOUNT EXCESS RUN.
  destruct(gateway_uniform_instruction_next backend ge f_host_read read_test(Kseq read_tail Kstop)empty_env
    (read_guard_values stream data amount remaining)before world events returned after next
    (State f_host_read read_error(Kseq read_tail Kstop)empty_env(read_guard_values stream data amount remaining)before)
    ltac:(cbn;tauto)ltac:(intro memory;apply certified_if_edge with(v:=Vint Int.one)(b:=true);
      [pose proof(actual_read_guard_comparison ge empty_env(read_guard_values stream data amount remaining)
        memory amount remaining AMOUNT eq_refl eq_refl)as VALUE;
       destruct(zlt(Int64.unsigned remaining)amount);[exact VALUE|lia]|reflexivity])RUN)
    as[prefix[suffix[memory[test_world[EVENTS[AMBIENT[PREFIX REST]]]]]]].
  cbn[gateway_replace_memory]in REST.
  eapply gateway_error_sequence_returns_failure with(function:=f_host_read)(continuation:=Kseq read_tail Kstop);
    [reflexivity|reflexivity|exact REST].
Qed.

Theorem actual_successful_read_body_passed_guard {World Event}(backend:gateway_backend World Event)ge
    stream_block stream_offset data amount initial before world events after next active
    (private:gateway_private_contract backend(gateway_stream_region stream_block stream_offset)active) :
  active world ->gateway_stream_memory before stream_block stream_offset initial ->
  stream_member_layout ge _remaining 24 ->Ptrofs.unsigned stream_offset+48<=Ptrofs.modulus ->
  0<=amount<=Int64.max_unsigned ->
  gateway_steps backend ge
    (gateway_live(State f_host_read(fn_body f_host_read)Kstop empty_env
      (read_parameters(Vptr stream_block stream_offset)data amount)before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next) ->
  amount<=Int64.unsigned(stream_remaining initial).
Proof.
  intros ACTIVE CELLS LAYOUT BOUND AMOUNT RUN.
  destruct(gateway_point_path_cut backend ge(gateway_stream_region stream_block stream_offset)active private
    (State f_host_read read_test(Kseq read_tail Kstop)empty_env
      (read_guard_values(Vptr stream_block stream_offset)data amount(stream_remaining initial))before)
    (fun memory=>gateway_stream_memory memory stream_block stream_offset initial)
    (fun memory=>gateway_stream_memory memory stream_block stream_offset initial)
    (State f_host_read(fn_body f_host_read)Kstop empty_env
      (read_parameters(Vptr stream_block stream_offset)data amount)before)
    world events(Vint Int.zero)after next ACTIVE CELLS
    (actual_read_body_guard_path ge stream_block stream_offset data amount initial before LAYOUT BOUND)RUN)
    as[prefix[suffix[memory[test_world[EVENTS[PREFIX[CELLS1[ALIVE REST]]]]]]]].
  cbn[gateway_replace_memory]in REST.
  destruct(Z_le_gt_dec amount(Int64.unsigned(stream_remaining initial)))as[FITS|EXCESS];[exact FITS|].
  pose proof(actual_read_excess_test_returns_failure backend ge(Vptr stream_block stream_offset)data amount
    (stream_remaining initial)memory test_world suffix(Vint Int.zero)after next AMOUNT ltac:(lia)REST)as BAD.
  discriminate BAD.
Qed.

Theorem actual_successful_read_body_calls_transfer {World Event}(backend:gateway_backend World Event)ge
    stream_block stream_offset data_block data_offset amount initial before world events after next active
    (private:gateway_private_contract backend(gateway_stream_region stream_block stream_offset)active)symbol :
  active world ->gateway_stream_memory before stream_block stream_offset initial ->
  stream_member_layout ge _remaining 24 ->Ptrofs.unsigned stream_offset+48<=Ptrofs.modulus ->
  0<=amount<=Int64.max_unsigned ->Genv.find_symbol ge _host_transfer=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some(Internal f_host_transfer) ->
  gateway_steps backend ge
    (gateway_live(State f_host_read(fn_body f_host_read)Kstop empty_env
      (read_parameters(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount)before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next) ->
  amount<=Int64.unsigned(stream_remaining initial) /\
  exists prefix suffix called_memory called_world,
    events=prefix++suffix /\
    gateway_steps backend ge
      (gateway_live(State f_host_read(fn_body f_host_read)Kstop empty_env
        (read_parameters(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount)before)world)prefix
      (gateway_live(Callstate(Internal f_host_transfer)
        [Vptr stream_block stream_offset;Vptr data_block data_offset;Vlong(Int64.repr amount);Vint Int.zero]
        (read_transfer_cont(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount
          (stream_remaining initial))called_memory)called_world) /\
    gateway_stream_memory called_memory stream_block stream_offset initial /\active called_world /\
    gateway_steps backend ge
      (gateway_live(Callstate(Internal f_host_transfer)
        [Vptr stream_block stream_offset;Vptr data_block data_offset;Vlong(Int64.repr amount);Vint Int.zero]
        (read_transfer_cont(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount
          (stream_remaining initial))called_memory)called_world)suffix
      (gateway_live(Returnstate(Vint Int.zero)Kstop after)next).
Proof.
  intros ACTIVE CELLS LAYOUT BOUND AMOUNT SYMBOL FUNCTION RUN.
  destruct(gateway_point_path_cut backend ge(gateway_stream_region stream_block stream_offset)active private
    (State f_host_read read_test(Kseq read_tail Kstop)empty_env
      (read_guard_values(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount
        (stream_remaining initial))before)
    (fun memory=>gateway_stream_memory memory stream_block stream_offset initial)
    (fun memory=>gateway_stream_memory memory stream_block stream_offset initial)
    (State f_host_read(fn_body f_host_read)Kstop empty_env
      (read_parameters(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount)before)
    world events(Vint Int.zero)after next ACTIVE CELLS
    (actual_read_body_guard_path ge stream_block stream_offset(Vptr data_block data_offset)amount initial
      before LAYOUT BOUND)RUN)
    as[prefix1[suffix1[memory1[world1[EVENTS1[PREFIX1[CELLS1[ACTIVE1 REST1]]]]]]]].
  cbn[gateway_replace_memory]in REST1.
  assert(FITS:amount<=Int64.unsigned(stream_remaining initial)).
  { destruct(Z_le_gt_dec amount(Int64.unsigned(stream_remaining initial)))as[FITS|EXCESS];[exact FITS|].
    pose proof(actual_read_excess_test_returns_failure backend ge(Vptr stream_block stream_offset)
      (Vptr data_block data_offset)amount(stream_remaining initial)memory1 world1 suffix1(Vint Int.zero)
      after next AMOUNT ltac:(lia)REST1)as BAD;discriminate BAD. }
  split;[exact FITS|].
  assert(SCRIPT:gateway_call_path ge(gateway_stream_region stream_block stream_offset)(Internal f_host_transfer)
    [Vptr stream_block stream_offset;Vptr data_block data_offset;Vlong(Int64.repr amount);Vint Int.zero]
    (read_transfer_cont(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount(stream_remaining initial))
    (fun memory=>gateway_stream_memory memory stream_block stream_offset initial)
    (fun memory=>gateway_stream_memory memory stream_block stream_offset initial)
    (State f_host_read read_test(Kseq read_tail Kstop)empty_env
      (read_guard_values(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount
        (stream_remaining initial))memory1)).
  { apply gateway_retained_framed.
    - apply actual_read_guard_transfer_path with(symbol:=symbol);assumption.
    - apply gateway_stream_memory_closed;exact BOUND. }
  destruct(gateway_call_path_cut backend ge(gateway_stream_region stream_block stream_offset)active private
    (Internal f_host_transfer)
    [Vptr stream_block stream_offset;Vptr data_block data_offset;Vlong(Int64.repr amount);Vint Int.zero]
    (read_transfer_cont(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount(stream_remaining initial))
    (fun memory=>gateway_stream_memory memory stream_block stream_offset initial)
    (fun memory=>gateway_stream_memory memory stream_block stream_offset initial)
    (State f_host_read read_test(Kseq read_tail Kstop)empty_env
      (read_guard_values(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount
        (stream_remaining initial))memory1)world1 suffix1(Vint Int.zero)after next
    ACTIVE1 CELLS1 SCRIPT REST1)
    as[prefix2[suffix2[memory2[world2[EVENTS2[PREFIX2[CELLS2[ACTIVE2 REST2]]]]]]]].
  exists(prefix1++prefix2),suffix2,memory2,world2.
  split;[rewrite EVENTS1,EVENTS2,app_assoc;reflexivity|]. split.
  - eapply gateway_steps_append;[exact PREFIX1|exact PREFIX2].
  - auto.
Qed.
