(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: The actual successful read tail stores the exact remaining budget. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Globalenvs
  Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayStreamInterface GatewayStreamLayout GatewayStreamAccess
  GatewayStreamMemory GatewayReadContext GatewayReadGuard GatewayReadTransfer GatewayReadCounterMemory GatewayReadCounterRuntime
  GatewayThreadRuntime GatewayBufferReference GatewayPrefixContext GatewayFramedRuntime GatewayRuntimeTrace GatewayReadonly.
Import ListNotations.
Open Scope Z_scope.

Definition read_counter_sequence:=match read_after_transfer with Ssequence counter _=>counter|_=>Sskip end.
Definition read_success_return:=match read_after_transfer with Ssequence _ result=>result|_=>Sskip end.
Definition read_counter_load:=match read_counter_sequence with Ssequence load _=>load|_=>Sskip end.
Definition read_counter_store:=match read_counter_sequence with Ssequence _ store=>store|_=>Sskip end.
Definition read_counter_values stream data amount cached remaining:=
  PTree.set _t'2(Vlong remaining)(read_transfer_return_values stream data amount cached(Vint Int.zero)).

Lemma actual_read_counter_value ge temporaries memory amount remaining :
  0<=amount<=Int64.max_unsigned ->temporaries!_size=Some(Vlong(Int64.repr amount)) ->
  temporaries!_t'2=Some(Vlong remaining) ->
  expression_value ge empty_env temporaries memory
    (Ebinop Osub(Etempvar _t'2 tulong)(Etempvar _size tulong)tulong)
    (Vlong(Int64.repr(Int64.unsigned remaining-amount))).
Proof.
  intros AMOUNT SIZE COUNTER;apply old_expression_value;eapply value_binary.
  - apply value_temp;exact COUNTER.
  - apply value_temp;exact SIZE.
  - change(Some(Vlong(Int64.sub remaining(Int64.repr amount)))=
      Some(Vlong(Int64.repr(Int64.unsigned remaining-amount)))).
    unfold Int64.sub;rewrite Int64.unsigned_repr by exact AMOUNT;reflexivity.
Qed.

Section CounterSource.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
  (native_private:World->block->Prop)(stable_readonly:World->block->Z->Prop)
  (discipline:option val->mem->World->Prop)(thread_errno:World->int).
Context(runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).
Variable ge:Clight.genv.
Variables stream_block data_block:Values.block.
Variables stream_offset data_offset:ptrofs.
Variable initial:gateway_stream_values.
Variable amount:Z.
Variable readonly:Values.block->Z->Prop.
Variable bytes:list Byte.int.
Variable reference:mem.
Variable owner:World.
Variable cached:int64.
Hypothesis LAYOUT:stream_member_layout ge _remaining 24.
Local Definition counter_context snapshot:=gateway_prefix_context native_private stable_readonly discipline
  stream_block data_block stream_offset data_offset snapshot amount readonly reference owner None data_offset amount bytes.
Local Lemma counter_ambient snapshot:gateway_ambient_closed backend(counter_context snapshot).
Proof. apply gateway_prefix_context_ambient with(io:=io)(thread_errno:=thread_errno);exact runtime. Qed.

Local Ltac counter_same target:=
  eapply gateway_runtime_same with(next:=target);[apply counter_ambient|cbn;tauto|intros available current READY|].

Theorem actual_read_counter_script memory :
  gateway_runtime_path backend ge(counter_context initial)
    (Returnstate(Vint Int.zero)(read_transfer_cont(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount cached)memory)
    (Vint Int.zero)(counter_context(gateway_stream_debit initial amount)).
Proof.
  counter_same(State f_host_read Sskip(Kseq read_transfer_test(Kseq read_after_transfer Kstop))empty_env
    (read_transfer_return_values(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount cached(Vint Int.zero))memory).
  { apply unchanged_store_edge,edge_returnstate. }
  counter_same(State f_host_read read_transfer_test(Kseq read_after_transfer Kstop)empty_env
    (read_transfer_return_values(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount cached(Vint Int.zero))memory).
  { apply unchanged_store_edge,edge_skip_seq. }
  counter_same(State f_host_read Sskip(Kseq read_after_transfer Kstop)empty_env
    (read_transfer_return_values(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount cached(Vint Int.zero))memory).
  { apply certified_if_edge with(v:=Vint Int.zero)(b:=false);
      [apply old_expression_value,value_temp;apply PTree.gss|reflexivity]. }
  counter_same(State f_host_read read_after_transfer Kstop empty_env
    (read_transfer_return_values(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount cached(Vint Int.zero))memory).
  { apply unchanged_store_edge,edge_skip_seq. }
  counter_same(State f_host_read read_counter_sequence(Kseq read_success_return Kstop)empty_env
    (read_transfer_return_values(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount cached(Vint Int.zero))memory).
  { apply unchanged_store_edge,edge_seq. }
  counter_same(State f_host_read read_counter_load(Kseq read_counter_store(Kseq read_success_return Kstop))empty_env
    (read_transfer_return_values(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount cached(Vint Int.zero))memory).
  { apply unchanged_store_edge,edge_seq. }
  counter_same(State f_host_read Sskip(Kseq read_counter_store(Kseq read_success_return Kstop))empty_env
    (read_counter_values(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount cached(stream_remaining initial))memory).
  { apply certified_set_edge.
    eapply actual_stream_member_read with(block:=stream_block)(offset:=stream_offset)(delta:=24)(chunk:=Mint64).
    - reflexivity.
    - exact LAYOUT.
    - reflexivity.
    - exact(proj1(proj2(proj2(proj2(proj2(proj2
        (gateway_read_stream_cells _ _ _ _ _ _ _ _(proj2(proj2(proj2(proj2(proj1(proj1 READY))))))))))))).
  }
  counter_same(State f_host_read read_counter_store(Kseq read_success_return Kstop)empty_env
    (read_counter_values(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount cached(stream_remaining initial))memory).
  { apply unchanged_store_edge,edge_skip_seq. }
  eapply gateway_runtime_next with
    (next:=State f_host_read Sskip(Kseq read_success_return Kstop)empty_env
      (read_counter_values(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount cached(stream_remaining initial))memory)
    (middle:=counter_context(gateway_stream_debit initial amount)).
  - apply counter_ambient.
  - cbn;tauto.
  - intros before world[[CONTEXT[BUFFER NATIVE]]LOAD].
    pose proof(proj2(proj2(proj2(proj2 CONTEXT))))as INPUT.
    destruct(gateway_read_counter_allocate before stream_block stream_offset initial data_block data_offset amount readonly INPUT)
      as[after STORE].
    exists after;split.
    + eapply actual_stream_member_store with(delta:=24)(chunk:=Mint64)
        (value:=Vlong(Int64.repr(Int64.unsigned(stream_remaining initial)-amount)))
        (converted:=Vlong(Int64.repr(Int64.unsigned(stream_remaining initial)-amount))).
      * reflexivity.
      * exact LAYOUT.
      * reflexivity.
      * apply actual_read_counter_value with(amount:=amount)(remaining:=stream_remaining initial);
          [exact(gateway_read_amount _ _ _ _ _ _ _ _ INPUT)|reflexivity|reflexivity].
      * reflexivity.
      * unfold Mem.storev,gateway_stream_slot.
        rewrite(gateway_stream_slot_unsigned stream_offset 24 ltac:(lia)
          (gateway_read_stream_bounds _ _ _ _ _ _ _ _ INPUT)).
        destruct(zle(Ptrofs.unsigned stream_offset+24+size_chunk Mint64)Ptrofs.modulus);[exact STORE|].
        pose proof(gateway_read_stream_bounds _ _ _ _ _ _ _ _ INPUT);cbn[size_chunk]in*;lia.
    + destruct(gateway_read_counter_context backend io native_private stable_readonly discipline thread_errno runtime
        before world after stream_block stream_offset initial data_block data_offset amount readonly CONTEXT STORE)
        as[AFTER[COUNTER_BUFFER COUNTER_NATIVE]].
      split.
      * split;[exact AFTER|]. split.
        -- eapply gateway_buffer_reference_transitive;[exact BUFFER|exact COUNTER_BUFFER].
        -- eapply gateway_native_reference_transitive;[exact NATIVE|exact COUNTER_NATIVE].
      * eapply Mem.loadbytes_unchanged_on;
          [eapply gateway_read_counter_retained;[exact INPUT|exact STORE]| |exact LOAD].
        intros position RANGE;right;split;[reflexivity|exact RANGE].
  - counter_same(State f_host_read read_success_return Kstop empty_env
      (read_counter_values(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount cached(stream_remaining initial))memory).
    { apply unchanged_store_edge,edge_skip_seq. }
    counter_same(Returnstate(Vint Int.zero)Kstop memory).
    { apply unchanged_store_edge;eapply edge_return with(v:=Vint Int.zero);[constructor|reflexivity]. }
    constructor;[apply counter_ambient|auto].
Qed.
End CounterSource.
