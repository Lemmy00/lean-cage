(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The source installs the received value length in the real stream. *)
From Stdlib Require Import ZArith Lia.
From compcert Require Import Integers AST Values Memory.
From HostGateway Require Import GatewayMachine GatewayStreamInterface GatewayThreadRuntime GatewayReadContext GatewayReadCounterMemory
  GatewayResponseWord.
Open Scope Z_scope.

Definition gateway_response_budget(initial:gateway_stream_values)(remaining:int64):gateway_stream_values:={|
  stream_descriptor:=stream_descriptor initial;stream_control:=stream_control initial;
  stream_cancel_sent:=stream_cancel_sent initial;stream_cli:=stream_cli initial;stream_cancellation:=stream_cancellation initial;
  stream_remaining:=remaining;stream_nodes:=stream_nodes initial;stream_deadline:=stream_deadline initial|}.

Lemma gateway_response_budget_debit initial remaining:
  gateway_stream_debit initial(Int64.unsigned(stream_remaining initial)-Int64.unsigned remaining)=
    gateway_response_budget initial remaining.
Proof.
  unfold gateway_stream_debit,gateway_response_budget.
  replace(Int64.unsigned(stream_remaining initial)-(Int64.unsigned(stream_remaining initial)-Int64.unsigned remaining))
    with(Int64.unsigned remaining)by lia;rewrite Int64.repr_unsigned;reflexivity.
Qed.

Lemma gateway_response_budget_cells before after stream initial remaining:
  gateway_stream_memory before stream Ptrofs.zero initial->
  Mem.store Mint64 before stream 24(Vlong remaining)=Some after->
  gateway_stream_memory after stream Ptrofs.zero(gateway_response_budget initial remaining).
Proof.
  intros CELLS STORE;rewrite<-(gateway_response_budget_debit initial remaining).
  eapply gateway_read_counter_cells;[change(48<=18446744073709551616);lia|exact CELLS|].
  replace(Int64.unsigned(stream_remaining initial)-(Int64.unsigned(stream_remaining initial)-Int64.unsigned remaining))
    with(Int64.unsigned remaining)by lia;rewrite Int64.repr_unsigned;exact STORE.
Qed.

Theorem gateway_response_budget_store {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    stream response readonly initial bytes remaining before world after:
  gateway_response_context native stable discipline stream response readonly initial bytes before world->
  Mem.store Mint64 before stream 24(Vlong remaining)=Some after->
  gateway_response_context native stable discipline stream response readonly(gateway_response_budget initial remaining)bytes after world.
Proof.
  intros[[SIDE[STREAM[DATA[IMMUTABLE INPUT]]]]LOADED]STORE.
  assert(FRAME:Mem.unchanged_on(fun object position=>readonly object position\/object=response)before after).
  { eapply Mem.store_unchanged_on;[exact STORE|].
    intros position RANGE[READONLY|SAME].
    - eapply(gateway_read_readonly_remaining _ _ _ _ _ _ _ _ INPUT position);[cbn[size_chunk]in RANGE;exact RANGE|exact READONLY].
    - destruct(gateway_read_data_separate _ _ _ _ _ _ _ _ INPUT)as[DIFFERENT|[LOW|HIGH]];
        [congruence|change(24<=0)in LOW;lia|change(48<=0)in HIGH;lia]. }
  split.
  - split;[eapply gateway_thread_native_store;[exact runtime|exact SIDE|exact STREAM|exact STORE]|].
    split;[exact STREAM|]. split;[exact DATA|]. split;[exact IMMUTABLE|].
    destruct INPUT as[CELLS SIZE STREAM_BOUND DATA_BOUND STREAM_PERM DATA_LIVE DATA_PERM SEPARATE
      READONLY_LIVE READONLY_READABLE READONLY_DATA READONLY_REMAINING READONLY_CANCEL].
    constructor;try assumption.
    + apply gateway_response_budget_cells with(before:=before);assumption.
    + intros position RANGE;eapply Mem.perm_store_1;[exact STORE|apply STREAM_PERM;exact RANGE].
    + eapply Mem.store_valid_block_1;[exact STORE|exact DATA_LIVE].
    + intros position RANGE;eapply Mem.perm_store_1;[exact STORE|apply DATA_PERM;exact RANGE].
    + intros object position HERE;eapply Mem.store_valid_block_1;[exact STORE|apply READONLY_LIVE with(position:=position);exact HERE].
    + intros object position HERE;eapply Mem.perm_unchanged_on;[exact FRAME|left;exact HERE|apply READONLY_READABLE;exact HERE].
  - eapply Mem.loadbytes_unchanged_on;[exact FRAME| |exact LOADED];intros;right;reflexivity.
Qed.

Theorem gateway_response_budget_allocates before stream response readonly initial remaining:
  gateway_read_inputs before stream Ptrofs.zero initial response Ptrofs.zero 24 readonly->
  exists after,Mem.store Mint64 before stream 24(Vlong remaining)=Some after.
Proof.
  intro INPUT.
  destruct(Mem.valid_access_store before Mint64 stream 24(Vlong remaining)
    (gateway_read_counter_valid before stream Ptrofs.zero initial response Ptrofs.zero 24 readonly INPUT))as[after STORE].
  exists after;exact STORE.
Qed.
