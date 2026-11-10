(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: Completed prefixes become actual readable retained bytes. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata.
From HostGateway Require Import GatewayMachine GatewayStreamInterface GatewayReadyInterface GatewayReadContext GatewayThreadRuntime
  GatewayBufferReference.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_prefix_readonly readonly data_block base written object position :Prop:=
  readonly object position \/gateway_data_region data_block base written object position.

Definition gateway_whole_data_separate(stream_block:Values.block)stream_offset(data_block:Values.block)base total :Prop:=
  stream_block<>data_block \/Ptrofs.unsigned base+total<=Ptrofs.unsigned stream_offset \/
    Ptrofs.unsigned stream_offset+48<=Ptrofs.unsigned base.

Lemma gateway_read_inputs_restrict memory stream_block stream_offset initial data_block offset amount large small :
  gateway_read_inputs memory stream_block stream_offset initial data_block offset amount large ->
  (forall object position,small object position->large object position) ->
  gateway_read_inputs memory stream_block stream_offset initial data_block offset amount small.
Proof.
  intros[CELLS SIZE STREAM_BOUND DATA_BOUND STREAM_PERM DATA_LIVE DATA_PERM SEPARATE
    READONLY_LIVE READONLY_READABLE READONLY_DATA READONLY_REMAINING READONLY_CANCEL]INCLUDED.
  constructor;try assumption.
  - intros object position HERE;apply READONLY_LIVE with(position:=position);apply INCLUDED;exact HERE.
  - intros object position HERE;apply READONLY_READABLE;apply INCLUDED;exact HERE.
  - intros position RANGE HERE;apply(READONLY_DATA position RANGE);apply INCLUDED;exact HERE.
  - intros position RANGE HERE;apply(READONLY_REMAINING position RANGE);apply INCLUDED;exact HERE.
  - intros position RANGE HERE;apply(READONLY_CANCEL position RANGE);apply INCLUDED;exact HERE.
Qed.

Lemma gateway_read_restrict_context {World}native_private stable_readonly discipline mode
    stream_block stream_offset initial data_block offset amount large small memory world :
  @gateway_read_context World native_private stable_readonly discipline mode stream_block stream_offset initial
    data_block offset amount large memory world ->
  (forall object position,small object position->large object position) ->
  gateway_read_context native_private stable_readonly discipline mode stream_block stream_offset initial
    data_block offset amount small memory world.
Proof.
  intros[SIDE[STREAM[DATA[IMMUTABLE INPUT]]]]INCLUDED.
  split;[exact SIDE|]. split;[exact STREAM|]. split;[exact DATA|]. split.
  - intros object position HERE;apply IMMUTABLE;apply INCLUDED;exact HERE.
  - eapply gateway_read_inputs_restrict;[exact INPUT|exact INCLUDED].
Qed.

Theorem gateway_read_inputs_prefix memory stream_block stream_offset initial data_block offset size readonly base
    written bytes :
  gateway_read_inputs memory stream_block stream_offset initial data_block offset size readonly ->
  0<=written ->Ptrofs.unsigned offset=Ptrofs.unsigned base+written ->
  gateway_whole_data_separate stream_block stream_offset data_block base(written+size) ->
  Mem.loadbytes memory data_block(Ptrofs.unsigned base)written=Some(inj_bytes bytes) ->
  gateway_read_inputs memory stream_block stream_offset initial data_block offset size
    (gateway_prefix_readonly readonly data_block base written).
Proof.
  intros INPUT WRITTEN OFFSET WHOLE LOAD.
  destruct INPUT as[CELLS SIZE STREAM_BOUND DATA_BOUND STREAM_PERM DATA_LIVE DATA_PERM SEPARATE
    READONLY_LIVE READONLY_READABLE READONLY_DATA READONLY_REMAINING READONLY_CANCEL].
  constructor;try assumption.
  - intros object position[HERE|[SAME RANGE]];
      [apply READONLY_LIVE with(position:=position);exact HERE|subst object;exact DATA_LIVE].
  - intros object position[HERE|[SAME RANGE]];
      [apply READONLY_READABLE;exact HERE|subst object;eapply Mem.loadbytes_range_perm;[exact LOAD|exact RANGE]].
  - intros position RANGE[HERE|[SAME PREFIX]];[exact(READONLY_DATA position RANGE HERE)|lia].
  - intros position RANGE[HERE|[SAME PREFIX]];[exact(READONLY_REMAINING position RANGE HERE)|].
    destruct WHOLE as[DIFFERENT|[BEFORE|AFTER]];[congruence|lia|lia].
  - intros position RANGE[HERE|[SAME PREFIX]];[exact(READONLY_CANCEL position RANGE HERE)|].
    destruct WHOLE as[DIFFERENT|[BEFORE|AFTER]];[congruence|lia|lia].
Qed.

Theorem gateway_read_prefix_context {World Event}(backend:gateway_backend World Event)io native_private stable_readonly
    discipline thread_errno(runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno)
    mode stream_block stream_offset initial data_block offset size readonly base written bytes memory world :
  gateway_read_context native_private stable_readonly discipline mode stream_block stream_offset initial
    data_block offset size readonly memory world ->
  0<=written ->Ptrofs.unsigned offset=Ptrofs.unsigned base+written ->
  gateway_whole_data_separate stream_block stream_offset data_block base(written+size) ->
  Mem.loadbytes memory data_block(Ptrofs.unsigned base)written=Some(inj_bytes bytes) ->
  gateway_read_context native_private stable_readonly discipline mode stream_block stream_offset initial
    data_block offset size(gateway_prefix_readonly readonly data_block base written)memory world.
Proof.
  intros[SIDE[STREAM[DATA[IMMUTABLE INPUT]]]]WRITTEN OFFSET WHOLE LOAD.
  split;[exact SIDE|]. split;[exact STREAM|]. split;[exact DATA|]. split.
  - intros object position[HERE|[SAME RANGE]];[apply IMMUTABLE;exact HERE|subst object].
    eapply gateway_thread_native_stable;[exact runtime|exact SIDE|exact DATA].
  - eapply gateway_read_inputs_prefix;[exact INPUT|exact WRITTEN|exact OFFSET|exact WHOLE|exact LOAD].
Qed.

Lemma gateway_loaded_prefix_append memory data_block base offset written count prefix bytes :
  0<=written ->0<=count ->Ptrofs.unsigned offset=Ptrofs.unsigned base+written ->
  Mem.loadbytes memory data_block(Ptrofs.unsigned base)written=Some(inj_bytes prefix) ->
  Mem.loadbytes memory data_block(Ptrofs.unsigned offset)count=Some(inj_bytes bytes) ->
  Mem.loadbytes memory data_block(Ptrofs.unsigned base)(written+count)=Some(inj_bytes(prefix++bytes)).
Proof.
  intros WRITTEN COUNT OFFSET PREFIX BYTES.
  rewrite OFFSET in BYTES;unfold inj_bytes;rewrite map_app.
  eapply Mem.loadbytes_concat;[exact PREFIX|exact BYTES|lia|lia].
Qed.

Lemma gateway_ready_total_data_permissions before after stream_block stream_offset initial data_block offset size readonly
    base written :
  gateway_read_inputs before stream_block stream_offset initial data_block offset size
    (gateway_prefix_readonly readonly data_block base written) ->
  0<=written ->Ptrofs.unsigned offset=Ptrofs.unsigned base+written ->
  Mem.unchanged_on(fun object position=>gateway_prefix_readonly readonly data_block base written object position \/
    gateway_data_region data_block offset size object position)before after ->
  gateway_native_permissions before after data_block base(written+size).
Proof.
  intros INPUT WRITTEN OFFSET FRAME position kind permission RANGE.
  apply(Mem.unchanged_on_perm _ _ _ FRAME data_block position kind permission);
    [|exact(gateway_read_data_live _ _ _ _ _ _ _ _ INPUT)].
  destruct(Z_lt_ge_dec position(Ptrofs.unsigned offset))as[PREFIX|TAIL].
  - left;right;split;[reflexivity|rewrite OFFSET in PREFIX;lia].
  - right;split;[reflexivity|rewrite OFFSET in*;lia].
Qed.

Lemma gateway_native_permissions_transitive before middle after object offset amount :
  gateway_native_permissions before middle object offset amount ->
  gateway_native_permissions middle after object offset amount ->
  gateway_native_permissions before after object offset amount.
Proof. intros FIRST SECOND position kind permission HERE;rewrite(FIRST position kind permission HERE);apply SECOND;exact HERE. Qed.

Lemma gateway_buffer_native_permissions readonly first second before after object offset amount :
  gateway_buffer_reference readonly first second before after ->(object=first \/object=second) ->
  gateway_native_permissions before after object offset amount.
Proof. intros[FRAME PERMISSIONS]HERE position kind permission RANGE;apply PERMISSIONS;exact HERE. Qed.
