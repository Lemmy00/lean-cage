(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Retain all real stable capabilities without separating overlapping owners. *)
From Stdlib Require Import ZArith.
From compcert Require Import Coqlib Integers AST Values Memory.
From HostGateway Require Import GatewayMachine GatewayStreamInterface GatewayReadContext GatewayThreadRuntime.
Open Scope Z_scope.

Definition gateway_stable_readonly {World}(stable_readonly:World->block->Z->Prop)
    before world stream_block data_block readonly object position :Prop:=
  readonly object position \/Mem.perm before object position Cur Readable /\stable_readonly world object position /\
    object<>stream_block /\object<>data_block.

Lemma gateway_read_stable_inputs {World}(stable_readonly:World->block->Z->Prop)
    before world stream_block stream_offset initial data_block data_offset amount readonly :
  gateway_read_inputs before stream_block stream_offset initial data_block data_offset amount readonly ->
  gateway_read_inputs before stream_block stream_offset initial data_block data_offset amount
    (gateway_stable_readonly stable_readonly before world stream_block data_block readonly).
Proof.
  intros[CELLS SIZE STREAM_BOUND DATA_BOUND STREAM_PERM DATA_LIVE DATA_PERM SEPARATE
    READONLY_LIVE READONLY_READABLE READONLY_DATA READONLY_REMAINING READONLY_CANCEL].
  constructor;try assumption.
  - intros object position[HERE|[READABLE STABLE]].
    + apply READONLY_LIVE with(position:=position);exact HERE.
    + eapply Mem.perm_valid_block;exact READABLE.
  - intros object position[HERE|[READABLE STABLE]];[apply READONLY_READABLE;exact HERE|exact READABLE].
  - intros position RANGE[HERE|[READABLE[STABLE[NOT_STREAM NOT_DATA]]]];
      [exact(READONLY_DATA position RANGE HERE)|apply NOT_DATA;reflexivity].
  - intros position RANGE[HERE|[READABLE[STABLE[NOT_STREAM NOT_DATA]]]];
      [exact(READONLY_REMAINING position RANGE HERE)|apply NOT_STREAM;reflexivity].
  - intros position RANGE[HERE|[READABLE[STABLE[NOT_STREAM NOT_DATA]]]];
      [exact(READONLY_CANCEL position RANGE HERE)|apply NOT_STREAM;reflexivity].
Qed.

Lemma gateway_read_stable_context {World}native_private stable_readonly discipline mode
    before world stream_block stream_offset initial data_block data_offset amount readonly :
  @gateway_read_context World native_private stable_readonly discipline mode stream_block stream_offset initial
    data_block data_offset amount readonly before world ->
  gateway_read_context native_private stable_readonly discipline mode stream_block stream_offset initial
    data_block data_offset amount(gateway_stable_readonly stable_readonly before world stream_block data_block readonly)
    before world.
Proof.
  intros[SIDE[STREAM[DATA[IMMUTABLE INPUT]]]];split;[exact SIDE|].
  split;[exact STREAM|]. split;[exact DATA|]. split.
  - intros object position[HERE|[READABLE[STABLE OUTSIDE]]];[apply IMMUTABLE;exact HERE|exact STABLE].
  - apply gateway_read_stable_inputs;exact INPUT.
Qed.

Theorem gateway_read_stable_retained {World Event}(backend:gateway_backend World Event)io native_private stable_readonly
    discipline thread_errno(runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno)
    before world stream_block stream_offset final data_block data_offset amount readonly after next :
  gateway_read_context native_private stable_readonly discipline None stream_block stream_offset final
    data_block data_offset amount(gateway_stable_readonly stable_readonly before world stream_block data_block readonly)
    after next ->
  forall object position,Mem.perm before object position Cur Readable ->stable_readonly world object position ->
    stable_readonly next object position.
Proof.
  intros[SIDE[STREAM[DATA[IMMUTABLE INPUT]]]]object position READABLE STABLE.
  destruct(peq object stream_block)as[SAME|NOT_STREAM];[subst object|].
  - eapply gateway_thread_native_stable;[exact runtime|exact SIDE|exact STREAM].
  - destruct(peq object data_block)as[SAME|NOT_DATA];[subst object|].
    + eapply gateway_thread_native_stable;[exact runtime|exact SIDE|exact DATA].
    + apply IMMUTABLE;right;repeat split;assumption.
Qed.
