(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Stream fields become initialized only through their actual stores. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory.
From HostGateway Require Import GatewayMachine GatewayThreadRuntime GatewayStreamInterface GatewayStreamMemory GatewayFramedRuntime
  GatewaySpawnResources GatewaySpawnRuntime GatewaySpawnActions GatewayPostSpawnContext GatewayPostSpawnCleanup GatewayPostSpawnStores
  GatewayCallerBuffers GatewayCallerFamily GatewayStreamInitialization.
Open Scope Z_scope.

Section Context.
Context {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno resources ipc builders genuine footprint
  (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
  (descriptors:gateway_spawn_descriptor_runtime backend io native stable discipline resources ipc)
  (sdk:gateway_spawn_builder_runtime backend io native stable discipline resources builders genuine footprint).
Variables(readonly:Values.block->Z->Prop)(selected:Values.block->Prop)(reference:mem)(owner:World)
  (data control stream:Values.block)(data_left data_right control_left control_right:Z)(leases:list(Z*gateway_resource_descriptor))
  (values:gateway_stream_values).
Hypotheses(DATA_SELECTED:selected data)(CONTROL_SELECTED:selected control)(STREAM_SELECTED:selected stream)
  (STREAM_DATA:stream<>data)(STREAM_CONTROL:stream<>control)(STREAM_READONLY:forall position,~readonly stream position)
  (STREAM_RANGE:Mem.range_perm reference stream 0 48 Cur Freeable).
Local Definition context:=gateway_postspawn_context native stable discipline resources builders genuine readonly selected reference owner
  data control data_left data_right control_left control_right postspawn_empty_builders leases.
Definition gateway_stream_setup_stage count memory world:Prop:=context memory world /\gateway_stream_prefix memory stream values count.

Lemma gateway_stream_setup_ambient count:
  (count<=8)%nat->gateway_ambient_closed backend(gateway_stream_setup_stage count).
Proof.
  intros COUNT before world after next[READY PREFIX]INTERFERENCE.
  assert(AFTER:context after next).
  { eapply gateway_postspawn_ambient;[exact runtime|exact descriptors|exact sdk|exact DATA_SELECTED|exact CONTROL_SELECTED
      |exact READY|exact INTERFERENCE]. }
  pose proof READY as INPUT;destruct INPUT as[SIDE VALID GENUINE BUILDERS FAMILY DATA CONTROL LEASES].
  destruct(gateway_thread_ambient _ _ _ _ _ _ runtime None before world after next SIDE INTERFERENCE)as[NORMAL[ACCESS FRAME]].
  split;[exact AFTER|]. eapply gateway_stream_prefix_unchanged;[exact COUNT|exact PREFIX|].
  eapply gateway_native_frame_restrict;[exact FRAME| |intros object position HERE BAD;exact BAD].
  intros object position[SAME INSIDE];subst object;left;exact(proj1(proj2(FAMILY stream STREAM_SELECTED))).
Qed.

Theorem gateway_stream_setup_next index before world:
  (index<8)%nat->
  ((exists object offset,stream_cancellation values=Vptr object offset)\/(exists word,stream_cancellation values=Vlong word))->
  gateway_stream_setup_stage index before world->
  exists after,Mem.store(stream_initial_chunk(stream_initial_cell values index))before stream
    (stream_initial_offset(stream_initial_cell values index))(stream_initial_value(stream_initial_cell values index))=Some after /\
    gateway_stream_setup_stage(S index)after world.
Proof.
  intros BOUND POINTER[READY PREFIX].
  assert(WRITABLE:Mem.range_perm before stream 0 48 Cur Writable).
  { destruct READY as[SIDE VALID GENUINE BUILDERS FAMILY DATA CONTROL LEASES].
    destruct(FAMILY stream STREAM_SELECTED)as[LIVE[PRIVATE[READONLY[[FRAME PERMISSIONS]HISTORY]]]].
    intros position RANGE;eapply Mem.perm_implies.
    - apply(proj1(PERMISSIONS stream(or_introl eq_refl)position Cur Freeable));apply STREAM_RANGE;exact RANGE.
    - constructor. }
  destruct(gateway_stream_initial_store before stream values index BOUND WRITABLE)as[after STORE].
  exists after;split;[exact STORE|]. split.
  - eapply gateway_postspawn_store;[exact runtime|exact sdk|exact READY|exact STREAM_SELECTED|exact STREAM_DATA|exact STREAM_CONTROL
      |exact STREAM_READONLY|exact STORE].
  - eapply gateway_stream_prefix_store;[exact BOUND|exact PREFIX|exact POINTER|exact STORE].
Qed.
End Context.
