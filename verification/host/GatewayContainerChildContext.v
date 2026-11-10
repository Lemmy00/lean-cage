(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Recursive reads update the same stream while retaining the
   enclosing parser's initialized tag/count cells and caller-owned readonly bytes. *)
From Stdlib Require Import ZArith Lia.
From compcert Require Import Coqlib Integers AST Values Memory.
From HostGateway Require Import GatewayMachine GatewayThreadRuntime GatewayStreamInterface GatewayStreamMemory
  GatewayValueEntry GatewayValueContext GatewayValueStack GatewayContainerLength GatewayContainerGuards GatewayWordsMemory.
Open Scope Z_scope.

Definition gateway_container_child_readonly slots readonly object position:Prop:=
  readonly object position \/gateway_byte_region(gateway_value_tag_slot slots)0 8 object position \/
    gateway_byte_region(gateway_value_size_slot slots)0 8 object position.

Theorem gateway_container_child_input {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    container slots stream_block stream_offset initial readonly original size before world:
  gateway_container_counted native stable discipline container slots stream_block stream_offset initial readonly original size before world->
  (forall object position,readonly object position->native world object)->
  gateway_value_context native stable discipline stream_block stream_offset initial
    (gateway_container_child_readonly slots readonly)before before world /\
  (forall object position,gateway_container_child_readonly slots readonly object position->native world object).
Proof.
  intros[[[CONTEXT[TAG[SIZE[TAG_OWN[SIZE_OWN[DIFFERENT[TAG_STREAM[SIZE_STREAM[NO_TAG NO_SIZE]]]]]]]]]TAG_LOAD]SIZE_LOAD]READONLY.
  destruct CONTEXT as[SIDE[STREAM[STABLE[INPUT FRAME]]]].
  split.
  2: { intros object position[OLD|[[SAME RANGE]|[SAME RANGE]]];
    [apply READONLY with(position:=position);exact OLD|subst object;exact TAG|subst object;exact SIZE]. }
  split;[exact SIDE|]. split;[exact STREAM|]. split.
  - intros object position[OLD|[[SAME RANGE]|[SAME RANGE]]].
    + apply STABLE;exact OLD.
    + subst object;eapply gateway_thread_native_stable;[exact runtime|exact SIDE|exact TAG].
    + subst object;eapply gateway_thread_native_stable;[exact runtime|exact SIDE|exact SIZE].
  - split;[|apply Mem.unchanged_on_refl].
    destruct INPUT as[CELLS BOUNDS OWNED LIVE READABLE CANCEL COUNTERS];constructor;try assumption.
    + intros object position[OLD|[[SAME RANGE]|[SAME RANGE]]].
      * apply LIVE with(position:=position);exact OLD.
      * subst object;eapply Mem.perm_valid_block;apply(TAG_OWN position);exact RANGE.
      * subst object;eapply Mem.perm_valid_block;apply(SIZE_OWN position);exact RANGE.
    + intros object position[OLD|[[SAME RANGE]|[SAME RANGE]]].
      * apply READABLE;exact OLD.
      * subst object;eapply Mem.perm_implies;[apply(TAG_OWN position);exact RANGE|constructor].
      * subst object;eapply Mem.perm_implies;[apply(SIZE_OWN position);exact RANGE|constructor].
    + intros position RANGE[OLD|[[SAME _]|[SAME _]]];[exact(CANCEL position RANGE OLD)|congruence|congruence].
    + intros position RANGE[OLD|[[SAME _]|[SAME _]]];[exact(COUNTERS position RANGE OLD)|congruence|congruence].
Qed.

Theorem gateway_container_child_return {World}native stable discipline container slots stream_block stream_offset initial final_stream
    readonly original size before world after next:
  @gateway_container_counted World native stable discipline container slots stream_block stream_offset initial readonly original size before world->
  gateway_value_context native stable discipline stream_block stream_offset final_stream
    (gateway_container_child_readonly slots readonly)before after next->
  (forall object position,gateway_container_child_readonly slots readonly object position->native next object)->
  gateway_container_counted native stable discipline container slots stream_block stream_offset final_stream readonly original size after next /\
  (forall object position,readonly object position->native next object).
Proof.
  intros[[[OLD_CONTEXT[TAG[SIZE[TAG_OWN[SIZE_OWN REST]]]]]TAG_LOAD]SIZE_LOAD]
    [SIDE[STREAM[STABLE[INPUT FRAME]]]]NATIVE.
  destruct OLD_CONTEXT as[OLD_SIDE[OLD_STREAM[OLD_STABLE[OLD_INPUT OLD_FRAME]]]].
  assert(TAG_NATIVE:native next(gateway_value_tag_slot slots)).
  { apply(NATIVE _ 0);right;left;split;[reflexivity|lia]. }
  assert(SIZE_NATIVE:native next(gateway_value_size_slot slots)).
  { apply(NATIVE _ 0);right;right;split;[reflexivity|lia]. }
  split;[split;[split;[split|]|]|].
  - split;[exact SIDE|]. split;[exact STREAM|]. split.
    + intros object position OLD;apply STABLE;left;exact OLD.
    + split.
      * destruct INPUT as[CELLS BOUNDS OWNED LIVE READABLE CANCEL COUNTERS];constructor.
        -- exact CELLS.
        -- exact BOUNDS.
        -- exact OWNED.
        -- intros object position OLD;apply LIVE with(position:=position);left;exact OLD.
        -- intros object position OLD;apply READABLE;left;exact OLD.
        -- intros position RANGE OLD;apply(CANCEL position RANGE);left;exact OLD.
        -- intros position RANGE OLD;apply(COUNTERS position RANGE);left;exact OLD.
      * eapply Mem.unchanged_on_trans;[exact OLD_FRAME|]. eapply Mem.unchanged_on_implies;[exact FRAME|intros;left;assumption].
  - split;[exact TAG_NATIVE|]. split;[exact SIZE_NATIVE|]. split.
    + intros position RANGE;eapply Mem.perm_unchanged_on;[exact FRAME|right;left;split;[reflexivity|exact RANGE]|apply TAG_OWN;exact RANGE].
    + split;[|exact REST]. intros position RANGE;eapply Mem.perm_unchanged_on;
        [exact FRAME|right;right;split;[reflexivity|exact RANGE]|apply SIZE_OWN;exact RANGE].
  - change(Mem.load Mint64 after(gateway_value_tag_slot slots)0=Some(Vlong(Int64.repr(gateway_container_code container)))).
    eapply Mem.load_unchanged_on;[exact FRAME| |exact TAG_LOAD].
    intros position RANGE;right;left;split;[reflexivity|exact RANGE].
  - change(Mem.load Mint64 after(gateway_value_size_slot slots)0=Some(Vlong size)).
    eapply Mem.load_unchanged_on;[exact FRAME| |exact SIZE_LOAD].
    intros position RANGE;right;right;split;[reflexivity|exact RANGE].
  - intros object position OLD;apply NATIVE with(position:=position);left;exact OLD.
Qed.
