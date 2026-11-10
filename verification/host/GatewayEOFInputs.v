(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: EOF output authority is retained from actual caller scratch
   storage. *)
From Stdlib Require Import ZArith Lia.
From compcert Require Import Integers AST Values Memory Ctypes Clight.
From HostGateway Require Import GatewayStreamInterface GatewayReadContext GatewayValueEntry GatewayValueContext.
Open Scope Z_scope.

Definition gateway_eof_readonly(readonly:Values.block->Z->Prop)(extra:Values.block)object position:Prop:=
  readonly object position /\object<>extra.

Theorem gateway_eof_inputs_from_parser {World}(native:World->Values.block->Prop)stable discipline
    stream extra initial readonly original memory(world:World):
  gateway_value_context native stable discipline stream Ptrofs.zero initial readonly original memory world->
  (forall object position,readonly object position->native world object)->stream<>extra->
  (forall position,0<=position<1->readonly extra position)->
  Mem.range_perm original extra 0 1 Cur Writable->
  gateway_read_context native stable discipline None stream Ptrofs.zero initial extra Ptrofs.zero 1
    (gateway_eof_readonly readonly extra)memory world.
Proof.
  intros[SIDE[STREAM[STABLE[INPUT FRAME]]]]NATIVE SEPARATE EXTRA OWNED.
  assert(EXTRA_PERMISSIONS:Mem.range_perm memory extra 0 1 Cur Writable).
  { intros position RANGE;eapply Mem.perm_unchanged_on;[exact FRAME|apply EXTRA;exact RANGE|apply OWNED;exact RANGE]. }
  assert(EXTRA_LIVE:Mem.valid_block memory extra).
  { eapply Mem.perm_valid_block;apply(EXTRA_PERMISSIONS 0);lia. }
  split;[exact SIDE|]. split;[exact STREAM|]. split.
  - apply(NATIVE extra 0),EXTRA;lia.
  - split;[intros object position[HERE OTHER];apply STABLE;exact HERE|].
    constructor.
    + exact(gateway_value_stream_cells _ _ _ _ _ INPUT).
    + change(0<=1<=18446744073709551615);lia.
    + exact(gateway_value_stream_bounds _ _ _ _ _ INPUT).
    + change(0+1<=18446744073709551616);lia.
    + exact(gateway_value_stream_owned _ _ _ _ _ INPUT).
    + exact EXTRA_LIVE.
    + exact EXTRA_PERMISSIONS.
    + left;exact SEPARATE.
    + intros object position[HERE OTHER];exact(gateway_value_readonly_live _ _ _ _ _ INPUT object position HERE).
    + intros object position[HERE OTHER];exact(gateway_value_readonly_readable _ _ _ _ _ INPUT object position HERE).
    + intros position RANGE[HERE OTHER];apply OTHER;reflexivity.
    + intros position RANGE[HERE OTHER];eapply gateway_value_readonly_counters;[exact INPUT| |exact HERE].
      change(24<=position<40);change(24<=position<32)in RANGE;lia.
    + intros position RANGE[HERE OTHER];eapply gateway_value_readonly_cancel;[exact INPUT|exact RANGE|exact HERE].
Qed.

Theorem gateway_eof_control_from_parser {World}(native:World->Values.block->Prop)stable discipline
    stream initial readonly original memory(world:World)control:
  gateway_value_context native stable discipline stream Ptrofs.zero initial readonly original memory world->
  (forall position,4<=position<8->readonly stream position)->
  Mem.load Mint32 original stream 4=Some(Vint control)->stream_control initial=control.
Proof.
  intros[SIDE[STREAM[STABLE[INPUT FRAME]]]]READONLY LOAD.
  assert(SAME:Mem.load Mint32 memory stream 4=Some(Vint control)).
  { eapply Mem.load_unchanged_on;[exact FRAME|exact READONLY|exact LOAD]. }
  pose proof(proj1(proj2(gateway_value_stream_cells _ _ _ _ _ INPUT)))as CURRENT.
  change(Mem.load Mint32 memory stream 4=Some(Vint(stream_control initial)))in CURRENT.
  congruence.
Qed.
