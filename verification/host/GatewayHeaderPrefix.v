(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Later header words preserve the actual earlier prefix. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Memdata.
From HostGateway Require Import GatewayHeaderRuntime GatewayBufferReference GatewayThreadRuntime GatewayWordsMemory.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_header_prefix_region(readonly:block->Z->Prop)(object:block)count other position:Prop:=
  readonly other position \/(other=object /\0<=position<count).

Lemma gateway_header_resources_compose {World}native_private stable_readonly discipline mode object held
    readonly large original origin before current after next:
  @gateway_header_resources World native_private stable_readonly discipline mode object held readonly original origin before current->
  gateway_header_resources native_private stable_readonly discipline mode object held large before current after next->
  (forall other position,readonly other position->large other position)->
  gateway_header_resources native_private stable_readonly discipline mode object held readonly original origin after next.
Proof.
  intros[INITIAL_SIDE INITIAL_PRIVATE INITIAL_LIVE INITIAL_HELD INITIAL_READONLY INITIAL_FRAME INITIAL_PERM INITIAL_NATIVE INITIAL_STABLE]
    [SIDE PRIVATE LIVE HELD READONLY FRAME PERM NATIVE STABLE]INCLUDED.
  constructor;try assumption.
  - intros other position HERE;apply READONLY;apply INCLUDED;exact HERE.
  - eapply Mem.unchanged_on_trans;[exact INITIAL_FRAME|].
    eapply Mem.unchanged_on_implies;[exact FRAME|]. intros other position HERE VALID;apply INCLUDED;exact HERE.
  - intros position kind permission;rewrite INITIAL_PERM;apply PERM.
  - eapply gateway_native_reference_transitive;eassumption.
  - intros other position READABLE IMMUTABLE.
    destruct(INITIAL_STABLE other position READABLE IMMUTABLE)as[CURRENT_READABLE CURRENT_IMMUTABLE].
    apply STABLE;assumption.
Qed.

Lemma gateway_header_resources_prefix {World}native_private stable_readonly discipline mode object held readonly original origin
    before world prefix:
  @gateway_header_resources World native_private stable_readonly discipline mode object held readonly original origin before world->
  Mem.loadbytes before object 0(Z.of_nat(length prefix))=Some(inj_bytes prefix)->
  gateway_header_resources native_private stable_readonly discipline mode object held
    (gateway_header_prefix_region readonly object(Z.of_nat(length prefix)))before world before world.
Proof.
  intros[SIDE PRIVATE LIVE HELD READONLY FRAME PERMISSIONS NATIVE STABLE]BYTES.
  eapply gateway_header_resources_initial;[exact SIDE|exact PRIVATE|exact LIVE|exact HELD|].
  intros other position[HERE|[SAME RANGE]];[apply READONLY;exact HERE|].
  subst other;split;[|left;exact PRIVATE].
  eapply Mem.loadbytes_range_perm;eassumption.
Qed.

Lemma gateway_header_prefix_retained readonly object prefix before after:
  Mem.loadbytes before object 0(Z.of_nat(length prefix))=Some(inj_bytes prefix)->
  Mem.unchanged_on(gateway_header_prefix_region readonly object(Z.of_nat(length prefix)))before after->
  Mem.loadbytes after object 0(Z.of_nat(length prefix))=Some(inj_bytes prefix).
Proof.
  intros BYTES FRAME;eapply Mem.loadbytes_unchanged_on;[exact FRAME| |exact BYTES].
  intros position RANGE;right;split;[reflexivity|exact RANGE].
Qed.

Lemma gateway_header_prefix_extend readonly object prefix word before after:
  Mem.loadbytes before object 0(Z.of_nat(length prefix))=Some(inj_bytes prefix)->
  Mem.loadbytes after object(Z.of_nat(length prefix))(Z.of_nat(length word))=Some(inj_bytes word)->
  Mem.unchanged_on(gateway_header_prefix_region readonly object(Z.of_nat(length prefix)))before after->
  Mem.loadbytes after object 0(Z.of_nat(length(prefix++word)))=Some(inj_bytes(prefix++word)).
Proof.
  intros PREFIX WORD FRAME.
  pose proof(gateway_header_prefix_retained readonly object prefix before after PREFIX FRAME)as EARLIER.
  rewrite length_app,Nat2Z.inj_add;unfold inj_bytes in *;rewrite map_app.
  eapply Mem.loadbytes_concat;[exact EARLIER| |lia|lia].
  change(0+Z.of_nat(length prefix))with(Z.of_nat(length prefix));exact WORD.
Qed.

Lemma gateway_header_word_after_prefix readonly object(prefix:list Byte.int)width:
  0<=width->
  (forall position,Z.of_nat(length prefix)<=position<Z.of_nat(length prefix)+width->~readonly object position)->
  forall position,Z.of_nat(length prefix)<=position<Z.of_nat(length prefix)+width->
    ~gateway_header_prefix_region readonly object(Z.of_nat(length prefix))object position.
Proof. intros WIDTH DISJOINT position RANGE[OLD|[SAME EARLIER]];[eapply DISJOINT;eassumption|lia]. Qed.
