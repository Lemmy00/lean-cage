(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Decoder returns free only the two actual owned local word cells. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayValueEntry GatewayValueContext GatewayValueStack
  GatewayReturnRuntime GatewayLocalRuntime.
Import ListNotations.
Open Scope Z_scope.

Lemma gateway_value_environment_slots slots identifier object ty :
  (gateway_value_environment slots)!identifier=Some(object,ty) ->
  object=gateway_value_tag_slot slots \/object=gateway_value_size_slot slots.
Proof.
  unfold gateway_value_environment;rewrite PTree.gsspec.
  destruct(peq identifier _size)as[SAME|DIFFERENT].
  - intro LOOK;inversion LOOK;right;reflexivity.
  - rewrite PTree.gsspec;destruct(peq identifier _tag)as[SAME|DIFFERENT_TAG].
    + intro LOOK;inversion LOOK;left;reflexivity.
    + rewrite PTree.gempty;discriminate.
Qed.

Theorem gateway_value_active_environment {World}native stable discipline slots stream_block stream_offset
    initial readonly original memory world :
  @gateway_value_active World native stable discipline slots stream_block stream_offset initial readonly original memory world ->
  gateway_return_environment native discipline None(gateway_value_environment slots)memory world.
Proof.
  intros[CONTEXT[TAG[SIZE[TAG_OWN[SIZE_OWN REST]]]]];split;[exact(proj1 CONTEXT)|].
  intros identifier object ty LOOK;destruct(gateway_value_environment_slots _ _ _ _ LOOK)as[SAME|SAME];subst object;
    split;try assumption;eapply Mem.perm_valid_block;
      [apply(TAG_OWN 0);lia|apply(SIZE_OWN 0);lia].
Qed.
