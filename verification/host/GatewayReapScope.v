(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: Fresh reap locals cannot name any retained caller region. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayThreadRuntime GatewayStreamInterface
  GatewayReapAllocation GatewayReapContext GatewayCallerBuffers GatewayCallerFamily GatewayBufferReference
  GatewayCallerReadonly GatewayLocalRuntime GatewayScopedMemory.
Import ListNotations.

Record gateway_reap_scope slots(readonly:block->Z->Prop)(selected:block->Prop)(reference:mem):Prop:={
  reap_status_reference_fresh:~Mem.valid_block reference(reap_status_slot slots);
  reap_pause_reference_fresh:~Mem.valid_block reference(reap_pause_slot slots);
  reap_status_readonly_separate:forall position,~readonly(reap_status_slot slots)position;
  reap_pause_readonly_separate:forall position,~readonly(reap_pause_slot slots)position;
  reap_status_selected_separate:~selected(reap_status_slot slots);
  reap_pause_selected_separate:~selected(reap_pause_slot slots)
}.

Theorem gateway_actual_reap_scope {World}native stable readonly selected reference owner before world slots:
  @gateway_caller_family World native stable readonly selected reference owner before world->(exists target,selected target)->
  ~Mem.valid_block before(reap_status_slot slots)->~Mem.valid_block before(reap_pause_slot slots)->
  gateway_reap_scope slots readonly selected reference.
Proof.
  intros FAMILY[target SELECTED]STATUS PAUSE.
  destruct(FAMILY target SELECTED)as[LIVE[PRIVATE[READONLY[BUFFER REST]]]].
  constructor.
  - intro VALID;apply STATUS;eapply Mem.valid_block_unchanged_on;[exact(proj1 BUFFER)|exact VALID].
  - intro VALID;apply PAUSE;eapply Mem.valid_block_unchanged_on;[exact(proj1 BUFFER)|exact VALID].
  - intros position HERE;apply STATUS;exact(proj1(READONLY _ _ HERE)).
  - intros position HERE;apply PAUSE;exact(proj1(READONLY _ _ HERE)).
  - intro HERE;apply STATUS;exact(proj1(FAMILY _ HERE)).
  - intro HERE;apply PAUSE;exact(proj1(FAMILY _ HERE)).
Qed.

Lemma gateway_reap_scope_avoids slots readonly selected reference target:
  gateway_reap_scope slots readonly selected reference->selected target->
  gateway_environment_avoids(gateway_caller_scope readonly target reference)(reap_environment slots).
Proof.
  intros SCOPE SELECTED identifier object ty position LOOK.
  assert(SLOT:object=reap_status_slot slots\/object=reap_pause_slot slots).
  { unfold reap_environment in LOOK;destruct(peq identifier _pause)as[SAME|OTHER].
    - subst identifier;rewrite PTree.gss in LOOK;inversion LOOK;right;reflexivity.
    - rewrite PTree.gso in LOOK by exact OTHER;destruct(peq identifier _status)as[SAME|DIFFERENT].
      + subst identifier;rewrite PTree.gss in LOOK;inversion LOOK;left;reflexivity.
      + rewrite PTree.gso in LOOK by exact DIFFERENT;rewrite PTree.gempty in LOOK;discriminate. }
  destruct SLOT as[STATUS|PAUSE];subst object;intros[SAME|[HERE|VALID]].
  - subst target;exact(reap_status_selected_separate _ _ _ _ SCOPE SELECTED).
  - exact(reap_status_readonly_separate _ _ _ _ SCOPE position HERE).
  - exact(reap_status_reference_fresh _ _ _ _ SCOPE VALID).
  - subst target;exact(reap_pause_selected_separate _ _ _ _ SCOPE SELECTED).
  - exact(reap_pause_readonly_separate _ _ _ _ SCOPE position HERE).
  - exact(reap_pause_reference_fresh _ _ _ _ SCOPE VALID).
Qed.

Theorem gateway_reap_context_store {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (thread:gateway_thread_runtime backend io native stable discipline thread_errno)
    saved slots allocated allocation_world readonly selected reference owner before world after chunk position value:
  gateway_reap_scope slots readonly selected reference->
  gateway_reap_context native stable discipline saved slots allocated allocation_world
    readonly selected reference owner before world->
  Mem.store chunk before(reap_pause_slot slots)position value=Some after->
  gateway_reap_context native stable discipline saved slots allocated allocation_world
    readonly selected reference owner after world.
Proof.
  intros SCOPE CONTEXT STORE;destruct CONTEXT as[SIDE[CALLER LOCALS]].
  assert(PRIVATE:native world(reap_pause_slot slots)).
  { exact (proj1 (proj2 (LOCALS _ (or_intror eq_refl)))). }
  split;[eapply gateway_thread_native_store;[exact thread|exact SIDE|exact PRIVATE|exact STORE]|].
  split;intros target SELECTED;eapply gateway_caller_buffers_store;
    [exact(CALLER target SELECTED)|exact STORE|exact(reap_pause_readonly_separate _ _ _ _ SCOPE)|
      exact(LOCALS target SELECTED)|exact STORE|exact(reap_pause_readonly_separate _ _ _ _ SCOPE)].
Qed.

Theorem gateway_reap_context_free {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (thread:gateway_thread_runtime backend io native stable discipline thread_errno)
    saved slots allocated allocation_world readonly selected reference owner before world after:
  gateway_reap_scope slots readonly selected reference->
  gateway_reap_context native stable discipline saved slots allocated allocation_world
    readonly selected reference owner before world->
  Mem.free_list before(blocks_of_env(Clight.globalenv prog)(reap_environment slots))=Some after->
  discipline(Some saved)after world /\gateway_caller_family native stable readonly selected reference owner after world.
Proof.
  intros SCOPE CONTEXT FREE.
  pose proof(gateway_reap_context_environment native stable discipline saved slots allocated allocation_world
    readonly selected reference owner before world CONTEXT)as PRIVATE.
  destruct CONTEXT as[SIDE[CALLER LOCALS]]. split.
  - eapply gateway_native_free_list;[exact thread|exact SIDE| |exact FREE].
    intros object low high MEMBER;eapply gateway_native_environment_free_blocks;[exact PRIVATE|exact MEMBER].
  - intros target SELECTED;eapply gateway_caller_buffers_source_frame;[exact(CALLER target SELECTED)|].
    eapply gateway_environment_avoids_free;
      [exact(gateway_reap_scope_avoids slots readonly selected reference target SCOPE SELECTED)|exact FREE].
Qed.
