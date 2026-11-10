(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Each real reaper API preserves only its caller-owned regions. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayRuntime GatewayThreadRuntime GatewayStreamInterface
  GatewayReapRuntime GatewayReapAllocation GatewayReapContext GatewayReapScope GatewayCallerBuffers GatewayCallerFamily
  GatewayPairBuffers GatewayReapStructure GatewayRuntimeABI.
Import ListNotations.
Open Scope Z_scope.

Lemma gateway_reap_positive_group child:
  0<Int.signed child->Int.signed(Int.neg child)<0.
Proof.
  intro POSITIVE.
  replace(Int.neg child)with(Int.repr(-Int.signed child))by(rewrite <-Int.neg_repr,Int.repr_signed;reflexivity).
  rewrite Int.signed_repr;[lia|].
  pose proof(Int.signed_range child)as RANGE.
  change(-2147483648<=Int.signed child<=2147483647)in RANGE.
  change(-2147483648<= -Int.signed child<=2147483647);lia.
Qed.

Theorem gateway_reap_context_no_output {World}native stable discipline saved slots allocated allocation_world
    readonly selected reference owner before world after next:
  @gateway_reap_context World native stable discipline saved slots allocated allocation_world
    readonly selected reference owner before world->
  discipline(Some saved)after next->gateway_access_retained native stable before world next->
  gateway_native_frame native stable gateway_native_no_output world before after->
  gateway_reap_context native stable discipline saved slots allocated allocation_world
    readonly selected reference owner after next.
Proof.
  intros[SIDE[CALLER LOCALS]]AFTER ACCESS FRAME;split;[exact AFTER|].
  split;intros target SELECTED;eapply gateway_caller_buffers_no_output;
    [exact(CALLER target SELECTED)|exact ACCESS|exact FRAME|exact(LOCALS target SELECTED)|exact ACCESS|exact FRAME].
Qed.

Theorem gateway_reap_context_status_output {World}native stable discipline saved slots allocated allocation_world
    readonly selected reference owner before world after next:
  gateway_reap_scope slots readonly selected reference->
  @gateway_reap_context World native stable discipline saved slots allocated allocation_world
    readonly selected reference owner before world->
  discipline(Some saved)after next->gateway_access_retained native stable before world next->
  gateway_native_permissions before after(reap_status_slot slots)Ptrofs.zero 4->
  gateway_native_frame native stable(gateway_native_region(reap_status_slot slots)Ptrofs.zero 4)world before after->
  gateway_reap_context native stable discipline saved slots allocated allocation_world
    readonly selected reference owner after next.
Proof.
  intros SCOPE[SIDE[CALLER LOCALS]]AFTER ACCESS PERMISSIONS FRAME;split;[exact AFTER|].
  assert(PRESERVE:forall target ref initial,
    gateway_caller_buffers native stable readonly target ref initial before world->
    gateway_caller_buffers native stable readonly target ref initial after next).
  { intros target ref initial HISTORY;eapply gateway_caller_buffers_operation;
      [exact HISTORY|exact ACCESS|exact FRAME|apply gateway_native_region_dec| | |].
    - intros object position HERE[SAME RANGE];subst object.
      exact(reap_status_readonly_separate _ _ _ _ SCOPE position HERE).
    - intros position kind permission[SAME RANGE];subst target;apply PERMISSIONS;exact RANGE.
    - intros object position READABLE[SAME RANGE];subst object.
      apply(proj1(PERMISSIONS position Cur Readable RANGE));exact READABLE. }
  split;intros target SELECTED;apply PRESERVE;[exact(CALLER target SELECTED)|exact(LOCALS target SELECTED)].
Qed.

Theorem gateway_reap_pause_pointer {World}native stable discipline saved slots allocated allocation_world
    readonly selected reference owner memory world before:
  reap_allocations before slots allocated->
  @gateway_reap_context World native stable discipline saved slots allocated allocation_world
    readonly selected reference owner memory world->
  native world(reap_pause_slot slots) /\gateway_native_pointer memory(reap_pause_slot slots)Ptrofs.zero 16 Readable.
Proof.
  intros ALLOC[SIDE[CALLER LOCALS]].
  pose proof(LOCALS(reap_pause_slot slots)(or_intror eq_refl))as[LIVE[PRIVATE[READONLY[BUFFER REST]]]].
  split;[exact PRIVATE|]. split;[lia|]. split;[vm_compute;discriminate|]. split;[exact LIVE|].
  intros position RANGE;apply Mem.perm_implies with(p1:=Freeable);[|constructor].
  apply(proj1(proj2 BUFFER(reap_pause_slot slots)(or_introl eq_refl)position Cur Freeable)).
  destruct ALLOC as[middle[STATUS PAUSE]];eapply Mem.perm_alloc_2;[exact PAUSE|]. cbn in RANGE;exact RANGE.
Qed.

Theorem gateway_reap_api_effect {World Event}(backend:gateway_backend World Event)io observation native stable discipline thread_errno
    (thread:gateway_thread_runtime backend io native stable discipline thread_errno)
    (runtime:gateway_reap_runtime backend io observation native stable discipline thread_errno)
    saved slots allocated allocation_world readonly selected reference owner allocation_before child site
    before world result after next event:
  0<Int.signed child->site<>reap_site_clock->reap_allocations allocation_before slots allocated->
  gateway_reap_scope slots readonly selected reference->
  gateway_reap_context native stable discipline saved slots allocated allocation_world
    readonly selected reference owner before world->
  gateway_runtime_operation backend(reap_site_definition site)(reap_site_values slots child site)
    before world result after next event->
  gateway_reap_context native stable discipline saved slots allocated allocation_world
    readonly selected reference owner after next /\io event=None.
Proof.
  intros CHILD NOT_CLOCK ALLOC SCOPE CONTEXT OPERATION.
  pose proof(proj1 CONTEXT)as SIDE;destruct site;[contradiction| | | | |].
  - destruct(gateway_reap_kill_operation _ _ _ _ _ _ _ runtime(Some saved)before world(Int.neg child)result after next event
      SIDE(gateway_reap_positive_group child CHILD)OPERATION)
      as(status&RETURNED&RANGE&OBSERVATION&AFTER&ACCESS&FRAME&IO).
    split;[eapply gateway_reap_context_no_output;eassumption|exact IO].
  - destruct(gateway_reap_status_pointer native stable discipline saved slots allocated allocation_world
      readonly selected reference owner before world allocation_before ALLOC CONTEXT)as[PRIVATE POINTER].
    destruct(gateway_reap_wait_operation _ _ _ _ _ _ _ runtime(Some saved)before world child Int.one
      (reap_status_slot slots)Ptrofs.zero result after next event SIDE CHILD(or_intror eq_refl)PRIVATE POINTER OPERATION)
      as(observed&status&RETURNED&RANGE&BYTES&ABSENT&OBSERVATION&AFTER&ACCESS&PERMISSIONS&FRAME&IO).
    split;[eapply gateway_reap_context_status_output;eassumption|exact IO].
  - destruct(gateway_reap_status_pointer native stable discipline saved slots allocated allocation_world
      readonly selected reference owner before world allocation_before ALLOC CONTEXT)as[PRIVATE POINTER].
    destruct(gateway_reap_wait_operation _ _ _ _ _ _ _ runtime(Some saved)before world child Int.zero
      (reap_status_slot slots)Ptrofs.zero result after next event SIDE CHILD(or_introl eq_refl)PRIVATE POINTER OPERATION)
      as(observed&status&RETURNED&RANGE&BYTES&ABSENT&OBSERVATION&AFTER&ACCESS&PERMISSIONS&FRAME&IO).
    split;[eapply gateway_reap_context_status_output;eassumption|exact IO].
  - destruct(gateway_reap_pause_pointer native stable discipline saved slots allocated allocation_world
      readonly selected reference owner before world allocation_before ALLOC CONTEXT)as[PRIVATE POINTER].
    destruct(gateway_reap_pause_operation _ _ _ _ _ _ _ runtime(Some saved)before world
      (reap_pause_slot slots)Ptrofs.zero result after next event SIDE PRIVATE POINTER OPERATION)
      as(status&RETURNED&RANGE&OBSERVATION&AFTER&ACCESS&FRAME&IO).
    split;[eapply gateway_reap_context_no_output;eassumption|exact IO].
  - destruct(gateway_errno_location_operation _ _ _ _ _ _ thread(Some saved)before world result after next event SIDE OPERATION)
      as(object&offset&RETURNED&POINTER&NUMBER&FOREIGN&UNSTABLE&AFTER&ACCESS&FRAME&IO).
    split;[eapply gateway_reap_context_no_output;eassumption|exact IO].
Qed.
