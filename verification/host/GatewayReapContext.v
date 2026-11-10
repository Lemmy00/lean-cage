(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: Real reap locals retain the caller's roots and permissions. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayThreadRuntime GatewayStreamInterface
  GatewayReapAllocation GatewayCallerBuffers GatewayCallerFamily GatewayBufferReference GatewayLocalRuntime
  GatewayFramedRuntime GatewayDetachedClock GatewayClockModeInterface.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_reap_selected slots object:Prop:=object=reap_status_slot slots\/object=reap_pause_slot slots.

Definition gateway_reap_context {World}(native:World->block->Prop)(stable:World->block->Z->Prop)
    (discipline:option val->mem->World->Prop)saved slots allocated allocation_world readonly selected reference owner
    memory world:Prop:=
  discipline(Some saved)memory world /\
  gateway_caller_family native stable readonly selected reference owner memory world /\
  gateway_caller_family native stable readonly(gateway_reap_selected slots)allocated allocation_world memory world.

Lemma gateway_reap_context_environment {World}native stable discipline saved slots allocated allocation_world
    readonly selected reference owner memory world:
  @gateway_reap_context World native stable discipline saved slots allocated allocation_world
    readonly selected reference owner memory world->
  gateway_native_environment native world memory(reap_environment slots).
Proof.
  intros[SIDE[CALLER LOCALS]]identifier object ty LOOK.
  assert(HERE:gateway_reap_selected slots object).
  { unfold reap_environment in LOOK;destruct(peq identifier _pause)as[SAME|OTHER].
    - subst identifier;rewrite PTree.gss in LOOK;inversion LOOK;right;reflexivity.
    - rewrite PTree.gso in LOOK by exact OTHER;destruct(peq identifier _status)as[SAME|DIFFERENT].
      + subst identifier;rewrite PTree.gss in LOOK;inversion LOOK;left;reflexivity.
      + rewrite PTree.gso in LOOK by exact DIFFERENT;rewrite PTree.gempty in LOOK;discriminate. }
  exact(conj(proj1(LOCALS object HERE))(proj1(proj2(LOCALS object HERE)))).
Qed.

Theorem gateway_reap_context_ambient {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (thread:gateway_thread_runtime backend io native stable discipline thread_errno)
    saved slots allocated allocation_world readonly selected reference owner:
  gateway_ambient_closed backend(gateway_reap_context native stable discipline saved slots allocated allocation_world
    readonly selected reference owner).
Proof.
  intros before world after next[SIDE[CALLER LOCALS]]INTERFERENCE.
  destruct(gateway_thread_ambient _ _ _ _ _ _ thread(Some saved)before world after next SIDE INTERFERENCE)
    as[AFTER[ACCESS FRAME]].
  split;[exact AFTER|]. split;intros target SELECTED;eapply gateway_caller_buffers_no_output;
    [exact(CALLER target SELECTED)|exact ACCESS|exact FRAME|exact(LOCALS target SELECTED)|exact ACCESS|exact FRAME].
Qed.

Theorem gateway_reap_context_allocated {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (thread:gateway_thread_runtime backend io native stable discipline thread_errno)
    saved before world child complete environment temporaries allocated readonly selected reference owner:
  discipline(Some saved)before world->
  gateway_caller_family native stable readonly selected reference owner before world->(exists target,selected target)->
  function_entry2(Clight.globalenv prog)f_host_engine_reap[Vint child;Vint complete]before environment temporaries allocated->
  exists slots,environment=reap_environment slots /\temporaries=reap_parameters child complete /\
    reap_allocations before slots allocated /\
    gateway_reap_context native stable discipline saved slots allocated world readonly selected reference owner allocated world.
Proof.
  intros SIDE FAMILY NONEMPTY ENTRY.
  destruct(actual_reap_entry_allocates before child complete environment temporaries allocated ENTRY)
    as(slots&ENV&TEMPS&ALLOC&STATUS_FRESH&PAUSE_FRESH&SEPARATE&STATUS_PERMISSION&PAUSE_PERMISSION&FRAME).
  subst environment temporaries.
  destruct(reap_allocations_thread backend io native stable discipline thread_errno thread(Some saved)
    before world slots allocated readonly selected reference owner SIDE ALLOC FAMILY)as[AFTER[ENV FAMILY_AFTER]].
  exists slots;split;[reflexivity|]. split;[reflexivity|]. split;[exact ALLOC|].
  split;[exact AFTER|]. split;[exact FAMILY_AFTER|]. apply gateway_caller_family_refl.
  - intros target[STATUS|PAUSE];subst target.
    + apply(ENV _status(reap_status_slot slots)tint);unfold reap_environment;
        rewrite PTree.gso by discriminate;apply PTree.gss.
    + apply(ENV _pause(reap_pause_slot slots)(Tstruct _timespec noattr));apply PTree.gss.
  - destruct NONEMPTY as[target SELECTED];exact(proj1(proj2(proj2(FAMILY_AFTER target SELECTED)))).
Qed.

Theorem gateway_reap_status_pointer {World}native stable discipline saved slots allocated allocation_world
    readonly selected reference owner memory world before:
  reap_allocations before slots allocated->
  @gateway_reap_context World native stable discipline saved slots allocated allocation_world
    readonly selected reference owner memory world->
  native world(reap_status_slot slots) /\gateway_native_pointer memory(reap_status_slot slots)Ptrofs.zero 4 Writable.
Proof.
  intros ALLOC[SIDE[CALLER LOCALS]].
  pose proof(LOCALS(reap_status_slot slots)(or_introl eq_refl))as[LIVE[PRIVATE[READONLY[BUFFER REST]]]].
  split;[exact PRIVATE|]. split;[lia|]. split;[vm_compute;discriminate|]. split;[exact LIVE|].
  intros position RANGE;apply Mem.perm_implies with(p1:=Freeable);[|constructor].
  apply(proj1(proj2 BUFFER(reap_status_slot slots)(or_introl eq_refl)position Cur Freeable)).
  destruct ALLOC as[middle[STATUS PAUSE]].
  eapply Mem.perm_alloc_1;[exact PAUSE|]. eapply Mem.perm_alloc_2;[exact STATUS|]. cbn in RANGE;exact RANGE.
Qed.

Theorem gateway_reap_clock_context {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (thread:gateway_thread_runtime backend io native stable discipline thread_errno)saved
    (clock:gateway_clock_mode_operation backend io native stable discipline(Some saved))
    slots allocated allocation_world readonly selected reference owner before world events returned after next descriptor:
  gateway_reap_context native stable discipline saved slots allocated allocation_world
    readonly selected reference owner before world->(exists target,selected target)->
  gateway_steps backend(Clight.globalenv prog)(gateway_live(Callstate(Internal f_host_now)[]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next)->
  gateway_reap_context native stable discipline saved slots allocated allocation_world
    readonly selected reference owner after next /\gateway_received_bytes io descriptor events=[].
Proof.
  intros[SIDE[CALLER LOCALS]]NONEMPTY RUN.
  destruct(gateway_actual_detached_clock backend io native stable discipline thread_errno thread saved clock
    readonly selected reference owner before world events returned after next descriptor SIDE CALLER NONEMPTY RUN)
    as[AFTER[CALLER_AFTER EMPTY]].
  destruct(gateway_actual_detached_clock backend io native stable discipline thread_errno thread saved clock
    readonly(gateway_reap_selected slots)allocated allocation_world before world events returned after next descriptor
    SIDE LOCALS ltac:(exists(reap_status_slot slots);left;reflexivity)RUN)as[AFTER2[LOCALS_AFTER EMPTY2]].
  split;[split;[exact AFTER|split;assumption]|exact EMPTY].
Qed.
