(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: The real reap helper allocates its own status and pause slots. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess ReceiverAllocation.
From HostGateway Require Import GatewaySource GatewayMachine GatewayThreadRuntime GatewayLocalRuntime
  GatewayCallerBuffers GatewayCallerFamily GatewayClock GatewayRuntimeCuts GatewayReadonly GatewayStreamInterface.
Import ListNotations.
Open Scope Z_scope.

Record gateway_reap_slots:Type:={reap_status_slot:Values.block;reap_pause_slot:Values.block}.
Definition reap_environment slots:=PTree.set _pause(reap_pause_slot slots,Tstruct _timespec noattr)
  (PTree.set _status(reap_status_slot slots,tint)empty_env).
Definition reap_parameters child complete:=PTree.set _complete(Vint complete)
  (PTree.set _child(Vint child)(create_undef_temps(fn_temps f_host_engine_reap))).
Definition reap_allocations before slots after:Prop:=exists middle,
  Mem.alloc before 0 4=(middle,reap_status_slot slots) /\Mem.alloc middle 0 16=(after,reap_pause_slot slots).

Lemma reap_allocation_chain before slots after:
  reap_allocations before slots after->local_allocations before[(reap_status_slot slots,4);(reap_pause_slot slots,16)]after.
Proof. intros[middle[STATUS PAUSE]];econstructor;[exact STATUS|]. econstructor;[exact PAUSE|constructor]. Qed.

Lemma reap_function_entry before child complete slots after:
  reap_allocations before slots after->
  function_entry2(Clight.globalenv prog)f_host_engine_reap[Vint child;Vint complete]before
    (reap_environment slots)(reap_parameters child complete)after.
Proof.
  intros[middle[STATUS PAUSE]];constructor.
  - repeat(apply list_norepet_cons;[cbn;intuition discriminate|]);apply list_norepet_nil.
  - repeat(apply list_norepet_cons;[cbn;intuition discriminate|]);apply list_norepet_nil.
  - unfold list_disjoint,var_names;cbn;intros first second LEFT RIGHT.
    repeat destruct LEFT as[LEFT|LEFT];try contradiction;subst first;
      repeat destruct RIGHT as[RIGHT|RIGHT];try contradiction;subst second;discriminate.
  - cbn[fn_vars];eapply alloc_variables_cons with(m1:=middle)(b1:=reap_status_slot slots);[exact STATUS|].
    eapply alloc_variables_cons with(m1:=after)(b1:=reap_pause_slot slots).
    + assert(SIZE:sizeof(Clight.globalenv prog)(Tstruct _timespec noattr)=16)by exact actual_clock_sample_size.
      rewrite SIZE;exact PAUSE.
    + constructor.
  - reflexivity.
Qed.

Theorem actual_reap_entry_allocates before child complete environment temporaries after:
  function_entry2(Clight.globalenv prog)f_host_engine_reap[Vint child;Vint complete]before environment temporaries after->
  exists slots,environment=reap_environment slots /\temporaries=reap_parameters child complete /\reap_allocations before slots after /\
    ~Mem.valid_block before(reap_status_slot slots) /\~Mem.valid_block before(reap_pause_slot slots) /\
    reap_status_slot slots<>reap_pause_slot slots /\
    Mem.range_perm after(reap_status_slot slots)0 4 Cur Freeable /\Mem.range_perm after(reap_pause_slot slots)0 16 Cur Freeable /\
    Mem.unchanged_on(fun _ _=>True)before after.
Proof.
  intro ENTRY;destruct(Mem.alloc before 0 4)as[middle status]eqn:STATUS.
  destruct(Mem.alloc middle 0 16)as[canonical pause]eqn:PAUSE.
  set(slots:={|reap_status_slot:=status;reap_pause_slot:=pause|}).
  assert(ALLOC:reap_allocations before slots canonical)by(exists middle;auto).
  destruct(function_entry_unique _ _ _ _ _ _ _ _ _ _(reap_function_entry before child complete slots canonical ALLOC)ENTRY)
    as[ENV[TEMPS MEMORY]];subst environment temporaries after.
  pose proof(reap_allocation_chain _ _ _ ALLOC)as CHAIN.
  pose proof(local_allocations_objects _ _ _ CHAIN)as OBJECTS.
  inversion OBJECTS as[|? ? STATUS_OBJECT REST];subst;inversion REST as[|? ? PAUSE_OBJECT TAIL];subst.
  pose proof(local_allocations_distinct _ _ _ CHAIN)as DISTINCT;inversion DISTINCT as[|? ? DIFFERENT NODUP];subst.
  exists slots;split;[reflexivity|]. split;[reflexivity|]. split;[exact ALLOC|].
  split;[exact(proj1 STATUS_OBJECT)|]. split;[exact(proj1 PAUSE_OBJECT)|].
  split;[intro SAME;apply DIFFERENT;cbn;auto|]. split;[exact(proj2 STATUS_OBJECT)|].
  split;[exact(proj2 PAUSE_OBJECT)|eapply local_allocations_unchanged;exact CHAIN].
Qed.

Theorem reap_allocations_thread {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (thread:gateway_thread_runtime backend io native stable discipline thread_errno)
    mode before world slots after readonly selected reference owner:
  discipline mode before world->reap_allocations before slots after->
  gateway_caller_family native stable readonly selected reference owner before world->
  discipline mode after world /\gateway_native_environment native world after(reap_environment slots) /\
    gateway_caller_family native stable readonly selected reference owner after world.
Proof.
  intros SIDE[middle[STATUS PAUSE]]FAMILY.
  assert(MIDDLE:discipline mode middle world)by(eapply gateway_thread_native_alloc;[exact thread|exact SIDE|exact STATUS]).
  assert(AFTER:discipline mode after world)by(eapply gateway_thread_native_alloc;[exact thread|exact MIDDLE|exact PAUSE]).
  assert(STATUS_PRIVATE:native world(reap_status_slot slots)).
  { eapply gateway_thread_fresh_native;[exact thread|exact SIDE|eapply Mem.fresh_block_alloc;exact STATUS]. }
  assert(PAUSE_PRIVATE:native world(reap_pause_slot slots)).
  { eapply gateway_thread_fresh_native;[exact thread|exact MIDDLE|eapply Mem.fresh_block_alloc;exact PAUSE]. }
  split;[exact AFTER|]. split.
  - intros identifier object ty LOOK;unfold reap_environment in LOOK.
    destruct(peq identifier _pause)as[SAME|OTHER].
    + subst identifier;rewrite PTree.gss in LOOK;inversion LOOK;subst object;split;
        [eapply Mem.valid_new_block;exact PAUSE|exact PAUSE_PRIVATE].
    + rewrite PTree.gso in LOOK by exact OTHER;destruct(peq identifier _status)as[SAME|DIFFERENT].
      * subst identifier;rewrite PTree.gss in LOOK;inversion LOOK;subst object;split.
        -- eapply Mem.valid_block_alloc;[exact PAUSE|eapply Mem.valid_new_block;exact STATUS].
        -- exact STATUS_PRIVATE.
      * rewrite PTree.gso in LOOK by exact DIFFERENT;rewrite PTree.gempty in LOOK;discriminate.
  - intros object HERE;eapply gateway_caller_buffers_alloc;[|exact PAUSE].
    eapply gateway_caller_buffers_alloc;[exact(FAMILY object HERE)|exact STATUS].
Qed.
