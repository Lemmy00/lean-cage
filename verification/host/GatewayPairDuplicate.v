(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: The actual duplicate return determines the replacement lease and stored FD. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewaySpawnABI GatewaySpawnResources GatewaySpawnRuntime
  GatewayPairContext GatewayPairMemory GatewayPairStatements GatewayPairDuplicateTail GatewayPairMove
  GatewayThreadRuntime GatewayFramedRuntime GatewaySetupPaths GatewayOperations GatewayFrames GatewayStreamInterface GatewayPairBuffers.
Import ListNotations.
Open Scope Z_scope.

Section PairDuplicate.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
  (native_private:World->block->Prop)(stable_readonly:World->block->Z->Prop)
  (discipline:option val->mem->World->Prop)(thread_errno:World->int)
  (resources:World->gateway_resource_state)(ipc:nat->Prop).
Context(runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno)
  (descriptors:gateway_spawn_descriptor_runtime backend io native_private stable_readonly discipline resources ipc).
Variable ge:Clight.genv.
Variable identity:gateway_pair_identity ipc.
Variable object:block.
Variable offset:ptrofs.
Variable history:mem->World->Prop.
Context(buffers:gateway_pair_buffer_laws backend native_private stable_readonly discipline object offset history).
Local Definition pair_context left right:=gateway_pair_full_context native_private discipline resources ipc identity object offset left right history.
Local Lemma pair_context_closed left right:gateway_ambient_closed backend(pair_context left right).
Proof. apply gateway_pair_full_context_ambient with(io:=io)(stable_readonly:=stable_readonly)(thread_errno:=thread_errno);assumption. Qed.

Lemma actual_pair_duplicate_context left right index moved before world after next:
  pair_context left right before world->0<=index<2->discipline None after next->gateway_resource_valid(resources next)->
  gateway_access_retained native_private stable_readonly before world next->
  gateway_native_frame native_private stable_readonly gateway_native_no_output world before after->
  gateway_duplicate_receipt(resources world)(resources next)(pair_slot_value index left right)4 moved
    (pair_slot_entry ipc identity index)->gateway_exclusive_kept(resources world)(resources next)->
  pair_before_close native_private discipline resources ipc identity object offset history left right
    (pair_slot_left index moved left)(pair_slot_right index moved right)
    (pair_slot_value index left right)(pair_slot_entry ipc identity index)after next /\
    moved<>pair_slot_value index left right /\4<=moved.
Proof.
  intros CONTEXT RANGE SIDE VALID ACCESS FRAME DUPLICATE EXCLUSIVE.
  pose proof(gateway_pair_slot_duplicate ipc identity left right moved index(resources world)(resources next)
    (proj2(proj2(proj2(proj1 CONTEXT)))))as MOVE.
  destruct(MOVE VALID RANGE DUPLICATE EXCLUSIVE)as[RESOURCES[DIFFERENT MINIMUM]].
  assert(OLD:gateway_pair_full_storage native_private discipline resources ipc identity object offset
    left right left right history after next).
  { eapply gateway_pair_full_storage_preserved;[exact buffers|exact CONTEXT|exact SIDE|exact ACCESS|exact FRAME|exact VALID|
      exact(gateway_duplicate_frame _ _ _ _ _ _ DUPLICATE)|tauto|tauto|
      exact(gateway_duplicate_status _ _ _ _ _ _ DUPLICATE)|intros;tauto|exact EXCLUSIVE]. }
  split;[|auto]. split.
  - destruct OLD as[[AFTER[PRIVATE[CELLS IGNORED]]]HISTORY];split;[|exact HISTORY].
    split;[exact AFTER|]. split;[exact PRIVATE|]. split;assumption.
  - eapply gateway_duplicate_keeps_source;exact DUPLICATE.
Qed.

Theorem actual_pair_duplicate_script left right index temporaries memory result duplicate_symbol close_symbol:
  temporaries!_pair=Some(Vptr object offset)->temporaries!_index=Some(Vint(Int.repr index))->0<=index<2->
  Genv.find_symbol ge _leancage_host_fcntl=Some duplicate_symbol->
  Genv.find_funct_ptr ge duplicate_symbol=Some(gateway_spawn_signature gateway_fcntl_api)->
  Genv.find_symbol ge _close=Some close_symbol->
  Genv.find_funct_ptr ge close_symbol=Some(gateway_spawn_signature gateway_close_api)->
  (forall moved changed memory,4<=moved->changed!_pair=Some(Vptr object offset)->
    changed!_index=Some(Vint(Int.repr index))->
    gateway_setup_path backend ge result
      (pair_context(pair_slot_left index moved left)(pair_slot_right index moved right))
      (State f_host_private_pair Sskip pair_loop_cont empty_env changed memory))->
  gateway_setup_path backend ge result(pair_context left right)
    (State f_host_private_pair pair_low_body pair_loop_cont empty_env temporaries memory).
Proof.
  intros POINTER INDEX RANGE DUPLICATE_SYMBOL DUPLICATE_FUNCTION CLOSE_SYMBOL CLOSE_FUNCTION REST.
  set(old:=pair_slot_value index left right).
  set(changed_temps:=PTree.set _t'9(Vint(Int.repr old))temporaries).
  eapply gateway_setup_same with(next:=State f_host_private_pair pair_duplicate_sequence
    (Kseq pair_after_duplicate pair_loop_cont)empty_env temporaries memory);[apply pair_context_closed|cbn;tauto| |].
  { intros available current GOOD;apply unchanged_store_edge,edge_seq. }
  eapply gateway_setup_same with(next:=State f_host_private_pair pair_duplicate_prefix
    (Kseq pair_moved_set(Kseq pair_after_duplicate pair_loop_cont))empty_env temporaries memory);
    [apply pair_context_closed|cbn;tauto| |].
  { intros available current GOOD;apply unchanged_store_edge,edge_seq. }
  eapply gateway_setup_same with(next:=State f_host_private_pair pair_duplicate_load
    (Kseq pair_duplicate_call(Kseq pair_moved_set(Kseq pair_after_duplicate pair_loop_cont)))empty_env temporaries memory);
    [apply pair_context_closed|cbn;tauto| |].
  { intros available current GOOD;apply unchanged_store_edge,edge_seq. }
  eapply gateway_setup_same with(next:=State f_host_private_pair Sskip
    (Kseq pair_duplicate_call(Kseq pair_moved_set(Kseq pair_after_duplicate pair_loop_cont)))empty_env changed_temps memory);
    [apply pair_context_closed|cbn;tauto| |].
  { intros available current[[SIDE[PRIVATE[CELLS RESOURCES]]]HISTORY].
    apply certified_set_edge;eapply actual_pair_element_read;[exact POINTER|exact INDEX|exact RANGE| |].
    - exact(proj1(proj2(proj1(proj1 CELLS)))).
    - apply gateway_pair_selected_load;assumption. }
  eapply gateway_setup_same with(next:=State f_host_private_pair pair_duplicate_call
    (Kseq pair_moved_set(Kseq pair_after_duplicate pair_loop_cont))empty_env changed_temps memory);
    [apply pair_context_closed|cbn;tauto| |].
  { intros available current GOOD;apply unchanged_store_edge,edge_skip_seq. }
  eapply gateway_setup_same with(next:=Callstate(gateway_spawn_signature gateway_fcntl_api)
    [Vint(Int.repr old);Vint(Int.repr 1030);Vint(Int.repr 4)](pair_duplicate_cont changed_temps)memory);
    [apply pair_context_closed|cbn;tauto| |].
  { intros available current GOOD;eapply actual_pair_duplicate_call;
      [apply PTree.gss|exact DUPLICATE_SYMBOL|exact DUPLICATE_FUNCTION]. }
  eapply gateway_setup_external;[apply pair_context_closed|].
  intros called call_world returned after next observed CONTEXT OPERATION.
  assert(API:gateway_spawn_operation backend gateway_fcntl_api
    [Vint(Int.repr old);Vint(Int.repr 1030);Vint(Int.repr 4)]called call_world returned after next observed).
  { exists(gateway_spawn_signature gateway_fcntl_api);split;[apply actual_gateway_spawn_signatures|exact OPERATION]. }
  destruct(gateway_pair_slot_resources ipc identity left right index(resources call_world)
    (proj2(proj2(proj2(proj1 CONTEXT))))RANGE)as[WIDTH OWNED].
  destruct(gateway_duplicate_operation _ _ _ _ _ _ _ descriptors called call_world old 4(pair_slot_entry ipc identity index)
    returned after next observed(proj1(proj1 CONTEXT))(proj1(proj2(proj2(proj2(proj1 CONTEXT)))))OWNED ltac:(cbn;lia)API)
    as[SIDE[VALID[ACCESS[FRAME[EXCLUSIVE[IO[FAILED|[moved[RETURNED DUPLICATE]]]]]]]]].
  - destruct FAILED as[RETURNED[RESOURCES STATUS]];subst returned;exists(fun _ _=>True);split;[exact I|].
    change(Vint(Int.neg Int.one))with(Vint(Int.repr(-1))).
    eapply actual_pair_duplicate_tail_script;
      [unfold gateway_ambient_closed,gateway_runtime_discipline;intros;exact I|cbn;lia|].
    intros NONNEGATIVE;lia.
  - subst returned.
    destruct(actual_pair_duplicate_context left right index moved called call_world after next CONTEXT RANGE SIDE VALID ACCESS FRAME
      DUPLICATE EXCLUSIVE)as[MOVING[DIFFERENT MINIMUM]].
    exists(pair_before_close native_private discipline resources ipc identity object offset history left right
      (pair_slot_left index moved left)(pair_slot_right index moved right)old(pair_slot_entry ipc identity index));split;
      [exact MOVING|].
    eapply actual_pair_duplicate_tail_script.
    + apply pair_before_close_closed with(io:=io)(stable_readonly:=stable_readonly)(thread_errno:=thread_errno);
        assumption.
    + pose proof(gateway_duplicate_width _ _ _ _ _ _ DUPLICATE)as BOUND.
      change Int.min_signed with(-2147483648);lia.
    + intros NONNEGATIVE initial_memory.
      assert(SEPARATE:left<>right).
      { destruct CONTEXT as[[_[_[_[_[_[_[SEPARATE _]]]]]]]_];exact SEPARATE. }
      destruct(gateway_pair_replaced_other index left right moved RANGE SEPARATE DIFFERENT)as[LKEPT RKEPT].
      eapply actual_pair_close_store_script with(symbol:=close_symbol);try eassumption.
      * unfold pair_duplicate_temps,changed_temps;repeat rewrite PTree.gso by discriminate;exact POINTER.
      * unfold pair_duplicate_temps,changed_temps;repeat rewrite PTree.gso by discriminate;exact INDEX.
      * unfold pair_duplicate_temps;apply PTree.gss.
      * intros final_memory;apply REST;[exact MINIMUM| |].
        -- unfold pair_duplicate_temps,changed_temps;repeat rewrite PTree.gso by discriminate;exact POINTER.
        -- unfold pair_duplicate_temps,changed_temps;repeat rewrite PTree.gso by discriminate;exact INDEX.
Qed.
End PairDuplicate.
