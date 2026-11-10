(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: Source closes the old lease before storing the actual duplicated descriptor. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewaySpawnABI GatewaySpawnResources GatewaySpawnRuntime
  GatewayPairContext GatewayPairMemory GatewayPairStatements GatewayThreadRuntime GatewayFramedRuntime GatewaySetupPaths
  GatewayOperations GatewayFrames GatewayStreamInterface GatewayPairBuffers.
Import ListNotations.
Open Scope Z_scope.

Section PairMove.
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

Local Definition pair_storage left right selected_left selected_right:=
  gateway_pair_full_storage native_private discipline resources ipc identity object offset
    left right selected_left selected_right history.
Local Definition pair_aligned left right:=
  gateway_pair_full_context native_private discipline resources ipc identity object offset left right history.
Definition pair_before_close left right selected_left selected_right old entry(memory:mem)(world:World):Prop:=
  pair_storage left right selected_left selected_right memory world /\gateway_owned_descriptor(resources world)old entry.

Local Lemma pair_storage_closed left right selected_left selected_right:
  gateway_ambient_closed backend(pair_storage left right selected_left selected_right).
Proof. apply gateway_pair_full_storage_ambient with(io:=io)(stable_readonly:=stable_readonly)(thread_errno:=thread_errno);
  assumption. Qed.
Local Lemma pair_aligned_closed left right:gateway_ambient_closed backend(pair_aligned left right).
Proof. apply gateway_pair_full_context_ambient with(io:=io)(stable_readonly:=stable_readonly)(thread_errno:=thread_errno);
  assumption. Qed.
Lemma pair_before_close_closed left right selected_left selected_right old entry:
  gateway_ambient_closed backend(pair_before_close left right selected_left selected_right old entry).
Proof.
  intros before world after next[STORAGE OLD]INTERFERENCE;split.
  - exact(pair_storage_closed left right selected_left selected_right before world after next STORAGE INTERFERENCE).
  - destruct(gateway_spawn_ambient _ _ _ _ _ _ _ descriptors before world after next(proj1(proj1 STORAGE))
      (proj1(proj2(proj2(proj2(proj1 STORAGE)))))INTERFERENCE)as[VALID[FRAME REST]].
    eapply(proj1 FRAME);[exact OLD|tauto].
Qed.

Lemma actual_pair_slot_store temporaries before after index moved continuation:
  temporaries!_pair=Some(Vptr object offset)->temporaries!_index=Some(Vint(Int.repr index))->
  temporaries!_moved=Some(Vint(Int.repr moved))->0<=index<2->Ptrofs.unsigned offset+8<=Ptrofs.modulus->
  Mem.store Mint32 before object(Ptrofs.unsigned offset+4*index)(Vint(Int.repr moved))=Some after->
  store_edge ge(State f_host_private_pair pair_store continuation empty_env temporaries before)
    (State f_host_private_pair Sskip continuation empty_env temporaries after).
Proof.
  intros POINTER INDEX MOVED RANGE BOUND STORE.
  eapply assignment_source_edge with(b:=object)(ofs:=Ptrofs.add offset(Ptrofs.repr(4*index)))
    (v:=Vint(Int.repr moved))(w:=Vint(Int.repr moved)).
  - apply pointer_location_value;eapply actual_pair_element;[exact POINTER|exact INDEX|lia].
  - apply old_expression_value,value_temp;exact MOVED.
  - reflexivity.
  - eapply assign_loc_value;[reflexivity|]. unfold Mem.storev.
    rewrite Ptrofs.add_unsigned.
    rewrite(Ptrofs.unsigned_repr(4*index))by(change Ptrofs.max_unsigned with 18446744073709551615;lia).
    rewrite Ptrofs.unsigned_repr by(unfold Ptrofs.max_unsigned;pose proof(Ptrofs.unsigned_range offset);lia).
    rewrite zle_true by(change(Ptrofs.unsigned offset+4*index+4<=Ptrofs.modulus);lia);exact STORE.
Qed.

Theorem actual_pair_store_script left right index moved temporaries memory result:
  temporaries!_pair=Some(Vptr object offset)->temporaries!_index=Some(Vint(Int.repr index))->
  temporaries!_moved=Some(Vint(Int.repr moved))->0<=index<2->
  (forall memory,gateway_setup_path backend ge result
    (pair_aligned(pair_slot_left index moved left)(pair_slot_right index moved right))
    (State f_host_private_pair Sskip pair_loop_cont empty_env temporaries memory))->
  gateway_setup_path backend ge result
    (pair_storage left right(pair_slot_left index moved left)(pair_slot_right index moved right))
    (State f_host_private_pair pair_store pair_loop_cont empty_env temporaries memory).
Proof.
  intros POINTER INDEX MOVED RANGE REST.
  eapply gateway_setup_next with
    (next:=State f_host_private_pair Sskip pair_loop_cont empty_env temporaries memory)
    (middle:=pair_aligned(pair_slot_left index moved left)(pair_slot_right index moved right)).
  - apply pair_storage_closed.
  - cbn;tauto.
  - intros before world[[SIDE[PRIVATE[CELLS RESOURCES]]]HISTORY].
    destruct(gateway_pair_cell_store before object offset left right index moved CELLS RANGE)as[after[STORE FINAL]].
    exists after;split.
    + eapply actual_pair_slot_store;try eassumption;exact(proj1(proj2(proj1(proj1 CELLS)))).
    + split.
      * split;[eapply gateway_thread_native_store;eassumption|]. split;[exact PRIVATE|]. split;assumption.
      * eapply gateway_pair_buffer_store;[exact buffers|exact HISTORY|exact STORE].
  - apply REST.
Qed.

Theorem actual_pair_close_store_script left right index moved temporaries memory result symbol:
  temporaries!_pair=Some(Vptr object offset)->temporaries!_index=Some(Vint(Int.repr index))->
  temporaries!_moved=Some(Vint(Int.repr moved))->0<=index<2->
  pair_slot_left index moved left<>pair_slot_value index left right->
  pair_slot_right index moved right<>pair_slot_value index left right->
  Genv.find_symbol ge _close=Some symbol->
  Genv.find_funct_ptr ge symbol=Some(gateway_spawn_signature gateway_close_api)->
  (forall memory,gateway_setup_path backend ge result
    (pair_aligned(pair_slot_left index moved left)(pair_slot_right index moved right))
    (State f_host_private_pair Sskip pair_loop_cont empty_env
      (PTree.set _t'6(Vint(Int.repr(pair_slot_value index left right)))temporaries)memory))->
  gateway_setup_path backend ge result
    (pair_before_close left right(pair_slot_left index moved left)(pair_slot_right index moved right)
      (pair_slot_value index left right)(pair_slot_entry ipc identity index))
    (State f_host_private_pair pair_replacement pair_loop_cont empty_env temporaries memory).
Proof.
  intros POINTER INDEX MOVED RANGE LEFT_DIFFERENT RIGHT_DIFFERENT SYMBOL FUNCTION REST.
  set(old:=pair_slot_value index left right).
  set(moving:=pair_before_close left right(pair_slot_left index moved left)(pair_slot_right index moved right)
    old(pair_slot_entry ipc identity index)).
  set(changed_temps:=PTree.set _t'6(Vint(Int.repr old))temporaries).
  assert(PATH:forall initial_memory,gateway_setup_path backend ge result moving
    (State f_host_private_pair pair_replacement pair_loop_cont empty_env temporaries initial_memory)).
  { intro initial_memory.
    eapply gateway_setup_same with(next:=State f_host_private_pair pair_close_prefix(Kseq pair_store pair_loop_cont)
      empty_env temporaries initial_memory);[apply pair_before_close_closed|cbn;tauto| |].
    { intros available current GOOD;apply unchanged_store_edge,edge_seq. }
    eapply gateway_setup_same with(next:=State f_host_private_pair pair_close_load
      (Kseq pair_close_call(Kseq pair_store pair_loop_cont))empty_env temporaries initial_memory);
      [apply pair_before_close_closed|cbn;tauto| |].
    { intros available current GOOD;apply unchanged_store_edge,edge_seq. }
    eapply gateway_setup_same with(next:=State f_host_private_pair Sskip
      (Kseq pair_close_call(Kseq pair_store pair_loop_cont))empty_env changed_temps initial_memory);
      [apply pair_before_close_closed|cbn;tauto| |].
    { intros available current[[[SIDE[PRIVATE[CELLS RESOURCES]]]HISTORY]OLD].
      apply certified_set_edge;eapply actual_pair_element_read;[exact POINTER|exact INDEX|exact RANGE| |].
      - exact(proj1(proj2(proj1(proj1 CELLS)))).
      - eapply gateway_pair_selected_load;eassumption. }
    eapply gateway_setup_same with(next:=State f_host_private_pair pair_close_call(Kseq pair_store pair_loop_cont)
      empty_env changed_temps initial_memory);[apply pair_before_close_closed|cbn;tauto| |].
    { intros available current GOOD;apply unchanged_store_edge,edge_skip_seq. }
    eapply gateway_setup_same with(next:=Callstate(gateway_spawn_signature gateway_close_api)[Vint(Int.repr old)]
      (Kcall None f_host_private_pair empty_env changed_temps(Kseq pair_store pair_loop_cont))initial_memory);
      [apply pair_before_close_closed|cbn;tauto| |].
    { intros available current GOOD;eapply actual_pair_close_call;[apply PTree.gss|exact SYMBOL|exact FUNCTION]. }
    eapply gateway_setup_external.
    - apply pair_before_close_closed.
    - intros called call_world returned after next observed[STORAGE OLD]OPERATION.
      assert(API:gateway_spawn_operation backend gateway_close_api[Vint(Int.repr old)]
        called call_world returned after next observed).
      { exists(gateway_spawn_signature gateway_close_api);split;[apply actual_gateway_spawn_signatures|exact OPERATION]. }
      destruct(gateway_close_operation _ _ _ _ _ _ _ descriptors called call_world old(pair_slot_entry ipc identity index)
        returned after next observed(proj1(proj1 STORAGE))(proj1(proj2(proj2(proj2(proj1 STORAGE)))))OLD API)
        as[RETURNED[SIDE[VALID[ACCESS[FRAME[CLOSED[RESOURCES[STATUS[EXCLUSIVE IO]]]]]]]]].
      exists(pair_storage left right(pair_slot_left index moved left)(pair_slot_right index moved right));split.
      + eapply gateway_pair_full_storage_preserved;try eassumption.
        -- intros fd previous PREVIOUS SAME;subst fd.
           eapply gateway_pair_selected_lease_new;[exact(proj2(proj2(proj2(proj1 STORAGE))))|exact RANGE|exact OLD|exact PREVIOUS].
      + eapply gateway_setup_same with(next:=State f_host_private_pair Sskip(Kseq pair_store pair_loop_cont)
          empty_env changed_temps after);[apply pair_storage_closed|cbn;tauto| |].
        { intros available current GOOD;apply unchanged_store_edge,edge_returnstate. }
        eapply gateway_setup_same with(next:=State f_host_private_pair pair_store pair_loop_cont
          empty_env changed_temps after);[apply pair_storage_closed|cbn;tauto| |].
        { intros available current GOOD;apply unchanged_store_edge,edge_skip_seq. }
        eapply actual_pair_store_script;[| | |exact RANGE|exact REST];
          unfold changed_temps;rewrite PTree.gso by discriminate;assumption.
  }
  apply PATH.
Qed.
End PairMove.
