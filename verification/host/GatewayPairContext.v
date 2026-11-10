(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: Pair normalization retains the actual IPC object and open-description identities. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory.
From HostGateway Require Import GatewayMachine GatewayOperations GatewayThreadRuntime GatewayStreamInterface
  GatewaySpawnResources GatewaySpawnRuntime GatewayPairHistory.
Open Scope Z_scope.

Record gateway_pair_identity(ipc:nat->Prop):Type:={
  pair_left_object:nat;
  pair_right_object:nat;
  pair_left_description:nat;
  pair_right_description:nat;
  pair_objects_separate:pair_left_object<>pair_right_object;
  pair_descriptions_separate:pair_left_description<>pair_right_description;
  pair_left_ipc:ipc pair_left_object;
  pair_right_ipc:ipc pair_right_object;
  pair_origin:gateway_resource_state;
  pair_left_fresh:gateway_resource_objects pair_origin pair_left_object=false;
  pair_right_fresh:gateway_resource_objects pair_origin pair_right_object=false
}.

Definition pair_left_entry ipc(identity:gateway_pair_identity ipc):gateway_resource_descriptor:=
  gateway_socket_descriptor(pair_left_object _ identity)(pair_left_description _ identity).
Definition pair_right_entry ipc(identity:gateway_pair_identity ipc):gateway_resource_descriptor:=
  gateway_socket_descriptor(pair_right_object _ identity)(pair_right_description _ identity).

Definition gateway_pair_resources ipc(identity:gateway_pair_identity ipc)left right(state:gateway_resource_state):Prop:=
  gateway_resource_valid state /\0<=left<=Int.max_signed /\0<=right<=Int.max_signed /\left<>right /\
  gateway_owned_descriptor state left(pair_left_entry ipc identity) /\
  gateway_owned_descriptor state right(pair_right_entry ipc identity) /\
  gateway_resource_exclusive state(pair_left_description _ identity)=true /\
  gateway_resource_exclusive state(pair_right_description _ identity)=true /\
  gateway_resource_nonblocking state(pair_left_description _ identity)=true /\
  gateway_resource_nonblocking state(pair_right_description _ identity)=true /\
  gateway_resource_peer state(pair_left_object _ identity)=Some(pair_right_object _ identity) /\
  gateway_resource_peer state(pair_right_object _ identity)=Some(pair_left_object _ identity) /\
  gateway_resource_valid(pair_origin _ identity) /\gateway_resource_reference(pair_origin _ identity)state.

Definition gateway_pair_cells(memory:mem)object offset left right:Prop:=
  gateway_pair_output_cells memory object offset /\
  Mem.load Mint32 memory object(Ptrofs.unsigned offset)=Some(Vint(Int.repr left)) /\
  Mem.load Mint32 memory object(Ptrofs.unsigned offset+4)=Some(Vint(Int.repr right)).

Lemma gateway_pair_original_valid ipc(identity:gateway_pair_identity ipc)left right state:
  gateway_pair_resources ipc identity left right state->gateway_resource_valid(pair_origin _ identity).
Proof. unfold gateway_pair_resources;tauto. Qed.
Lemma gateway_pair_original_reference ipc(identity:gateway_pair_identity ipc)left right state:
  gateway_pair_resources ipc identity left right state->gateway_resource_reference(pair_origin _ identity)state.
Proof. unfold gateway_pair_resources;tauto. Qed.

Definition gateway_pair_context {World}native_private(discipline:option val->mem->World->Prop)(resources:World->gateway_resource_state)
    ipc(identity:gateway_pair_identity ipc)object offset left right(memory:mem)(world:World):Prop:=
  discipline None memory world /\native_private world object /\
  gateway_pair_cells memory object offset left right /\gateway_pair_resources ipc identity left right(resources world).

Lemma gateway_pair_output_cells_permissions before after object offset:
  gateway_pair_output_cells before object offset->gateway_native_permissions before after object offset 8->
  gateway_pair_output_cells after object offset.
Proof.
  intros[[LENGTH[BOUND[LIVE RANGE]]][FIRST SECOND]]PERMISSIONS.
  assert(POINT:Mem.perm after object(Ptrofs.unsigned offset)Cur Writable).
  { apply(proj1(PERMISSIONS(Ptrofs.unsigned offset)Cur Writable ltac:(lia)));apply RANGE;lia. }
  split.
  - repeat split;try assumption.
    + eapply Mem.perm_valid_block;exact POINT.
    + intros position INSIDE;apply(proj1(PERMISSIONS position Cur Writable INSIDE));apply RANGE;exact INSIDE.
  - split.
    + destruct FIRST as[ACCESS ALIGN];split;[|exact ALIGN].
      intros position INSIDE;apply(proj1(PERMISSIONS position Cur Writable ltac:(cbn in INSIDE;lia)));apply ACCESS;exact INSIDE.
    + destruct SECOND as[ACCESS ALIGN];split;[|exact ALIGN].
      intros position INSIDE;apply(proj1(PERMISSIONS position Cur Writable ltac:(cbn in INSIDE;lia)));apply ACCESS;exact INSIDE.
Qed.

Lemma gateway_pair_output_cells_unchanged before after object offset:
  gateway_pair_output_cells before object offset->
  Mem.unchanged_on(gateway_native_region object offset 8)before after->gateway_pair_output_cells after object offset.
Proof.
  intros CELLS FRAME;eapply gateway_pair_output_cells_permissions;[exact CELLS|].
  intros position kind permission INSIDE;eapply Mem.unchanged_on_perm;[exact FRAME| |].
  - split;[reflexivity|exact INSIDE].
  - exact(proj1(proj2(proj2(proj1 CELLS)))).
Qed.

Lemma gateway_pair_cells_live memory object offset left right:
  gateway_pair_cells memory object offset left right->Mem.valid_block memory object.
Proof. intros[[[_[_[LIVE _]]]_ ]_];exact LIVE. Qed.

Lemma gateway_pair_cells_unchanged before after object offset left right:
  gateway_pair_cells before object offset left right->
  Mem.unchanged_on(gateway_native_region object offset 8)before after->
  gateway_pair_cells after object offset left right.
Proof.
  intros[[[LENGTH[BOUND[LIVE PERMISSIONS]]][FIRST SECOND]][LEFT RIGHT]]FRAME.
  assert(VALID:Mem.valid_block after object)by(eapply Mem.valid_block_unchanged_on;eassumption).
  split.
  - split.
    + repeat split;try assumption.
      intros position RANGE;eapply Mem.perm_unchanged_on;[exact FRAME| |apply PERMISSIONS;exact RANGE].
      split;[reflexivity|exact RANGE].
    + split.
      * destruct FIRST as[ACCESS ALIGN];split;[|exact ALIGN].
        intros position RANGE;eapply Mem.perm_unchanged_on;[exact FRAME| |apply ACCESS;exact RANGE].
        split;[reflexivity|cbn in RANGE;lia].
      * destruct SECOND as[ACCESS ALIGN];split;[|exact ALIGN].
        intros position RANGE;eapply Mem.perm_unchanged_on;[exact FRAME| |apply ACCESS;exact RANGE].
        split;[reflexivity|cbn in RANGE;lia].
  - split.
    + eapply Mem.load_unchanged_on;[exact FRAME| |exact LEFT].
      intros position RANGE;split;[reflexivity|cbn in RANGE;lia].
    + eapply Mem.load_unchanged_on;[exact FRAME| |exact RIGHT].
      intros position RANGE;split;[reflexivity|cbn in RANGE;lia].
Qed.

Lemma gateway_pair_resources_framed ipc(identity:gateway_pair_identity ipc)left right before after:
  gateway_pair_resources ipc identity left right before->gateway_resource_valid after->
  gateway_resource_frame before after(fun _=>False)(fun _=>False)->
  gateway_resource_status_frame before after(fun _=>False)->gateway_exclusive_kept before after->
  gateway_pair_resources ipc identity left right after.
Proof.
  intros[VALID[LBOUND[RBOUND[SEPARATE[LEFT[RIGHT[LEX[REX[LNON[RNON[LPEER[RPEER[ORIGIN_VALID REFERENCE]]]]]]]]]]]]]AFTER
    FRAME STATUS EXCLUSIVE.
  assert(LEFT_OBJECT:gateway_resource_objects before(pair_left_object _ identity)=true).
  { destruct VALID as[_ DESCRIPTORS];destruct LEFT as[_ ENTRY];
      destruct(DESCRIPTORS _ _ ENTRY)as[_[OBJECT _]];exact OBJECT. }
  assert(RIGHT_OBJECT:gateway_resource_objects before(pair_right_object _ identity)=true).
  { destruct VALID as[_ DESCRIPTORS];destruct RIGHT as[_ ENTRY];
      destruct(DESCRIPTORS _ _ ENTRY)as[_[OBJECT _]];exact OBJECT. }
  split;[exact AFTER|]. split;[exact LBOUND|]. split;[exact RBOUND|]. split;[exact SEPARATE|].
  split;[eapply(proj1 FRAME);[exact LEFT|tauto]|].
  split;[eapply(proj1 FRAME);[exact RIGHT|tauto]|].
  split;[apply EXCLUSIVE;exact LEX|]. split;[apply EXCLUSIVE;exact REX|].
  split.
  - pose proof(STATUS _ _ LEFT LEX ltac:(tauto))as SAME.
    change(gateway_resource_nonblocking after(pair_left_description _ identity)=
      gateway_resource_nonblocking before(pair_left_description _ identity))in SAME.
    rewrite SAME;exact LNON.
  - split.
    + pose proof(STATUS _ _ RIGHT REX ltac:(tauto))as SAME.
      change(gateway_resource_nonblocking after(pair_right_description _ identity)=
        gateway_resource_nonblocking before(pair_right_description _ identity))in SAME.
      rewrite SAME;exact RNON.
    + split.
      * destruct FRAME as[_[_[_[_ PEERS]]]];apply PEERS;assumption.
      * split;[destruct FRAME as[_[_[_[_ PEERS]]]];apply PEERS;assumption|].
        split;[exact ORIGIN_VALID|]. eapply gateway_resource_reference_step;
          [exact REFERENCE|exact FRAME|intros;tauto|exact STATUS|exact EXCLUSIVE].
Qed.

Lemma gateway_pair_resources_retained ipc(identity:gateway_pair_identity ipc)left right before after removed added:
  gateway_pair_resources ipc identity left right before->gateway_resource_valid after->
  gateway_resource_frame before after removed added->~removed left->~removed right->
  (forall fd entry,gateway_owned_descriptor(pair_origin _ identity)fd entry->~removed fd)->
  gateway_resource_status_frame before after(fun _=>False)->gateway_exclusive_kept before after->
  gateway_pair_resources ipc identity left right after.
Proof.
  intros[VALID[LBOUND[RBOUND[SEPARATE[LEFT[RIGHT[LEX[REX[LNON[RNON[LPEER[RPEER[ORIGIN_VALID REFERENCE]]]]]]]]]]]]]AFTER
    FRAME LKEPT RKEPT ORIGINAL_KEPT STATUS EXCLUSIVE.
  assert(LEFT_OBJECT:gateway_resource_objects before(pair_left_object _ identity)=true).
  { destruct VALID as[_ DESCRIPTORS];destruct LEFT as[_ ENTRY];
      destruct(DESCRIPTORS _ _ ENTRY)as[_[OBJECT _]];exact OBJECT. }
  assert(RIGHT_OBJECT:gateway_resource_objects before(pair_right_object _ identity)=true).
  { destruct VALID as[_ DESCRIPTORS];destruct RIGHT as[_ ENTRY];
      destruct(DESCRIPTORS _ _ ENTRY)as[_[OBJECT _]];exact OBJECT. }
  split;[exact AFTER|]. split;[exact LBOUND|]. split;[exact RBOUND|]. split;[exact SEPARATE|].
  split;[eapply(proj1 FRAME);[exact LEFT|exact LKEPT]|].
  split;[eapply(proj1 FRAME);[exact RIGHT|exact RKEPT]|].
  split;[apply EXCLUSIVE;exact LEX|]. split;[apply EXCLUSIVE;exact REX|].
  split.
  - pose proof(STATUS _ _ LEFT LEX ltac:(tauto))as SAME.
    change(gateway_resource_nonblocking after(pair_left_description _ identity)=
      gateway_resource_nonblocking before(pair_left_description _ identity))in SAME.
    rewrite SAME;exact LNON.
  - split.
    + pose proof(STATUS _ _ RIGHT REX ltac:(tauto))as SAME.
      change(gateway_resource_nonblocking after(pair_right_description _ identity)=
        gateway_resource_nonblocking before(pair_right_description _ identity))in SAME.
      rewrite SAME;exact RNON.
    + split.
      * destruct FRAME as[_[_[_[_ PEERS]]]];apply PEERS;assumption.
      * split;[destruct FRAME as[_[_[_[_ PEERS]]]];apply PEERS;assumption|].
        split;[exact ORIGIN_VALID|]. eapply gateway_resource_reference_step;
          [exact REFERENCE|exact FRAME|exact ORIGINAL_KEPT|exact STATUS|exact EXCLUSIVE].
Qed.

Lemma gateway_pair_resources_duplicate_left ipc(identity:gateway_pair_identity ipc)left right moved before after:
  gateway_pair_resources ipc identity left right before->gateway_resource_valid after->
  gateway_duplicate_receipt before after left 4 moved(pair_left_entry ipc identity)->
  gateway_exclusive_kept before after->gateway_pair_resources ipc identity moved right after /\moved<>left.
Proof.
  intros RESOURCES VALID DUPLICATE EXCLUSIVE.
  pose proof(gateway_pair_resources_retained ipc identity left right before after(fun _=>False)(fun fd=>fd=moved)
    RESOURCES VALID(gateway_duplicate_frame _ _ _ _ _ _ DUPLICATE)ltac:(tauto)ltac:(tauto)ltac:(intros;tauto)
    (gateway_duplicate_status _ _ _ _ _ _ DUPLICATE)EXCLUSIVE)as FRAMED.
  destruct FRAMED as[AFTER[LBOUND[RBOUND[SEPARATE[LEFT[RIGHT[LEX[REX[LNON[RNON[LPEER[RPEER[ORIGIN_VALID REFERENCE]]]]]]]]]]]]].
  destruct RESOURCES as[ORIGINAL[_[_[_[_[OLD_RIGHT _]]]]]].
  assert(MOVED_NE_RIGHT:moved<>right).
  { intro SAME;subst moved;destruct OLD_RIGHT as[OWNED _];
      rewrite(gateway_duplicate_unleased _ _ _ _ _ _ DUPLICATE)in OWNED;discriminate. }
  split;[|eapply gateway_duplicate_slot_distinct;exact DUPLICATE].
  split;[exact AFTER|]. split;[pose proof(gateway_duplicate_width _ _ _ _ _ _ DUPLICATE);lia|].
  split;[exact RBOUND|]. split;[exact MOVED_NE_RIGHT|].
  split;[exact(gateway_duplicate_live _ _ _ _ _ _ DUPLICATE)|].
  split;[exact RIGHT|]. repeat first[assumption|split].
Qed.

Lemma gateway_pair_resources_duplicate_right ipc(identity:gateway_pair_identity ipc)left right moved before after:
  gateway_pair_resources ipc identity left right before->gateway_resource_valid after->
  gateway_duplicate_receipt before after right 4 moved(pair_right_entry ipc identity)->
  gateway_exclusive_kept before after->gateway_pair_resources ipc identity left moved after /\moved<>right.
Proof.
  intros RESOURCES VALID DUPLICATE EXCLUSIVE.
  pose proof(gateway_pair_resources_retained ipc identity left right before after(fun _=>False)(fun fd=>fd=moved)
    RESOURCES VALID(gateway_duplicate_frame _ _ _ _ _ _ DUPLICATE)ltac:(tauto)ltac:(tauto)ltac:(intros;tauto)
    (gateway_duplicate_status _ _ _ _ _ _ DUPLICATE)EXCLUSIVE)as FRAMED.
  destruct FRAMED as[AFTER[LBOUND[RBOUND[SEPARATE[LEFT[RIGHT[LEX[REX[LNON[RNON[LPEER[RPEER[ORIGIN_VALID REFERENCE]]]]]]]]]]]]].
  destruct RESOURCES as[ORIGINAL[_[_[_[OLD_LEFT _]]]]].
  assert(LEFT_NE_MOVED:left<>moved).
  { intro SAME;subst moved;destruct OLD_LEFT as[OWNED _];
      rewrite(gateway_duplicate_unleased _ _ _ _ _ _ DUPLICATE)in OWNED;discriminate. }
  split;[|eapply gateway_duplicate_slot_distinct;exact DUPLICATE].
  split;[exact AFTER|]. split;[exact LBOUND|].
  split;[pose proof(gateway_duplicate_width _ _ _ _ _ _ DUPLICATE);lia|].
  split;[exact LEFT_NE_MOVED|]. split;[exact LEFT|].
  split;[exact(gateway_duplicate_live _ _ _ _ _ _ DUPLICATE)|]. repeat first[assumption|split].
Qed.

Definition gateway_pair_storage_context {World}native_private(discipline:option val->mem->World->Prop)
    (resources:World->gateway_resource_state)ipc(identity:gateway_pair_identity ipc)object offset
    stored_left stored_right left right(memory:mem)(world:World):Prop:=
  discipline None memory world /\native_private world object /\
  gateway_pair_cells memory object offset stored_left stored_right /\
  gateway_pair_resources ipc identity left right(resources world).

Lemma gateway_pair_storage_preserved {World}(native_private:World->block->Prop)stable_readonly discipline resources ipc
    (identity:gateway_pair_identity ipc)object offset stored_left stored_right left right before world after next removed added:
  gateway_pair_storage_context native_private discipline resources ipc identity object offset
    stored_left stored_right left right before world->
  discipline None after next->gateway_access_retained native_private stable_readonly before world next->
  gateway_native_frame native_private stable_readonly gateway_native_no_output world before after->
  gateway_resource_valid(resources next)->gateway_resource_frame(resources world)(resources next)removed added->
  ~removed left->~removed right->gateway_resource_status_frame(resources world)(resources next)(fun _=>False)->
  (forall fd entry,gateway_owned_descriptor(pair_origin _ identity)fd entry->~removed fd)->
  gateway_exclusive_kept(resources world)(resources next)->
  gateway_pair_storage_context native_private discipline resources ipc identity object offset
    stored_left stored_right left right after next.
Proof.
  intros[SIDE[PRIVATE[CELLS RESOURCES]]]NEXT[NATIVE STABLE]MEMORY VALID FRAME LKEPT RKEPT STATUS ORIGINAL_KEPT EXCLUSIVE.
  split;[exact NEXT|]. split.
  - apply NATIVE;[eapply gateway_pair_cells_live;exact CELLS|exact PRIVATE].
  - split.
    + eapply gateway_pair_cells_unchanged;[exact CELLS|].
      eapply gateway_native_frame_restrict;[exact MEMORY| |].
      * intros block position[SAME RANGE];subst block;left;exact PRIVATE.
      * intros block position RANGE FALSE;exact FALSE.
    + eapply gateway_pair_resources_retained;eassumption.
Qed.

Lemma gateway_pair_storage_ambient {World Event}(backend:gateway_backend World Event)io native_private stable_readonly
    discipline thread_errno resources ipc
    (runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno)
    (descriptors:gateway_spawn_descriptor_runtime backend io native_private stable_readonly discipline resources ipc)
    (identity:gateway_pair_identity ipc)object offset stored_left stored_right left right:
  gateway_runtime_discipline backend(gateway_pair_storage_context native_private discipline resources ipc identity object offset
    stored_left stored_right left right).
Proof.
  intros before world after next CONTEXT INTERFERENCE.
  destruct(gateway_thread_ambient _ _ _ _ _ _ runtime None before world after next(proj1 CONTEXT)INTERFERENCE)
    as[SIDE[ACCESS MEMORY]].
  assert(VALID:gateway_resource_valid(resources world))by(exact(proj1(proj2(proj2(proj2 CONTEXT))))).
  destruct(gateway_spawn_ambient _ _ _ _ _ _ _ descriptors before world after next(proj1 CONTEXT)VALID INTERFERENCE)
    as[AFTER[FRAME[STATUS EXCLUSIVE]]].
  eapply gateway_pair_storage_preserved;try eassumption;tauto.
Qed.

Lemma gateway_pair_context_preserved {World}(native_private:World->block->Prop)stable_readonly discipline resources ipc
    (identity:gateway_pair_identity ipc)object offset left right before world after next:
  gateway_pair_context native_private discipline resources ipc identity object offset left right before world->
  discipline None after next->gateway_access_retained native_private stable_readonly before world next->
  gateway_native_frame native_private stable_readonly gateway_native_no_output world before after->
  gateway_resource_valid(resources next)->
  gateway_resource_frame(resources world)(resources next)(fun _=>False)(fun _=>False)->
  gateway_resource_status_frame(resources world)(resources next)(fun _=>False)->
  gateway_exclusive_kept(resources world)(resources next)->
  gateway_pair_context native_private discipline resources ipc identity object offset left right after next.
Proof.
  intros[SIDE[PRIVATE[CELLS RESOURCES]]]NEXT[NATIVE STABLE]MEMORY VALID FRAME STATUS EXCLUSIVE.
  split;[exact NEXT|]. split.
  - apply NATIVE;[eapply gateway_pair_cells_live;exact CELLS|exact PRIVATE].
  - split.
    + eapply gateway_pair_cells_unchanged;[exact CELLS|].
      eapply gateway_native_frame_restrict;[exact MEMORY| |].
      * intros block position[SAME RANGE];subst block;left;exact PRIVATE.
      * intros block position RANGE FALSE;exact FALSE.
    + eapply gateway_pair_resources_framed;eassumption.
Qed.

Lemma gateway_pair_context_ambient {World Event}(backend:gateway_backend World Event)io native_private stable_readonly
    discipline thread_errno resources ipc
    (runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno)
    (descriptors:gateway_spawn_descriptor_runtime backend io native_private stable_readonly discipline resources ipc)
    (identity:gateway_pair_identity ipc)object offset left right:
  gateway_runtime_discipline backend
    (gateway_pair_context native_private discipline resources ipc identity object offset left right).
Proof.
  intros before world after next CONTEXT INTERFERENCE.
  destruct(gateway_thread_ambient _ _ _ _ _ _ runtime None before world after next(proj1 CONTEXT)INTERFERENCE)
    as[SIDE[ACCESS MEMORY]].
  assert(VALID:gateway_resource_valid(resources world))by(exact(proj1(proj2(proj2(proj2 CONTEXT))))).
  destruct(gateway_spawn_ambient _ _ _ _ _ _ _ descriptors before world after next(proj1 CONTEXT)VALID INTERFERENCE)
    as[AFTER[FRAME[STATUS EXCLUSIVE]]].
  eapply gateway_pair_context_preserved;eassumption.
Qed.

Definition gateway_pair_receipt_identity ipc before after(receipt:gateway_socketpair_receipt ipc before after):
    gateway_pair_identity ipc:=
  {|pair_left_object:=gateway_pair_left_object _ _ _ receipt;
    pair_right_object:=gateway_pair_right_object _ _ _ receipt;
    pair_left_description:=gateway_pair_left_description _ _ _ receipt;
    pair_right_description:=gateway_pair_right_description _ _ _ receipt;
    pair_objects_separate:=gateway_pair_objects_separate _ _ _ receipt;
    pair_descriptions_separate:=gateway_pair_descriptions_separate _ _ _ receipt;
    pair_left_ipc:=gateway_pair_left_ipc _ _ _ receipt;
    pair_right_ipc:=gateway_pair_right_ipc _ _ _ receipt;
    pair_origin:=before;
    pair_left_fresh:=gateway_pair_left_fresh _ _ _ receipt;
    pair_right_fresh:=gateway_pair_right_fresh _ _ _ receipt|}.

Lemma gateway_pair_receipt_resources ipc before after(receipt:gateway_socketpair_receipt ipc before after):
  gateway_resource_valid before->gateway_resource_valid after->gateway_exclusive_kept before after->
  gateway_pair_resources ipc(gateway_pair_receipt_identity ipc before after receipt)
    (gateway_pair_left _ _ _ receipt)(gateway_pair_right _ _ _ receipt)after.
Proof.
  intros BEFORE VALID EXCLUSIVE;split;[exact VALID|]. split;[apply gateway_pair_left_width|].
  split;[apply gateway_pair_right_width|]. split;[apply gateway_pair_slots_separate|].
  split;[apply gateway_pair_left_live|]. split;[apply gateway_pair_right_live|].
  split;[apply gateway_pair_left_exclusive|]. split;[apply gateway_pair_right_exclusive|].
  split;[apply gateway_pair_left_nonblocking|]. split;[apply gateway_pair_right_nonblocking|].
  split;[apply gateway_pair_left_connected|]. split;[apply gateway_pair_right_connected|].
  split;[exact BEFORE|]. eapply gateway_resource_reference_from_frame;
    [exact(gateway_pair_other_leases _ _ _ receipt)|intros;tauto|
     exact(gateway_pair_other_status _ _ _ receipt)|exact EXCLUSIVE].
Qed.
