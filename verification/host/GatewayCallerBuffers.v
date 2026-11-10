(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Uninitialized caller arrays retain permissions and roots across individual operations. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory.
From HostGateway Require Import GatewayThreadRuntime GatewayBufferReference GatewayScopeBufferReference.
Open Scope Z_scope.

Definition gateway_stable_reference {World}(stable_readonly:World->block->Z->Prop)
    before world after next:Prop:=
  forall object position,Mem.perm before object position Cur Readable->stable_readonly world object position->
    Mem.perm after object position Cur Readable /\stable_readonly next object position.

Lemma gateway_stable_reference_refl {World}(stable_readonly:World->block->Z->Prop)memory world:
  gateway_stable_reference stable_readonly memory world memory world.
Proof. intros object position READABLE STABLE;split;assumption. Qed.
Lemma gateway_stable_reference_transitive {World}(stable_readonly:World->block->Z->Prop)before world middle current after next:
  gateway_stable_reference stable_readonly before world middle current->
  gateway_stable_reference stable_readonly middle current after next->
  gateway_stable_reference stable_readonly before world after next.
Proof.
  intros FIRST SECOND object position READABLE STABLE;destruct(FIRST object position READABLE STABLE)as[READABLE' STABLE'];
    apply SECOND;assumption.
Qed.

Definition gateway_caller_readonly {World}(native_private:World->block->Prop)(stable_readonly:World->block->Z->Prop)
    (readonly:block->Z->Prop)(memory:mem)(world:World):Prop:=
  forall object position,readonly object position->Mem.valid_block memory object /\
    (native_private world object \/Mem.perm memory object position Cur Readable /\stable_readonly world object position).

Definition gateway_caller_buffers {World}(native_private:World->block->Prop)(stable_readonly:World->block->Z->Prop)
    (readonly:block->Z->Prop)target reference owner(memory:mem)(world:World):Prop:=
  Mem.valid_block memory target /\native_private world target /\
  gateway_caller_readonly native_private stable_readonly readonly memory world /\
  gateway_buffer_reference readonly target target reference memory /\
  gateway_native_reference native_private reference owner memory world /\
  gateway_stable_reference stable_readonly reference owner memory world.

Lemma gateway_caller_buffers_refl {World}(native_private:World->block->Prop)(stable_readonly:World->block->Z->Prop)
    readonly target memory world:
  Mem.valid_block memory target->native_private world target->
  gateway_caller_readonly native_private stable_readonly readonly memory world->
  gateway_caller_buffers native_private stable_readonly readonly target memory world memory world.
Proof.
  intros LIVE PRIVATE READONLY;split;[exact LIVE|]. split;[exact PRIVATE|]. split;[exact READONLY|].
  split;[apply gateway_buffer_reference_refl|]. split;[apply gateway_native_reference_refl|apply gateway_stable_reference_refl].
Qed.

Lemma gateway_caller_permission_frame {World}(native_private:World->block->Prop)(stable_readonly:World->block->Z->Prop)
    output before world after target:
  Mem.valid_block before target->native_private world target->
  gateway_native_frame native_private stable_readonly output world before after->
  (forall object position,{output object position}+{~output object position})->
  (forall position kind permission,output target position->
    (Mem.perm before target position kind permission<->Mem.perm after target position kind permission))->
  gateway_buffer_permissions target target before after.
Proof.
  intros LIVE PRIVATE FRAME DECISION OUTPUT object[OBJECT|OBJECT]position kind permission;subst object;
    destruct(DECISION target position)as[WRITTEN|NOT_WRITTEN].
  all:try solve[apply OUTPUT;exact WRITTEN].
  all:apply(Mem.unchanged_on_perm _ _ _ FRAME target position kind permission);
    [split;[left;exact PRIVATE|exact NOT_WRITTEN]|exact LIVE].
Qed.

Theorem gateway_caller_buffers_operation {World}(native_private:World->block->Prop)(stable_readonly:World->block->Z->Prop)
    readonly target reference owner before world after next output:
  gateway_caller_buffers native_private stable_readonly readonly target reference owner before world->
  gateway_access_retained native_private stable_readonly before world next->
  gateway_native_frame native_private stable_readonly output world before after->
  (forall object position,{output object position}+{~output object position})->
  (forall object position,readonly object position->~output object position)->
  (forall position kind permission,output target position->
    (Mem.perm before target position kind permission<->Mem.perm after target position kind permission))->
  (forall object position,Mem.perm before object position Cur Readable->output object position->
    Mem.perm after object position Cur Readable)->
  gateway_caller_buffers native_private stable_readonly readonly target reference owner after next.
Proof.
  intros[LIVE[PRIVATE[READONLY[BUFFER[NATIVE STABLE]]]]]ACCESS FRAME DECISION DISJOINT TARGET_PERMISSION OUTPUT_READABLE.
  assert(READONLY_FRAME:Mem.unchanged_on readonly before after).
  { eapply gateway_native_frame_restrict;[exact FRAME| |exact DISJOINT].
    intros object position HERE;destruct(READONLY object position HERE)as[VALID[OWNED|[READABLE IMMUTABLE]]];auto. }
  assert(LOCAL_NATIVE:gateway_native_reference native_private before world after next).
  { eapply gateway_native_reference_operation;[exact ACCESS|exact FRAME]. }
  assert(LOCAL_STABLE:gateway_stable_reference stable_readonly before world after next).
  { intros object position READABLE IMMUTABLE;split;[|apply(proj2 ACCESS);assumption].
    destruct(DECISION object position)as[WRITTEN|NOT_WRITTEN].
    - apply OUTPUT_READABLE;assumption.
    - eapply Mem.perm_unchanged_on;[exact FRAME| |exact READABLE]. split;[right;exact IMMUTABLE|exact NOT_WRITTEN]. }
  split;[exact(proj1(LOCAL_NATIVE target LIVE PRIVATE))|]. split;[exact(proj2(LOCAL_NATIVE target LIVE PRIVATE))|].
  split.
  - intros object position HERE;destruct(READONLY object position HERE)as[VALID[OWNED|[READABLE IMMUTABLE]]].
    + split;[exact(proj1(LOCAL_NATIVE object VALID OWNED))|left;exact(proj2(LOCAL_NATIVE object VALID OWNED))].
    + split;[eapply Mem.valid_block_unchanged_on;[exact FRAME|exact VALID]|].
      right;apply LOCAL_STABLE;assumption.
  - split.
    + eapply gateway_buffer_reference_transitive;[exact BUFFER|]. split;[exact READONLY_FRAME|].
      eapply gateway_caller_permission_frame;eassumption.
    + split.
      * eapply gateway_native_reference_transitive;[exact NATIVE|exact LOCAL_NATIVE].
      * eapply gateway_stable_reference_transitive;[exact STABLE|exact LOCAL_STABLE].
Qed.

Theorem gateway_caller_buffers_no_output {World}(native_private:World->block->Prop)(stable_readonly:World->block->Z->Prop)
    readonly target reference owner before world after next:
  gateway_caller_buffers native_private stable_readonly readonly target reference owner before world->
  gateway_access_retained native_private stable_readonly before world next->
  gateway_native_frame native_private stable_readonly gateway_native_no_output world before after->
  gateway_caller_buffers native_private stable_readonly readonly target reference owner after next.
Proof.
  intros HISTORY ACCESS FRAME;eapply gateway_caller_buffers_operation;
    [exact HISTORY|exact ACCESS|exact FRAME|intros;right;tauto|intros;tauto|intros;contradiction|intros;contradiction].
Qed.

Theorem gateway_caller_buffers_store {World}(native_private:World->block->Prop)(stable_readonly:World->block->Z->Prop)
    readonly target reference owner before world after chunk object position value:
  gateway_caller_buffers native_private stable_readonly readonly target reference owner before world->
  Mem.store chunk before object position value=Some after->(forall offset,~readonly object offset)->
  gateway_caller_buffers native_private stable_readonly readonly target reference owner after world.
Proof.
  intros[LIVE[PRIVATE[READONLY[BUFFER[NATIVE STABLE]]]]]STORE DISJOINT.
  destruct(gateway_scope_store_buffer native_private readonly target target before after world chunk object position value STORE DISJOINT)
    as[LOCAL_BUFFER LOCAL_NATIVE].
  split;[eapply Mem.store_valid_block_1;eassumption|]. split;[exact PRIVATE|].
  split.
  - intros other query HERE;destruct(READONLY other query HERE)as[VALID[OWNED|[READABLE IMMUTABLE]]];split;
      try solve[eapply Mem.store_valid_block_1;eassumption].
    + left;exact OWNED.
    + right;split;[eapply Mem.perm_store_1;eassumption|exact IMMUTABLE].
  - split;[eapply gateway_buffer_reference_transitive;[exact BUFFER|exact LOCAL_BUFFER]|].
    split;[eapply gateway_native_reference_transitive;[exact NATIVE|exact LOCAL_NATIVE]|].
    intros other query READABLE IMMUTABLE;destruct(STABLE other query READABLE IMMUTABLE)as[CURRENT RETAINED].
    split;[eapply Mem.perm_store_1;eassumption|exact RETAINED].
Qed.

Theorem gateway_caller_buffers_alloc {World}(native_private:World->block->Prop)(stable_readonly:World->block->Z->Prop)
    readonly target reference owner before world after object low high:
  gateway_caller_buffers native_private stable_readonly readonly target reference owner before world->
  Mem.alloc before low high=(after,object)->
  gateway_caller_buffers native_private stable_readonly readonly target reference owner after world.
Proof.
  intros[LIVE[PRIVATE[READONLY[BUFFER[NATIVE STABLE]]]]]ALLOC.
  destruct(gateway_scope_alloc_buffer native_private readonly target target before after world object low high ALLOC LIVE LIVE)
    as[LOCAL_BUFFER LOCAL_NATIVE].
  split;[eapply Mem.valid_block_alloc;eassumption|]. split;[exact PRIVATE|].
  split.
  - intros other query HERE;destruct(READONLY other query HERE)as[VALID[OWNED|[READABLE IMMUTABLE]]];split;
      try solve[eapply Mem.valid_block_alloc;eassumption].
    + left;exact OWNED.
    + right;split;[eapply Mem.perm_alloc_1;eassumption|exact IMMUTABLE].
  - split;[eapply gateway_buffer_reference_transitive;[exact BUFFER|exact LOCAL_BUFFER]|].
    split;[eapply gateway_native_reference_transitive;[exact NATIVE|exact LOCAL_NATIVE]|].
    intros other query READABLE IMMUTABLE;destruct(STABLE other query READABLE IMMUTABLE)as[CURRENT RETAINED].
    split;[eapply Mem.perm_alloc_1;eassumption|exact RETAINED].
Qed.

Theorem gateway_caller_buffers_free {World}(native_private:World->block->Prop)(stable_readonly:World->block->Z->Prop)
    readonly target reference owner before world after object low high:
  gateway_caller_buffers native_private stable_readonly readonly target reference owner before world->
  Mem.free before object low high=Some after->(forall offset,~readonly object offset)->object<>target->
  ~Mem.valid_block reference object->
  gateway_caller_buffers native_private stable_readonly readonly target reference owner after world.
Proof.
  intros[LIVE[PRIVATE[READONLY[BUFFER[NATIVE STABLE]]]]]FREE DISJOINT TARGET FRESH.
  destruct(gateway_scope_free_buffer native_private readonly target target before after world object low high
    FREE DISJOINT TARGET TARGET LIVE LIVE)as[LOCAL_BUFFER LOCAL_NATIVE].
  split;[eapply Mem.valid_block_free_1;eassumption|]. split;[exact PRIVATE|].
  split.
  - intros other query HERE;destruct(READONLY other query HERE)as[VALID[OWNED|[READABLE IMMUTABLE]]];split;
      try solve[eapply Mem.valid_block_free_1;eassumption].
    + left;exact OWNED.
    + right;split;[|exact IMMUTABLE]. eapply Mem.perm_free_1;[exact FREE| |exact READABLE].
      left;intro SAME;subst other;exact(DISJOINT query HERE).
  - split;[eapply gateway_buffer_reference_transitive;[exact BUFFER|exact LOCAL_BUFFER]|].
    split;[eapply gateway_native_reference_transitive;[exact NATIVE|exact LOCAL_NATIVE]|].
    intros other query READABLE IMMUTABLE;destruct(STABLE other query READABLE IMMUTABLE)as[CURRENT RETAINED].
    split;[|exact RETAINED]. eapply Mem.perm_free_1;[exact FREE| |exact CURRENT].
    left;intro SAME;subst other;apply FRESH;eapply Mem.perm_valid_block;exact READABLE.
Qed.
