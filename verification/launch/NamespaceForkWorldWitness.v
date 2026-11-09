(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.acceptance: One actual source fork has private tables and freshly empty queues. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers Values.
Require Import Machine LibraryMachine ProcessEffects.
From EntryNative Require Import NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine.
From EntryNamespace Require Import NamespaceMachine NamespacePaths NamespaceObjects NamespaceKernel
  NamespaceWorldTrace NamespaceChannel NamespaceQueue NamespaceFork NamespaceForkWitness.
Import ListNotations.
Open Scope Z_scope.

Definition fork_fixture_parent:TaskIdentity:=
  {|task_pid:=Int.one;task_incarnation:=0|}.
Definition fork_fixture_child:TaskIdentity:=
  {|task_pid:=Int.repr 2;task_incarnation:=0|}.
Definition fork_fixture_ordinary(descriptor:int):option DescriptorBinding:=
  if (Z.leb 0(Int.signed descriptor)&&Z.leb(Int.signed descriptor)8)%bool then
    Some{|descriptor_object:=ordinary_object(if (Int.eq descriptor Int.zero||Int.eq descriptor(Int.repr 2))%bool
        then 333 else 96+Z.to_nat(Int.signed descriptor));
      descriptor_cloexec:=negb((Int.eq descriptor Int.zero||Int.eq descriptor(Int.repr 2))%bool)|}
  else None.
Definition fork_fixture_other(descriptor:int):option DescriptorBinding:=
  if (Z.leb 0(Int.signed descriptor)&&Z.leb(Int.signed descriptor)2)%bool then
    Some{|descriptor_object:=ordinary_object(200+Z.to_nat(Int.signed descriptor));
      descriptor_cloexec:=true|}
  else None.
Definition fork_fixture_initial:NamespaceWorld:=
  {|namespace_task:=fork_fixture_parent;namespace_parent:=None;namespace_table_identity:=1;
    namespace_table:=fork_fixture_ordinary;namespace_ambient:=[fork_fixture_other];
    namespace_sigchld:={|action_handler:=Int64.one;action_flags:=Int64.repr 2;
      action_restorer:=Int64.zero;action_mask:=Int64.zero|};
    namespace_signal_mask:=Int64.zero|}.
Definition fork_fixture_paired:=table_put(table_put fork_fixture_ordinary(Int.repr 9)
  (endpoint_binding 60 parent_endpoint))(Int.repr 10)(endpoint_binding 60 child_endpoint).
Definition fork_fixture_duplicated:=table_put fork_fixture_paired(Int.repr 60)
  (endpoint_binding 60 child_endpoint).
Definition fork_fixture_inherited:=table_remove fork_fixture_duplicated(Int.repr 10).
Definition fork_fixture_world:=
  namespace_default_action(namespace_remask
    (namespace_retable(namespace_retable(namespace_retable fork_fixture_initial fork_fixture_paired)
      fork_fixture_duplicated)fork_fixture_inherited)
    (namespace_blockable_mask Int64.mone))(Int.repr 17).
Definition fork_fixture_reset(queues:NamespaceQueues):NamespaceQueues:=
  fun query=>if Nat.eqb query 60 then channel_empty else queues query.

Lemma fork_fixture_ordinary_has_no_channel channel:channel_absent fork_fixture_ordinary channel.
Proof.
  intros descriptor binding side PRESENT.
  unfold fork_fixture_ordinary in PRESENT;
  destruct((Z.leb 0(Int.signed descriptor)&&Z.leb(Int.signed descriptor)8)%bool);[|discriminate].
  inversion PRESENT;subst binding;discriminate.
Qed.
Lemma fork_fixture_ambient_has_no_channel channel:
  Forall(fun table=>channel_absent table channel)(namespace_ambient fork_fixture_initial).
Proof.
  constructor;[|constructor];intros descriptor binding side PRESENT.
  unfold fork_fixture_other in PRESENT;
  destruct((Z.leb 0(Int.signed descriptor)&&Z.leb(Int.signed descriptor)2)%bool);[|discriminate].
  inversion PRESENT;subst binding;discriminate.
Qed.
Lemma fork_fixture_pair:
  socketpair_table fork_fixture_ordinary(Int.repr 9)(Int.repr 10)60 fork_fixture_paired.
Proof.
  apply socketpair_table_success.
  - change(0<=9);lia.
  - change(0<=10);lia.
  - vm_compute;discriminate.
  - vm_compute;reflexivity.
  - vm_compute;reflexivity.
  - apply fork_fixture_ordinary_has_no_channel.
Qed.
Lemma fork_fixture_duplicate:
  duplicate_table fork_fixture_paired(Int.repr 10)(Int.repr 60)(Int.repr 60)
    fork_fixture_duplicated.
Proof.
  apply duplicate_table_success with(binding:=endpoint_binding 60 child_endpoint).
  - apply table_put_same.
  - lia.
  - vm_compute;reflexivity.
Qed.

(* The exact shared source log is retained, including all internal source steps. *)
Theorem namespace_useful_common_queue pair queues:
  namespace_queue_steps namespace_queue_model fork_fixture_initial queues
    (namespace_child_common_log pair(Int.repr 9)(Int.repr 10))fork_fixture_world
    (fork_fixture_reset queues).
Proof.
  unfold namespace_child_common_log;cbn[repeat app].
  repeat first[
    apply namespace_queue_nil|
    (eapply namespace_queue_cons;
      [eapply namespace_queue_other;
        [apply namespace_kernel_source|intros;discriminate|intros;reflexivity]|])|
    (eapply namespace_queue_cons;
      [eapply namespace_queue_created with(created:=60%nat);
        [exact fork_fixture_pair|apply fork_fixture_ambient_has_no_channel]|])|
    (eapply namespace_queue_cons;
      [eapply namespace_queue_other;
        [apply namespace_kernel_duplicate_success;exact fork_fixture_duplicate|
         intros;discriminate|intros;reflexivity]|])|
    (eapply namespace_queue_cons;
      [eapply namespace_queue_other;
        [apply namespace_kernel_close;apply close_table_success|
         intros;discriminate|intros;reflexivity]|])|
    (eapply namespace_queue_cons;
      [eapply namespace_queue_other;
        [apply namespace_kernel_mask_success|intros;discriminate|intros;reflexivity]|])|
    (eapply namespace_queue_cons;
      [eapply namespace_queue_other;
        [apply namespace_kernel_default_success|intros;discriminate|intros;reflexivity]|])].
Qed.

Theorem namespace_useful_common_kernel pair:
  namespace_kernel_steps fork_fixture_initial
    (namespace_child_common_log pair(Int.repr 9)(Int.repr 10))fork_fixture_world.
Proof.
  eapply namespace_queue_steps_kernel.
  exact(namespace_useful_common_queue pair(fun _=>channel_empty)).
Qed.

Theorem namespace_useful_common_resets_old_bytes pair queues:
  namespace_queue_steps namespace_queue_model fork_fixture_initial queues
    (namespace_child_common_log pair(Int.repr 9)(Int.repr 10))fork_fixture_world
    (fork_fixture_reset queues) /\fork_fixture_reset queues 60%nat=channel_empty.
Proof. split;[apply namespace_useful_common_queue|reflexivity]. Qed.

Definition fork_fixture_snapshot:ForkSnapshot.
Proof.
  refine{|fork_parent:=fork_fixture_parent;fork_child:=fork_fixture_child;
    fork_parent_table_identity:=1;fork_child_table_identity:=2;
    fork_inherited_table:=fork_fixture_inherited|}.
  - intro SAME;pose proof(f_equal task_pid SAME)as PID;vm_compute in PID;discriminate.
  - vm_compute;discriminate.
  - lia.
  - change(1<=2);lia.
Defined.

Theorem namespace_useful_common_fork:
  fork_matches fork_fixture_world fork_fixture_snapshot /\
  namespace_sigchld fork_fixture_world=default_signal_action /\
  namespace_signal_mask fork_fixture_world=namespace_blockable_mask Int64.mone /\
  namespace_fork_effect fork_fixture_world fork_fixture_snapshot(Int.repr 2)fork_fixture_world /\
  namespace_fork_effect fork_fixture_world fork_fixture_snapshot Int.zero
    (namespace_fork_child fork_fixture_world fork_fixture_snapshot).
Proof.
  assert(MATCH:fork_matches fork_fixture_world fork_fixture_snapshot)by(repeat split;reflexivity).
  split;[exact MATCH|]. split;[reflexivity|]. split;[reflexivity|].
  split;[apply namespace_fork_parent_effect|apply namespace_fork_child_effect];exact MATCH.
Qed.

Theorem namespace_useful_fork_handles:
  fork_inherited_table fork_fixture_snapshot(Int.repr 4)=
    Some{|descriptor_object:=ordinary_object 100;descriptor_cloexec:=true|} /\
  fork_inherited_table fork_fixture_snapshot(Int.repr 5)=
    Some{|descriptor_object:=ordinary_object 101;descriptor_cloexec:=true|} /\
  fork_inherited_table fork_fixture_snapshot(Int.repr 6)=
    Some{|descriptor_object:=ordinary_object 102;descriptor_cloexec:=true|} /\
  fork_inherited_table fork_fixture_snapshot(Int.repr 9)=Some(endpoint_binding 60 parent_endpoint) /\
  fork_inherited_table fork_fixture_snapshot(Int.repr 60)=Some(endpoint_binding 60 child_endpoint) /\
  fork_inherited_table fork_fixture_snapshot(Int.repr 10)=None.
Proof. vm_compute;repeat split;reflexivity. Qed.

Theorem namespace_useful_fork_copy cell memory:
  entry_errno_ready cell memory ->NativeForkCopy cell memory memory memory.
Proof. intro READY;constructor;try exact READY;apply namespace_partial_refl. Qed.

Definition fork_fixture_worker_table:=exec_table(handoff_stdio_table fork_fixture_inherited
  (Int.repr 4)(Int.repr 5)(Int.repr 6)(Int.repr 60)).
Definition fork_fixture_worker_slot descriptor:=
  if (Int.eq descriptor Int.zero||Int.eq descriptor(Int.repr 2))%bool then
    Some{|descriptor_object:=ordinary_object 333;descriptor_cloexec:=false|}
  else if Int.eq descriptor(Int.repr 4)then
    Some{|descriptor_object:=ordinary_object 100;descriptor_cloexec:=false|}
  else if Int.eq descriptor(Int.repr 5)then
    Some{|descriptor_object:=ordinary_object 101;descriptor_cloexec:=false|}
  else if Int.eq descriptor(Int.repr 6)then
    Some{|descriptor_object:=ordinary_object 102;descriptor_cloexec:=false|}
  else if Int.eq descriptor(Int.repr 60)then
    Some{|descriptor_object:=release_endpoint 60 child_endpoint;descriptor_cloexec:=false|}
  else None.

(* Metadata's temporary descriptor one is fresh in this same copied worker table. *)
Theorem namespace_useful_worker_table_exact descriptor:
  fork_fixture_worker_table descriptor=fork_fixture_worker_slot descriptor.
Proof.
  destruct(Int.eq descriptor Int.zero)eqn:ZERO;
    [apply Int.same_if_eq in ZERO;subst descriptor;vm_compute;reflexivity|].
  destruct(Int.eq descriptor(Int.repr 2))eqn:TWO;
    [apply Int.same_if_eq in TWO;subst descriptor;vm_compute;reflexivity|].
  destruct(Int.eq descriptor(Int.repr 4))eqn:FOUR;
    [apply Int.same_if_eq in FOUR;subst descriptor;vm_compute;reflexivity|].
  destruct(Int.eq descriptor(Int.repr 5))eqn:FIVE;
    [apply Int.same_if_eq in FIVE;subst descriptor;vm_compute;reflexivity|].
  destruct(Int.eq descriptor(Int.repr 6))eqn:SIX;
    [apply Int.same_if_eq in SIX;subst descriptor;vm_compute;reflexivity|].
  destruct(Int.eq descriptor(Int.repr 60))eqn:SIXTY;
    [apply Int.same_if_eq in SIXTY;subst descriptor;vm_compute;reflexivity|].
  unfold fork_fixture_worker_table,fork_fixture_worker_slot,exec_table,handoff_stdio_table,
    handoff_flagged_table,descriptor_flags,fork_fixture_inherited,fork_fixture_duplicated,
    fork_fixture_paired,table_remove,table_put,fork_fixture_ordinary.
  rewrite ZERO,TWO,FOUR,FIVE,SIX,SIXTY;cbn.
  destruct(Int.eq descriptor(Int.repr 10));[reflexivity|].
  destruct(Int.eq descriptor(Int.repr 9));
    destruct((Z.leb 0(Int.signed descriptor)&&Z.leb(Int.signed descriptor)8)%bool);
    destruct(Int.eq descriptor(Int.repr 1));reflexivity.
Qed.

Theorem namespace_useful_worker_has_private_metadata_slot:
  fork_fixture_worker_table Int.one=None /\
  fork_fixture_worker_table Int.zero=
    Some{|descriptor_object:=ordinary_object 333;descriptor_cloexec:=false|} /\
  fork_fixture_worker_table(Int.repr 2)=
    Some{|descriptor_object:=ordinary_object 333;descriptor_cloexec:=false|} /\
  fork_fixture_worker_table(Int.repr 7)=None /\fork_fixture_worker_table(Int.repr 8)=None.
Proof. vm_compute;repeat split;reflexivity. Qed.
