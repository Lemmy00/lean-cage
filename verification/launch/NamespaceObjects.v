(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-entry.release: Derive the child's private table and exclusion of its grant writer at exec. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers Values.
Require Import ProcessEffects.
Import ListNotations.
Open Scope Z_scope.

Inductive EndpointSide := parent_endpoint | child_endpoint.
Inductive DescriptorObject := ordinary_object (identity : nat) |
  release_endpoint (channel : nat) (side : EndpointSide).
Record DescriptorBinding := {
  descriptor_object : DescriptorObject;
  descriptor_cloexec : bool
}.
Definition DescriptorTable := int -> option DescriptorBinding.
Definition table_put (table : DescriptorTable) descriptor binding : DescriptorTable :=
  fun query => if Int.eq query descriptor then Some binding else table query.
Definition table_remove (table : DescriptorTable) descriptor : DescriptorTable :=
  fun query => if Int.eq query descriptor then None else table query.
Definition endpoint_binding channel side :=
  {|descriptor_object := release_endpoint channel side;descriptor_cloexec := true|}.
Definition channel_absent (table : DescriptorTable) channel :=
  forall descriptor binding side, table descriptor = Some binding ->
    descriptor_object binding <> release_endpoint channel side.

Lemma table_put_same table descriptor binding : table_put table descriptor binding descriptor = Some binding.
Proof. unfold table_put; rewrite Int.eq_true; reflexivity. Qed.
Lemma table_put_other table descriptor binding query : query <> descriptor ->
  table_put table descriptor binding query = table query.
Proof. intro DIFFERENT; unfold table_put; rewrite Int.eq_false by congruence; reflexivity. Qed.
Lemma table_remove_same table descriptor : table_remove table descriptor descriptor = None.
Proof. unfold table_remove; rewrite Int.eq_true; reflexivity. Qed.
Lemma table_remove_other table descriptor query : query <> descriptor ->
  table_remove table descriptor query = table query.
Proof. intro DIFFERENT; unfold table_remove; rewrite Int.eq_false by congruence; reflexivity. Qed.

(* These relations are single Linux operations. The application source selects
   their arguments and tests their returns; it does not receive a compound
   channel/fork guarantee as an external operation. *)
Inductive socketpair_table : DescriptorTable -> int -> int -> nat -> DescriptorTable -> Prop :=
| socketpair_table_success : forall before first second channel,
    0 <= Int.signed first -> 0 <= Int.signed second -> first <> second ->
    before first = None -> before second = None -> channel_absent before channel ->
    socketpair_table before first second channel
      (table_put (table_put before first (endpoint_binding channel parent_endpoint))
        second (endpoint_binding channel child_endpoint)).

Inductive duplicate_table : DescriptorTable -> int -> int -> int -> DescriptorTable -> Prop :=
| duplicate_table_success : forall before source minimum result binding,
    before source = Some binding -> Int.signed minimum <= Int.signed result ->
    before result = None ->
    duplicate_table before source minimum result
      (table_put before result
        {|descriptor_object := descriptor_object binding;descriptor_cloexec := true|}).

Inductive close_table : DescriptorTable -> int -> close_reply -> DescriptorTable -> Prop :=
| close_table_success : forall before descriptor error,
    close_table before descriptor (close_ok error) (table_remove before descriptor)
| close_table_error_closed : forall before descriptor error,
    close_table before descriptor (close_error error) (table_remove before descriptor)
| close_table_error_retained : forall before descriptor error,
    close_table before descriptor (close_error error) before.

Definition parent_channel_cloexec (table : DescriptorTable) channel :=
  forall descriptor binding,
    table descriptor = Some binding ->
    descriptor_object binding = release_endpoint channel parent_endpoint ->
    descriptor_cloexec binding = true.

Theorem pair_old_descriptors_distinct before first second channel after old binding :
  socketpair_table before first second channel after -> before old = Some binding ->
  old <> first /\ old <> second /\ after old = Some binding.
Proof.
  intros PAIR OLD; inversion PAIR; subst.
  assert (FIRST : old <> first) by congruence.
  assert (SECOND : old <> second) by congruence.
  split; [exact FIRST|]; split; [exact SECOND|].
  rewrite table_put_other by exact SECOND; rewrite table_put_other by exact FIRST; exact OLD.
Qed.

Theorem pair_parent_cloexec before first second channel after :
  socketpair_table before first second channel after -> parent_channel_cloexec after channel.
Proof.
  intros PAIR; inversion PAIR; subst.
  unfold parent_channel_cloexec,table_put; intros descriptor binding LOAD OBJECT.
  destruct (Int.eq descriptor second) eqn:SECOND.
  - inversion LOAD; reflexivity.
  - destruct (Int.eq descriptor first) eqn:FIRST.
    + inversion LOAD; reflexivity.
    + exfalso; eapply (H4 descriptor binding parent_endpoint); eassumption.
Qed.

Theorem pair_child_binding before first second channel after :
  socketpair_table before first second channel after ->
  after second = Some (endpoint_binding channel child_endpoint) /\
  after first = Some (endpoint_binding channel parent_endpoint).
Proof.
  intro PAIR; inversion PAIR; subst; split; [apply table_put_same|].
  rewrite table_put_other by congruence; apply table_put_same.
Qed.

Theorem duplicate_fresh_and_alias before source minimum result after binding :
  duplicate_table before source minimum result after -> before source = Some binding ->
  result <> source /\ Int.signed minimum <= Int.signed result /\
  after result = Some {|descriptor_object := descriptor_object binding;descriptor_cloexec := true|} /\
  forall descriptor, descriptor <> result -> after descriptor = before descriptor.
Proof.
  intros DUP SOURCE; inversion DUP; subst.
  assert (BINDING : binding0 = binding) by congruence; subst binding0.
  repeat split; try congruence; try assumption.
  - apply table_put_same.
  - intros descriptor DIFFERENT; apply table_put_other; exact DIFFERENT.
Qed.

Theorem duplicate_preserves_parent_cloexec before source minimum result after channel :
  duplicate_table before source minimum result after -> parent_channel_cloexec before channel ->
  parent_channel_cloexec after channel.
Proof.
  intros DUP PARENT; inversion DUP; subst.
  unfold parent_channel_cloexec,table_put; intros descriptor other LOAD OBJECT.
  destruct (Int.eq descriptor result); [inversion LOAD; reflexivity|].
  eapply PARENT; eassumption.
Qed.

Theorem close_preserves_other before descriptor reply after old binding :
  close_table before descriptor reply after -> old <> descriptor ->
  before old = Some binding -> after old = Some binding.
Proof.
  intros CLOSE DIFFERENT OLD; inversion CLOSE; subst; auto;
    rewrite table_remove_other by exact DIFFERENT; exact OLD.
Qed.

Theorem close_preserves_parent_cloexec before descriptor reply after channel :
  close_table before descriptor reply after -> parent_channel_cloexec before channel ->
  parent_channel_cloexec after channel.
Proof.
  intros CLOSE PARENT; inversion CLOSE; subst; try exact PARENT.
  all: unfold parent_channel_cloexec,table_remove; intros query binding LOAD OBJECT.
  all: destruct (Int.eq query descriptor); [discriminate|eapply PARENT; eassumption].
Qed.

Record TaskIdentity := { task_pid : int; task_incarnation : nat }.
Record ForkSnapshot := {
  fork_parent : TaskIdentity;
  fork_child : TaskIdentity;
  fork_parent_table_identity : nat;
  fork_child_table_identity : nat;
  fork_inherited_table : DescriptorTable;
  fork_different_tasks : fork_parent <> fork_child;
  fork_different_pids : task_pid fork_parent <> task_pid fork_child;
  fork_different_tables : fork_parent_table_identity <> fork_child_table_identity;
  fork_child_positive : 1 <= Int.signed (task_pid fork_child)
}.

Definition fork_parent_tables (snapshot : ForkSnapshot) query : option DescriptorTable :=
  if Nat.eqb query (fork_parent_table_identity snapshot)
  then Some (fork_inherited_table snapshot) else None.
Definition fork_copied_tables (snapshot : ForkSnapshot) query : option DescriptorTable :=
  if Nat.eqb query (fork_child_table_identity snapshot)
  then Some (fork_inherited_table snapshot) else fork_parent_tables snapshot query.
Definition replace_child_table snapshot table query : option DescriptorTable :=
  if Nat.eqb query (fork_child_table_identity snapshot) then Some table
  else fork_parent_tables snapshot query.

Theorem fork_private_table snapshot :
  fork_copied_tables snapshot (fork_child_table_identity snapshot) = Some (fork_inherited_table snapshot) /\
  fork_copied_tables snapshot (fork_parent_table_identity snapshot) = Some (fork_inherited_table snapshot) /\
  forall child_table,
    replace_child_table snapshot child_table (fork_parent_table_identity snapshot) =
      Some (fork_inherited_table snapshot).
Proof.
  unfold fork_copied_tables,replace_child_table,fork_parent_tables.
  rewrite Nat.eqb_refl.
  rewrite (proj2 (Nat.eqb_neq _ _)) by (pose proof (fork_different_tables snapshot); congruence).
  rewrite Nat.eqb_refl; auto.
Qed.

Definition descriptor_flags table descriptor cloexec : DescriptorTable :=
  fun query => match table query with
  | None => None
  | Some binding => if Int.eq query descriptor
      then Some {|descriptor_object := descriptor_object binding;descriptor_cloexec := cloexec|}
      else Some binding
  end.
Definition exec_table table : DescriptorTable :=
  fun descriptor => match table descriptor with
  | Some binding => if descriptor_cloexec binding then None else Some binding
  | None => None
  end.

Theorem flags_preserve_parent_cloexec table descriptor cloexec channel :
  parent_channel_cloexec table channel ->
  (forall binding, table descriptor = Some binding ->
    descriptor_object binding <> release_endpoint channel parent_endpoint) ->
  parent_channel_cloexec (descriptor_flags table descriptor cloexec) channel.
Proof.
  intros PARENT SELECTED query binding LOAD OBJECT.
  unfold descriptor_flags in LOAD.
  destruct (table query) as [old|] eqn:OLD; [|discriminate].
  destruct (Int.eq query descriptor) eqn:SAME.
  - apply Int.same_if_eq in SAME; subst query; inversion LOAD; subst binding; cbn in OBJECT.
    exfalso; eapply SELECTED; eassumption.
  - inversion LOAD; subst binding; eapply PARENT; eassumption.
Qed.

Theorem exec_excludes_parent_endpoint table channel :
  parent_channel_cloexec table channel ->
  forall descriptor binding, exec_table table descriptor = Some binding ->
    descriptor_object binding <> release_endpoint channel parent_endpoint.
Proof.
  intros PARENT descriptor binding LOAD OBJECT; unfold exec_table in LOAD.
  destruct (table descriptor) as [old|] eqn:OLD; [|discriminate].
  destruct (descriptor_cloexec old) eqn:FLAG; [discriminate|].
  inversion LOAD; subst binding; specialize (PARENT _ _ OLD OBJECT); congruence.
Qed.

Theorem fork_exec_closes_inherited_grant_writer snapshot channel :
  parent_channel_cloexec (fork_inherited_table snapshot) channel ->
  forall descriptor binding,
    exec_table (fork_inherited_table snapshot) descriptor = Some binding ->
    descriptor_object binding <> release_endpoint channel parent_endpoint.
Proof. intros CLOEXEC; apply exec_excludes_parent_endpoint; exact CLOEXEC. Qed.

Theorem local_child_channel before paired duplicated inherited first second failure channel reply :
  socketpair_table before first second channel paired ->
  duplicate_table paired second (Int.repr 60) failure duplicated ->
  close_table duplicated second reply inherited ->
  first <> failure /\ second <> failure /\ 60 <= Int.signed failure /\
  inherited first = Some (endpoint_binding channel parent_endpoint) /\
  inherited failure = Some (endpoint_binding channel child_endpoint) /\
  parent_channel_cloexec inherited channel.
Proof.
  intros PAIR DUP CLOSE.
  destruct (pair_child_binding _ _ _ _ _ PAIR) as [SECOND FIRST].
  inversion DUP; subst.
  assert (BINDING : binding = endpoint_binding channel child_endpoint) by congruence; subst binding.
  assert (FAILURE_FIRST : failure <> first) by congruence.
  assert (FAILURE_SECOND : failure <> second) by congruence.
  assert (FIRST_SECOND : first <> second) by (inversion PAIR; assumption).
  repeat split; try congruence; try assumption.
  - eapply close_preserves_other; [exact CLOSE|exact FIRST_SECOND|].
    rewrite table_put_other by congruence; exact FIRST.
  - eapply close_preserves_other; [exact CLOSE|exact FAILURE_SECOND|apply table_put_same].
  - eapply close_preserves_parent_cloexec; [exact CLOSE|].
    eapply duplicate_preserves_parent_cloexec; [exact DUP|].
    eapply pair_parent_cloexec; exact PAIR.
Qed.

Definition excludes_parent_at (table : DescriptorTable) channel descriptor :=
  forall binding, table descriptor = Some binding ->
    descriptor_object binding <> release_endpoint channel parent_endpoint.

Lemma flags_preserve_object table descriptor cloexec query binding :
  descriptor_flags table descriptor cloexec query = Some binding ->
  exists previous, table query = Some previous /\ descriptor_object previous = descriptor_object binding.
Proof.
  unfold descriptor_flags; destruct (table query) as [previous|] eqn:OLD; [|discriminate].
  destruct (Int.eq query descriptor); intros LOAD; inversion LOAD; subst;
    eexists; split; reflexivity.
Qed.

Lemma flags_preserve_exclusion table descriptor cloexec query channel :
  excludes_parent_at table channel query ->
  excludes_parent_at (descriptor_flags table descriptor cloexec) channel query.
Proof.
  intros EXCLUDED binding LOAD.
  destruct (flags_preserve_object _ _ _ _ _ LOAD) as [previous [OLD OBJECT]].
  rewrite <- OBJECT; apply EXCLUDED; exact OLD.
Qed.

Definition handoff_flagged_table table input output errors failure :=
  descriptor_flags
    (descriptor_flags (descriptor_flags (descriptor_flags table input false) output false) errors false)
    failure false.

Definition handoff_stdio_table table input output errors failure :=
  descriptor_flags (handoff_flagged_table table input output errors failure) (Int.repr 1) true.

Theorem cloexec_set_preserves_parent table descriptor channel :
  parent_channel_cloexec table channel ->
  parent_channel_cloexec (descriptor_flags table descriptor true) channel.
Proof.
  intros PARENT query binding LOAD OBJECT; unfold descriptor_flags in LOAD.
  destruct (table query) as [previous|] eqn:PREVIOUS; [|discriminate].
  destruct (Int.eq query descriptor).
  - inversion LOAD; reflexivity.
  - inversion LOAD; subst binding; eapply PARENT; eassumption.
Qed.

Theorem four_handle_flags_preserve_private_grant table input output errors failure channel :
  parent_channel_cloexec table channel ->
  excludes_parent_at table channel input -> excludes_parent_at table channel output ->
  excludes_parent_at table channel errors -> excludes_parent_at table channel failure ->
  parent_channel_cloexec (handoff_flagged_table table input output errors failure) channel.
Proof.
  intros PARENT INPUT OUTPUT ERRORS FAILURE; unfold handoff_flagged_table.
  apply flags_preserve_parent_cloexec.
  - apply flags_preserve_parent_cloexec.
    + apply flags_preserve_parent_cloexec.
      * apply flags_preserve_parent_cloexec; assumption.
      * apply flags_preserve_exclusion; exact OUTPUT.
    + apply flags_preserve_exclusion,flags_preserve_exclusion; exact ERRORS.
  - apply flags_preserve_exclusion,flags_preserve_exclusion,flags_preserve_exclusion; exact FAILURE.
Qed.

Theorem actual_handoff_exec_has_no_grant_writer table input output errors failure channel :
  parent_channel_cloexec table channel ->
  excludes_parent_at table channel input -> excludes_parent_at table channel output ->
  excludes_parent_at table channel errors -> excludes_parent_at table channel failure ->
  forall descriptor binding,
    exec_table (handoff_stdio_table table input output errors failure) descriptor = Some binding ->
    descriptor_object binding <> release_endpoint channel parent_endpoint.
Proof.
  intros PARENT INPUT OUTPUT ERRORS FAILURE.
  apply exec_excludes_parent_endpoint; unfold handoff_stdio_table; apply cloexec_set_preserves_parent.
  apply four_handle_flags_preserve_private_grant; assumption.
Qed.

Theorem local_channel_preserves_old_descriptors before paired duplicated inherited
    first second failure channel reply descriptor binding:
  socketpair_table before first second channel paired ->
  duplicate_table paired second(Int.repr 60)failure duplicated ->
  close_table duplicated second reply inherited ->before descriptor=Some binding ->
  inherited descriptor=Some binding /\
    descriptor_object binding<>release_endpoint channel parent_endpoint.
Proof.
  intros PAIR DUP CLOSE ORIGINAL.
  destruct(pair_old_descriptors_distinct _ _ _ _ _ _ _ PAIR ORIGINAL)
    as[FIRST[SECOND PAIRED]].
  assert(FAILURE:descriptor<>failure).
  { inversion DUP;subst;congruence. }
  assert(DUPLICATED:duplicated descriptor=Some binding).
  { inversion DUP;subst;rewrite table_put_other by exact FAILURE;exact PAIRED. }
  split;[eapply close_preserves_other;[exact CLOSE|exact SECOND|exact DUPLICATED]|].
  inversion PAIR;subst;eapply H4;eassumption.
Qed.
