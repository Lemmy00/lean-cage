(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Interpret the very source prefix that created the private child. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Clight.
Require Import Machine LibraryMachine ProcessEffects.
From EntryNative Require Import NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine.
From EntryNamespace Require Import NamespaceMachine NamespaceObjects NamespaceKernel NamespaceTraceRegion.
Import ListNotations.
Open Scope Z_scope.

Inductive namespace_kernel_steps : NamespaceWorld -> list namespace_event -> NamespaceWorld -> Prop :=
| namespace_kernel_nil : forall world,namespace_kernel_steps world [] world
| namespace_kernel_cons : forall before event middle rest after,
    namespace_kernel_event before event middle -> namespace_kernel_steps middle rest after ->
    namespace_kernel_steps before (event::rest) after.

Lemma namespace_kernel_steps_append before first middle second after :
  namespace_kernel_steps before first middle -> namespace_kernel_steps middle second after ->
  namespace_kernel_steps before (first++second) after.
Proof. intros FIRST SECOND;induction FIRST;cbn;[exact SECOND|econstructor;eauto]. Qed.

Lemma namespace_kernel_steps_split before first second after :
  namespace_kernel_steps before (first++second) after ->
  exists middle,namespace_kernel_steps before first middle /\namespace_kernel_steps middle second after.
Proof.
  revert before;induction first as[|event rest IH];intros before RUN;cbn in RUN.
  - exists before;split;[constructor|exact RUN].
  - inversion RUN;subst;destruct(IH _ H4)as[boundary[PREFIX SUFFIX]].
    exists boundary;split;[econstructor;eauto|exact SUFFIX].
Qed.

Lemma namespace_unselected_kernel_frame before event after :
  namespace_kernel_event before event after -> namespace_fd_event event=false -> after=before.
Proof.
  intros STEP UNSELECTED;inversion STEP;subst;cbn in UNSELECTED;try discriminate;try reflexivity.
  all: unfold namespace_passive_event in H;repeat match goal with
    | e:namespace_event|-_=>destruct e;cbn in *;try discriminate;try reflexivity
    | e:process_event|-_=>destruct e;cbn in *;try discriminate;try reflexivity
    | e:entry_handoff_event|-_=>destruct e;cbn in *;try discriminate;try reflexivity
    | e:library_event|-_=>destruct e;cbn in *;try discriminate;try reflexivity
    | e:Machine.event|-_=>destruct e;cbn in *;try discriminate;try reflexivity
    end.
Qed.

Theorem namespace_kernel_filter_is_same_run before events after :
  namespace_kernel_steps before events after ->
  namespace_kernel_steps before (namespace_fd_events events) after.
Proof.
  intro RUN;induction RUN;[constructor|].
  unfold namespace_fd_events in *;cbn;destruct(namespace_fd_event event)eqn:SELECTED.
  - econstructor;eassumption.
  - pose proof(namespace_unselected_kernel_frame _ _ _ H SELECTED);subst middle;exact IHRUN.
Qed.

Lemma namespace_pair_kernel_details before after output first second :
  namespace_kernel_event before
    (namespace_paired(Int.repr 1)(Int.repr 524289)Int.zero output Ptrofs.zero Int.zero first second)after ->
  exists channel table,socketpair_table(namespace_table before)first second channel table /\
    Forall(fun outside=>channel_absent outside channel)(namespace_ambient before) /\
    after=namespace_retable before table.
Proof. intro STEP;inversion STEP;subst;try discriminate;eauto 6. Qed.

Lemma namespace_duplicate_kernel_details before after source result :
  0<=Int.signed result ->
  namespace_kernel_event before(namespace_duplicated source(Int.repr 60)result)after ->
  exists table,duplicate_table(namespace_table before)source(Int.repr 60)result table /\
    after=namespace_retable before table.
Proof.
  intros NONNEGATIVE STEP;inversion STEP;subst;try discriminate;eauto.
  rewrite Int.signed_mone in NONNEGATIVE;lia.
Qed.

Lemma namespace_close_kernel_details before after descriptor reply :
  namespace_kernel_event before
    (namespace_process(process_entry(entry_library(close_returned descriptor reply))))after ->
  exists table,close_table(namespace_table before)descriptor reply table /\
    after=namespace_retable before table.
Proof. intro STEP;inversion STEP;subst;try discriminate;eauto. Qed.

Lemma namespace_mask_kernel_details before after :
  namespace_kernel_event before(namespace_masked Int64.mone Int64.zero)after ->
  after=namespace_remask before(namespace_blockable_mask Int64.mone).
Proof. intro STEP;inversion STEP;subst;try discriminate;reflexivity. Qed.

Lemma namespace_default_kernel_details before after :
  namespace_kernel_event before(namespace_defaulted(Int.repr 17)Int64.zero)after ->
  after=namespace_default_action before(Int.repr 17).
Proof. intro STEP;inversion STEP;subst;try discriminate;reflexivity. Qed.

Lemma namespace_fork_kernel_details before after returned :
  0<=Int.signed returned ->namespace_kernel_event before(namespace_forked returned)after ->
  exists snapshot,namespace_fork_effect before snapshot returned after.
Proof.
  intros NONNEGATIVE STEP;inversion STEP;subst;try discriminate;eauto.
  rewrite Int.signed_mone in NONNEGATIVE;lia.
Qed.

Definition child_channel_events output first second failure reply returned :=
  [namespace_paired(Int.repr 1)(Int.repr 524289)Int.zero output Ptrofs.zero Int.zero first second;
   namespace_duplicated second(Int.repr 60)failure;
   namespace_process(process_entry(entry_library(close_returned second reply)));
   namespace_masked Int64.mone Int64.zero;
   namespace_defaulted(Int.repr 17)Int64.zero;namespace_forked returned].

Definition child_fork_world before table :=
  namespace_default_action(namespace_remask(namespace_retable before table)
    (namespace_blockable_mask Int64.mone))(Int.repr 17).

Theorem child_channel_same_run_kernel_frame before after output first second failure reply returned :
  0<=Int.signed failure ->0<=Int.signed returned ->
  namespace_kernel_steps before(child_channel_events output first second failure reply returned)after ->
  exists channel snapshot inherited,
    namespace_fork_effect(child_fork_world before inherited)snapshot returned after /\
    namespace_sigchld(child_fork_world before inherited)=default_signal_action /\
    namespace_signal_mask(child_fork_world before inherited)=namespace_blockable_mask Int64.mone /\
    first<>failure /\second<>failure /\60<=Int.signed failure /\
    inherited first=Some(endpoint_binding channel parent_endpoint) /\
    inherited failure=Some(endpoint_binding channel child_endpoint) /\
    parent_channel_cloexec inherited channel /\
    Forall(fun outside=>channel_absent outside channel)(namespace_ambient before) /\
    (forall descriptor binding,namespace_table before descriptor=Some binding ->
      inherited descriptor=Some binding /\descriptor_object binding<>release_endpoint channel parent_endpoint).
Proof.
  intros FAILURE RETURNED RUN;unfold child_channel_events in RUN.
  inversion RUN;subst;clear RUN.
  match goal with PAIR:namespace_kernel_event _ (namespace_paired _ _ _ _ _ _ _ _) _|-_=>
    destruct(namespace_pair_kernel_details _ _ _ _ _ PAIR)as[channel[paired[PAIRTABLE[AMBIENT WORLD]]]];
    subst end.
  match goal with REST:namespace_kernel_steps _ (_::_) _|-_=>inversion REST;subst;clear REST end.
  match goal with DUP:namespace_kernel_event _ (namespace_duplicated _ _ _) _|-_=>
    destruct(namespace_duplicate_kernel_details _ _ _ _ FAILURE DUP)as[duplicated[DUPTABLE WORLD]];subst end.
  match goal with REST:namespace_kernel_steps _ (_::_) _|-_=>inversion REST;subst;clear REST end.
  match goal with CLOSE:namespace_kernel_event _ (namespace_process(process_entry(entry_library(close_returned _ _)))) _|-_=>
    destruct(namespace_close_kernel_details _ _ _ _ CLOSE)as[inherited[CLOSETABLE WORLD]];subst end.
  match goal with REST:namespace_kernel_steps _ (_::_) _|-_=>inversion REST;subst;clear REST end.
  match goal with MASK:namespace_kernel_event _ (namespace_masked _ _) _|-_=>
    pose proof(namespace_mask_kernel_details _ _ MASK)as WORLD;subst end.
  match goal with REST:namespace_kernel_steps _ (_::_) _|-_=>inversion REST;subst;clear REST end.
  match goal with DEFAULT:namespace_kernel_event _ (namespace_defaulted _ _) _|-_=>
    pose proof(namespace_default_kernel_details _ _ DEFAULT)as WORLD;subst end.
  match goal with REST:namespace_kernel_steps _ (_::_) _|-_=>inversion REST;subst;clear REST end.
  match goal with REST:namespace_kernel_steps _ [] _|-_=>inversion REST;subst;clear REST end.
  match goal with FORK:namespace_kernel_event _ (namespace_forked _) _|-_=>
    destruct(namespace_fork_kernel_details _ _ _ RETURNED FORK)as[snapshot FORKED] end.
  cbn[namespace_retable]in DUPTABLE,CLOSETABLE,FORKED.
  destruct(local_child_channel _ _ _ _ _ _ _ _ _ PAIRTABLE DUPTABLE CLOSETABLE)
    as[FIRST_SECOND[SECOND_FAILURE[MINIMUM[FIRST[ENDPOINT CLOEXEC]]]]].
  assert(OLD:forall descriptor binding,namespace_table before descriptor=Some binding ->
    inherited descriptor=Some binding /\descriptor_object binding<>release_endpoint channel parent_endpoint).
  { intros descriptor binding BINDING;eapply local_channel_preserves_old_descriptors;eassumption. }
  exists channel,snapshot,inherited;split;[exact FORKED|].
  unfold child_fork_world,namespace_default_action;rewrite Int.eq_true;cbn;auto 12.
Qed.

Theorem child_channel_same_run_kernel_producer before after output first second failure reply returned :
  0<=Int.signed failure ->0<=Int.signed returned ->
  namespace_kernel_steps before(child_channel_events output first second failure reply returned)after ->
  exists channel snapshot inherited,
    namespace_fork_effect(child_fork_world before inherited)snapshot returned after /\
    namespace_sigchld(child_fork_world before inherited)=default_signal_action /\
    namespace_signal_mask(child_fork_world before inherited)=namespace_blockable_mask Int64.mone /\
    first<>failure /\second<>failure /\60<=Int.signed failure /\
    inherited first=Some(endpoint_binding channel parent_endpoint) /\
    inherited failure=Some(endpoint_binding channel child_endpoint) /\
    parent_channel_cloexec inherited channel /\
    Forall(fun outside=>channel_absent outside channel)(namespace_ambient before).
Proof.
  intros FAILURE RETURNED RUN.
  destruct(child_channel_same_run_kernel_frame _ _ _ _ _ _ _ _ FAILURE RETURNED RUN)
    as[channel[snapshot[inherited BODY]]].
  exists channel,snapshot,inherited;tauto.
Qed.

Theorem selected_child_same_run_ownership before after output first second failure reply :
  0<=Int.signed failure ->
  namespace_kernel_steps before(child_channel_events output first second failure reply Int.zero)after ->
  exists channel snapshot,
    namespace_task after=fork_child snapshot /\
    namespace_parent after=Some(namespace_task before) /\
    namespace_table_identity after<>namespace_table_identity before /\
    namespace_sigchld after=default_signal_action /\
    namespace_signal_mask after=namespace_blockable_mask Int64.mone /\
    namespace_table after first=Some(endpoint_binding channel parent_endpoint) /\
    namespace_table after failure=Some(endpoint_binding channel child_endpoint) /\
    parent_channel_cloexec(namespace_table after)channel /\
    60<=Int.signed failure /\
    Forall(fun outside=>channel_absent outside channel)(namespace_ambient after).
Proof.
  intros FAILURE RUN.
  destruct(child_channel_same_run_kernel_producer _ _ _ _ _ _ _ _ FAILURE
    ltac:(rewrite Int.signed_zero;lia)RUN)
    as[channel[snapshot[inherited[FORK[DEFAULT[MASK[D0[D1[MINIMUM[FIRST[ENDPOINT[CLOEXEC AMBIENT]]]]]]]]]]]].
  pose proof(actual_fork_child_has_owned_table _ _ _ _ FORK eq_refl)
    as[TASK[PARENT[TABLE[PRIVATE DIFFERENT]]]].
  assert(SIGNAL:namespace_sigchld after=namespace_sigchld(child_fork_world before inherited)).
  { inversion FORK;subst;reflexivity. }
  assert(MASKED:namespace_signal_mask after=namespace_signal_mask(child_fork_world before inherited)).
  { inversion FORK;subst;reflexivity. }
  assert(OUTSIDE:namespace_ambient after=namespace_ambient before).
  { inversion FORK;subst;unfold child_fork_world,namespace_default_action;
      rewrite Int.eq_true;reflexivity. }
  exists channel,snapshot.
  unfold child_fork_world,namespace_default_action in *;rewrite Int.eq_true in *;cbn in *.
  rewrite TABLE;repeat split;try assumption;try congruence.
Qed.

Theorem selected_child_same_run_old_objects before after output first second failure reply:
  0<=Int.signed failure ->
  namespace_kernel_steps before(child_channel_events output first second failure reply Int.zero)after ->
  exists channel,parent_channel_cloexec(namespace_table after)channel /\
    namespace_table after failure=Some(endpoint_binding channel child_endpoint) /\
    (forall descriptor binding,namespace_table before descriptor=Some binding ->
      namespace_table after descriptor=Some binding /\
      descriptor_object binding<>release_endpoint channel parent_endpoint).
Proof.
  intros FAILURE RUN.
  destruct(child_channel_same_run_kernel_frame _ _ _ _ _ _ _ _ FAILURE
    ltac:(rewrite Int.signed_zero;lia)RUN)
    as[channel[snapshot[inherited[FORK BODY]]]].
  destruct(actual_fork_child_has_owned_table _ _ _ _ FORK eq_refl)
    as[TASK[PARENT[TABLE[PRIVATE DIFFERENT]]]].
  cbn[child_fork_world namespace_default_action namespace_retable namespace_remask]in TABLE.
  exists channel;rewrite TABLE;tauto.
Qed.
