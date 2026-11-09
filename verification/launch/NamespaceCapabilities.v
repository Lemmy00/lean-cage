(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-entry.release: Fresh private objects remain unavailable to unrelated tasks under actual FD operations. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Integers Values.
From EntryNamespace Require Import NamespaceObjects NamespaceDescriptorFrame.
Import ListNotations.

Definition TaskTables:=nat->DescriptorTable.
Definition task_table_put(tables:TaskTables)actor table:TaskTables:=
  fun query=>if Nat.eqb query actor then table else tables query.
Definition table_objects_from(before after:DescriptorTable):Prop:=forall fd binding,
  after fd=Some binding ->exists old previous,before old=Some previous /\
    descriptor_object previous=descriptor_object binding.
Lemma descriptor_frame_objects_from before after:
  descriptor_object_frame before after ->table_objects_from before after.
Proof. intros FRAME fd binding PRESENT;destruct(FRAME _ _ PRESENT)as[old[PRIOR OBJECT]];exists fd,old;auto. Qed.
Lemma local_duplicate_objects_from before source minimum returned after:
  duplicate_table before source minimum returned after ->table_objects_from before after.
Proof.
  intro DUP;inversion DUP;subst;intros fd present LOAD;unfold table_put in LOAD.
  destruct(Int.eq fd returned).
  - inversion LOAD;subst;exists source,binding;auto.
  - exists fd,present;auto.
Qed.

Record CapabilityMessage:={capability_receiver:nat;capability_object:DescriptorObject}.
Record CapabilityWorld:={capability_tables:TaskTables;capability_messages:list CapabilityMessage}.
Definition capability_retable world actor table:CapabilityWorld:={|
  capability_tables:=task_table_put(capability_tables world)actor table;
  capability_messages:=capability_messages world|}.
Definition capability_pending world messages:CapabilityWorld:={|
  capability_tables:=capability_tables world;capability_messages:=messages|}.

Inductive CapabilityAction:=
| capability_local(actor:nat)
| capability_open(actor:nat)
| capability_fork(parent child:nat)
| capability_send(actor receiver:nat)(fd:int)
| capability_receive(actor:nat)(fd:int)
| capability_acquire(actor donor:nat)(source target:int)
| capability_drop.

(* Individual Linux FD operations: flags/close/exec preserve objects at each
   retained descriptor; dup preserves an object from the same table. Ordinary
   open cannot return an existing anonymous socket. SCM_RIGHTS transfer and
   privileged acquisition are represented explicitly, not silently excluded. *)
Inductive capability_step(can_acquire:nat->nat->Prop):
    CapabilityWorld->CapabilityAction->CapabilityWorld->Prop:=
| capability_local_step:forall before actor after,
    table_objects_from(capability_tables before actor)after ->
    capability_step can_acquire before(capability_local actor)(capability_retable before actor after)
| capability_open_step:forall before actor fd identity flag,
    capability_tables before actor fd=None ->
    capability_step can_acquire before(capability_open actor)
      (capability_retable before actor(table_put(capability_tables before actor)fd
        {|descriptor_object:=ordinary_object identity;descriptor_cloexec:=flag|}))
| capability_fork_step:forall before parent child,
    (forall fd,capability_tables before child fd=None) ->
    capability_step can_acquire before(capability_fork parent child)
      (capability_retable before child(capability_tables before parent))
| capability_send_step:forall before actor receiver fd binding,
    capability_tables before actor fd=Some binding ->
    capability_step can_acquire before(capability_send actor receiver fd)
      (capability_pending before(capability_messages before++
        [{|capability_receiver:=receiver;capability_object:=descriptor_object binding|}]))
| capability_receive_step:forall before prefix message rest fd flag,
    capability_messages before=prefix++message::rest ->
    capability_tables before(capability_receiver message)fd=None ->
    capability_step can_acquire before(capability_receive(capability_receiver message)fd)
      {|capability_tables:=task_table_put(capability_tables before)(capability_receiver message)
          (table_put(capability_tables before(capability_receiver message))fd
            {|descriptor_object:=capability_object message;descriptor_cloexec:=flag|});
        capability_messages:=prefix++rest|}
| capability_acquire_step:forall before actor donor source target binding,
    can_acquire actor donor ->capability_tables before donor source=Some binding ->
    capability_tables before actor target=None ->
    capability_step can_acquire before(capability_acquire actor donor source target)
      (capability_retable before actor(table_put(capability_tables before actor)target binding))
| capability_drop_step:forall before retained,
    incl retained(capability_messages before) ->
    capability_step can_acquire before capability_drop(capability_pending before retained).

Definition unrelated(parent child actor:nat):=actor<>parent /\actor<>child.
Definition source_holders_do_not_export parent child action:=match action with
  |capability_send actor _ _|capability_fork actor _=>unrelated parent child actor
  |_=>True end.
Definition source_acquisition_private parent child action:=match action with
  |capability_acquire actor donor _ _=>unrelated parent child actor ->unrelated parent child donor
  |_=>True end.
Definition capability_private_invariant parent child channel world:=
  (forall actor,unrelated parent child actor ->channel_absent(capability_tables world actor)channel) /\
  Forall(fun message=>forall side,capability_object message<>release_endpoint channel side)
    (capability_messages world).
Definition no_privileged_private_acquisition(can_acquire:nat->nat->Prop)parent child:=forall actor donor,
  unrelated parent child actor ->can_acquire actor donor ->unrelated parent child donor.

Lemma task_table_put_same tables actor table:task_table_put tables actor table actor=table.
Proof. unfold task_table_put;rewrite Nat.eqb_refl;reflexivity. Qed.
Lemma task_table_put_other tables actor table query:query<>actor ->
  task_table_put tables actor table query=tables query.
Proof. intro OTHER;unfold task_table_put;assert(EQ:Nat.eqb query actor=false)by(apply Nat.eqb_neq;exact OTHER);rewrite EQ;reflexivity. Qed.
Lemma absence_from_objects before after channel:
  table_objects_from before after ->channel_absent before channel ->channel_absent after channel.
Proof.
  intros FROM ABSENT fd binding side PRESENT OBJECT;destruct(FROM _ _ PRESENT)as[old[previous[OLD SAME]]].
  exact(ABSENT old previous side OLD(eq_trans SAME OBJECT)).
Qed.
Lemma absence_put_ordinary table channel fd identity flag:
  channel_absent table channel ->channel_absent(table_put table fd
    {|descriptor_object:=ordinary_object identity;descriptor_cloexec:=flag|})channel.
Proof.
  intros ABSENT query binding side PRESENT OBJECT;unfold table_put in PRESENT.
  destruct(Int.eq query fd);[inversion PRESENT;subst;discriminate|eapply ABSENT;[exact PRESENT|exact OBJECT]].
Qed.
Lemma absence_put_object table channel fd object flag:
  channel_absent table channel ->(forall side,object<>release_endpoint channel side) ->
  channel_absent(table_put table fd{|descriptor_object:=object;descriptor_cloexec:=flag|})channel.
Proof.
  intros ABSENT OBJECT query binding side PRESENT SAME;unfold table_put in PRESENT.
  destruct(Int.eq query fd);[inversion PRESENT;subst;exact(OBJECT side SAME)|exact(ABSENT _ _ _ PRESENT SAME)].
Qed.

Theorem capability_step_preserves_private_from_action can_acquire parent child channel before action after:
  source_acquisition_private parent child action ->
  source_holders_do_not_export parent child action ->
  capability_private_invariant parent child channel before ->
  capability_step can_acquire before action after ->capability_private_invariant parent child channel after.
Proof.
  intros ACQUISITION NOEXPORT[ABSENT MESSAGES]STEP;inversion STEP;subst;
    cbn[capability_private_invariant capability_retable capability_pending capability_tables capability_messages]in *.
  - split;[|exact MESSAGES];intros query OTHER;cbn[capability_retable capability_pending capability_tables capability_messages].
    destruct(Nat.eq_dec query actor)as[SAME|DIFFERENT];subst.
    + rewrite task_table_put_same;eapply absence_from_objects;[eassumption|apply ABSENT;exact OTHER].
    + rewrite task_table_put_other by exact DIFFERENT;apply ABSENT;exact OTHER.
  - split;[|exact MESSAGES];intros query OTHER;cbn[capability_retable capability_pending capability_tables capability_messages].
    destruct(Nat.eq_dec query actor)as[SAME|DIFFERENT];subst.
    + rewrite task_table_put_same;apply absence_put_ordinary,ABSENT;exact OTHER.
    + rewrite task_table_put_other by exact DIFFERENT;apply ABSENT;exact OTHER.
  - split;[|exact MESSAGES];intros query OTHER;cbn[capability_retable capability_pending capability_tables capability_messages].
    destruct(Nat.eq_dec query child0)as[SAME|DIFFERENT];subst.
    + rewrite task_table_put_same;apply ABSENT;exact NOEXPORT.
    + rewrite task_table_put_other by exact DIFFERENT;apply ABSENT;exact OTHER.
  - split;[exact ABSENT|]. cbn[capability_pending capability_messages]. apply Forall_app;split;[exact MESSAGES|constructor;[|constructor]].
    intros side;exact(ABSENT actor NOEXPORT fd binding side H).
  - assert(MESSAGE:forall side,capability_object message<>release_endpoint channel side).
    { rewrite Forall_forall in MESSAGES;apply MESSAGES;rewrite H;apply in_or_app;right;left;reflexivity. }
    split.
    + intros query OTHER;cbn[capability_tables];destruct(Nat.eq_dec query(capability_receiver message))as[SAME|DIFFERENT];subst.
      * rewrite task_table_put_same;apply absence_put_object;[apply ABSENT;exact OTHER|exact MESSAGE].
      * rewrite task_table_put_other by exact DIFFERENT;apply ABSENT;exact OTHER.
    + cbn[capability_messages];rewrite H in MESSAGES;apply Forall_app in MESSAGES as[PREFIX REST];inversion REST;subst.
      apply Forall_app;auto.
  - split;[|exact MESSAGES];intros query OTHER;cbn[capability_retable capability_pending capability_tables capability_messages].
    destruct(Nat.eq_dec query actor)as[SAME|DIFFERENT];subst.
    + rewrite task_table_put_same.
      destruct binding as[object flag];apply absence_put_object;[apply ABSENT;exact OTHER|].
      intros side;exact(ABSENT donor(ACQUISITION OTHER)source
        {|descriptor_object:=object;descriptor_cloexec:=flag|}side H0).
    + rewrite task_table_put_other by exact DIFFERENT;apply ABSENT;exact OTHER.
  - split;[exact ABSENT|]. cbn[capability_pending capability_messages]. apply Forall_forall;intros message MEMBER.
    rewrite Forall_forall in MESSAGES;apply MESSAGES;apply H;exact MEMBER.
Qed.

Theorem capability_step_preserves_private can_acquire parent child channel before action after:
  no_privileged_private_acquisition can_acquire parent child ->
  source_holders_do_not_export parent child action ->
  capability_private_invariant parent child channel before ->
  capability_step can_acquire before action after ->capability_private_invariant parent child channel after.
Proof.
  intros AUTHORITY NOEXPORT INITIAL STEP.
  apply capability_step_preserves_private_from_action with(before:=before)(action:=action)(can_acquire:=can_acquire);
    [|exact NOEXPORT|exact INITIAL|exact STEP].
  destruct action;try exact I;intros OTHER;inversion STEP;subst;eapply AUTHORITY;eassumption.
Qed.

Inductive capability_execution can_acquire parent child:
  CapabilityWorld->list CapabilityAction->CapabilityWorld->Prop:=
| capability_execution_nil:forall world,capability_execution can_acquire parent child world[]world
| capability_execution_cons:forall before action middle rest after,
    source_holders_do_not_export parent child action ->capability_step can_acquire before action middle ->
    capability_execution can_acquire parent child middle rest after ->
    capability_execution can_acquire parent child before(action::rest)after.
Theorem capability_execution_preserves_private can_acquire parent child channel before actions after:
  no_privileged_private_acquisition can_acquire parent child ->
  capability_private_invariant parent child channel before ->
  capability_execution can_acquire parent child before actions after ->
  capability_private_invariant parent child channel after.
Proof.
  intros AUTHORITY INITIAL RUN;induction RUN;[exact INITIAL|].
  apply IHRUN;eapply capability_step_preserves_private;eassumption.
Qed.
