(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-entry.release: A private duplex read preserves the origin of every returned byte. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers Values.
From EntryNamespace Require Import NamespaceObjects.
Import ListNotations.

Record ChannelByte := {channel_value:Byte.int;channel_writer:nat}.
Record ChannelBuffers := {
  channel_to_parent:list ChannelByte;
  channel_to_child:list ChannelByte
}.
Definition channel_empty:= {|channel_to_parent:=[];channel_to_child:=[]|}.
Definition channel_tag actor bytes:=map(fun byte=>{|channel_value:=byte;channel_writer:=actor|})bytes.
Definition channel_enqueue buffers actor side bytes:=match side with
  |parent_endpoint=>{|channel_to_parent:=channel_to_parent buffers;
    channel_to_child:=channel_to_child buffers++channel_tag actor bytes|}
  |child_endpoint=>{|channel_to_parent:=channel_to_parent buffers++channel_tag actor bytes;
    channel_to_child:=channel_to_child buffers|}end.
Definition channel_incoming buffers side:=match side with
  |parent_endpoint=>channel_to_parent buffers|child_endpoint=>channel_to_child buffers end.
Definition channel_consume buffers side count:=match side with
  |parent_endpoint=>{|channel_to_parent:=skipn count(channel_to_parent buffers);
    channel_to_child:=channel_to_child buffers|}
  |child_endpoint=>{|channel_to_parent:=channel_to_parent buffers;
    channel_to_child:=skipn count(channel_to_child buffers)|}end.

Inductive ChannelEvent :=
| channel_sent(actor:nat)(descriptor:int)(bytes:list Byte.int)(acknowledgement_lost:bool)
| channel_read(actor:nat)(descriptor:int)(requested:nat)(bytes:list Byte.int)
| channel_passed
| channel_interrupted.

(* One syscall authenticates its actual actor and descriptor object. A lost
   write acknowledgement may still enqueue its committed prefix. A read can
   return only a prefix from the opposite endpoint; it cannot inject bytes. *)
Inductive channel_operation(tables:nat->DescriptorTable)(channel:nat):
    ChannelBuffers->ChannelEvent->ChannelBuffers->Prop:=
| channel_write_step:forall before actor fd side bytes lost,
    (exists binding,tables actor fd=Some binding /\
      descriptor_object binding=release_endpoint channel side) ->
    channel_operation tables channel before(channel_sent actor fd bytes lost)
      (channel_enqueue before actor side bytes)
| channel_read_step:forall before actor fd side requested count,
    (exists binding,tables actor fd=Some binding /\
      descriptor_object binding=release_endpoint channel side) ->
    (count<=requested)%nat ->
    channel_operation tables channel before
      (channel_read actor fd requested(map channel_value(firstn count(channel_incoming before side))))
      (channel_consume before side count)
| channel_loss_step:forall before parent_count child_count,
    channel_operation tables channel before channel_interrupted
      {|channel_to_parent:=skipn parent_count(channel_to_parent before);
        channel_to_child:=skipn child_count(channel_to_child before)|}
| channel_frame_step:forall before,
    channel_operation tables channel before channel_passed before.

Definition grant_write_owned tables parent channel event:=
  forall actor descriptor bytes lost binding,
    event=channel_sent actor descriptor bytes lost ->tables actor descriptor=Some binding ->
    descriptor_object binding=release_endpoint channel parent_endpoint ->actor=parent.

Inductive channel_execution channel:ChannelBuffers->
    list((nat->DescriptorTable)*ChannelEvent)->ChannelBuffers->Prop:=
| channel_execution_nil:forall buffers,channel_execution channel buffers[]buffers
| channel_execution_cons:forall before tables event middle rest after,
    channel_operation tables channel before event middle ->channel_execution channel middle rest after ->
    channel_execution channel before((tables,event)::rest)after.

Definition channel_sent_before parent(history:list((nat->DescriptorTable)*ChannelEvent)) byte:=
  channel_writer byte=parent /\exists tables fd bytes lost,
    In(tables,channel_sent parent fd bytes lost)history /\In(channel_value byte)bytes.
Definition channel_queue_provenance parent history buffers:=
  Forall(channel_sent_before parent history)(channel_to_child buffers).

Lemma channel_history_extend parent history observation byte:
  channel_sent_before parent history byte ->channel_sent_before parent(history++[observation])byte.
Proof.
  intros[WRITER[tables[fd[bytes[lost[EARLIER MEMBER]]]]]];split;[exact WRITER|].
  exists tables,fd,bytes,lost;split;[apply in_or_app;left;exact EARLIER|exact MEMBER].
Qed.

Lemma channel_skipn_preserves(P:ChannelByte->Prop)count bytes:
  Forall P bytes ->Forall P(skipn count bytes).
Proof. revert bytes;induction count;intros bytes GOOD;[exact GOOD|];destruct bytes;cbn;[constructor|].
  inversion GOOD;subst;apply IHcount;assumption.
Qed.

Theorem channel_operation_preserves_provenance tables parent channel before event after history:
  channel_queue_provenance parent history before ->grant_write_owned tables parent channel event ->
  channel_operation tables channel before event after ->
  channel_queue_provenance parent(history++[(tables,event)])after.
Proof.
  intros PRIOR OWNED STEP;inversion STEP;subst;unfold channel_queue_provenance in *.
  - destruct side;cbn[channel_enqueue].
    + apply Forall_app;split.
      * eapply Forall_impl;[|exact PRIOR];intros byte GOOD;apply channel_history_extend;exact GOOD.
      * destruct H as[binding[PRESENT OBJECT]].
        assert(SENDER:actor=parent)by(eapply OWNED;[reflexivity|exact PRESENT|exact OBJECT]);subst actor.
        apply Forall_forall;intros byte MEMBER;unfold channel_tag in MEMBER.
        apply in_map_iff in MEMBER as[value[SAME MEMBER]];subst byte;split;[reflexivity|].
        exists tables,fd,bytes,lost;split;[apply in_or_app;right;left;reflexivity|exact MEMBER].
    + eapply Forall_impl;[|exact PRIOR];intros byte GOOD;apply channel_history_extend;exact GOOD.
  - destruct side;cbn[channel_consume].
    + eapply Forall_impl;[|exact PRIOR];intros byte GOOD;apply channel_history_extend;exact GOOD.
    + apply channel_skipn_preserves;eapply Forall_impl;[|exact PRIOR];
        intros byte GOOD;apply channel_history_extend;exact GOOD.
  - cbn;apply channel_skipn_preserves;eapply Forall_impl;[|exact PRIOR];
      intros byte GOOD;apply channel_history_extend;exact GOOD.
  - eapply Forall_impl;[|exact PRIOR];intros byte GOOD;apply channel_history_extend;exact GOOD.
Qed.

Theorem private_channel_trace_provenance parent channel before history events after:
  channel_queue_provenance parent history before ->
  Forall(fun observation=>grant_write_owned(fst observation)parent channel(snd observation))events ->
  channel_execution channel before events after ->channel_queue_provenance parent(history++events)after.
Proof.
  intros PRIOR OWNED RUN;revert history PRIOR OWNED;induction RUN;intros history PRIOR OWNED.
  - rewrite app_nil_r;exact PRIOR.
  - inversion OWNED;subst.
    replace(history++(tables,event)::rest)with((history++[(tables,event)])++rest)
      by(rewrite <-app_assoc;reflexivity).
    apply IHRUN;[eapply channel_operation_preserves_provenance;eassumption|assumption].
Qed.


Definition channel_actor_eq_dec(a b:nat):{a=b}+{a<>b}.
Proof.
  exact(Nat.eq_dec a b).
Defined.

Theorem no_other_grant_endpoint_produces_owner tables parent channel event:
  (forall actor fd binding,actor<>parent ->tables actor fd=Some binding ->
    descriptor_object binding<>release_endpoint channel parent_endpoint) ->
  grant_write_owned tables parent channel event.
Proof.
  intros EXCLUDED actor fd bytes lost binding SAME PRESENT OBJECT.
  destruct(channel_actor_eq_dec actor parent)as[SENDER|FOREIGN];[exact SENDER|].
  exfalso;eapply EXCLUDED;eassumption.
Qed.

Lemma channel_firstn_member(P:ChannelByte->Prop) count bytes:
  Forall P bytes ->Forall P(firstn count bytes).
Proof.
  revert bytes;induction count;intros bytes GOOD;[constructor|].
  destruct bytes;cbn;[constructor|];inversion GOOD;subst;constructor;[assumption|apply IHcount;assumption].
Qed.

Theorem private_read_byte_has_parent_write parent channel history before tables actor fd wanted bytes after byte:
  Forall(fun observation=>grant_write_owned(fst observation)parent channel(snd observation))history ->
  channel_execution channel channel_empty history before ->
  (exists binding,tables actor fd=Some binding /\
    descriptor_object binding=release_endpoint channel child_endpoint) ->
  channel_operation tables channel before(channel_read actor fd wanted bytes)after ->
  In byte bytes ->exists source_tables source_fd sent lost,
    In(source_tables,channel_sent parent source_fd sent lost)history /\In byte sent.
Proof.
  intros OWNED RUN CHILD READ MEMBER.
  assert(ORIGINS:channel_queue_provenance parent history before).
  { exact(private_channel_trace_provenance parent channel channel_empty[]history before
      (Forall_nil _)OWNED RUN). }
  inversion READ;subst.
  destruct CHILD as[child_binding[CHILD_FD CHILD_OBJECT]].
  match goal with BINDING:exists binding,tables actor fd=Some binding /\
    descriptor_object binding=release_endpoint channel side|-_=>
    destruct BINDING as[read_binding[READ_FD READ_OBJECT]]end.
  assert(BINDING:child_binding=read_binding)by congruence;subst child_binding.
  assert(SIDE:side=child_endpoint)by(congruence);subst side.
  cbn[channel_incoming]in MEMBER;apply in_map_iff in MEMBER as[queued[VALUE QUEUED]].
  unfold channel_queue_provenance in ORIGINS.
  pose proof(channel_firstn_member(channel_sent_before parent history)count(channel_to_child before)ORIGINS)
    as PREFIX.
  apply Forall_forall with(x:=queued)in PREFIX;[|exact QUEUED].
  destruct PREFIX as[WRITER[source_tables[source_fd[sent[lost[EARLIER SENT]]]]]].
  exists source_tables,source_fd,sent,lost;split;[exact EARLIER|rewrite <-VALUE;exact SENT].
Qed.
