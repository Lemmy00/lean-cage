(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-entry.release: A returned byte retains its exact send occurrence and parent-endpoint binding. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers Values.
From EntryNamespace Require Import NamespaceObjects NamespaceChannel NamespaceGrant NamespacePhysical.
From EntryProcess Require Import ProcessImport.
Import ListNotations.

Definition channel_byte_origin channel history byte:=exists tables actor fd sent lost binding,
  In(tables,channel_sent actor fd sent lost)history /\tables actor fd=Some binding /\
  descriptor_object binding=release_endpoint channel parent_endpoint /\
  In(channel_value byte)sent /\channel_writer byte=actor.
Definition channel_bytes_origin channel history buffers:=
  Forall(channel_byte_origin channel history)(channel_to_child buffers).

Lemma channel_byte_origin_extend channel history observation byte:
  channel_byte_origin channel history byte ->channel_byte_origin channel(history++[observation])byte.
Proof.
  intros[tables[actor[fd[sent[lost[binding[MEMBER[PRESENT[OBJECT[BYTE WRITER]]]]]]]]]].
  exists tables,actor,fd,sent,lost,binding;split;[apply in_or_app;left;exact MEMBER|auto].
Qed.

Theorem channel_operation_retains_byte_origins channel tables before event after history:
  channel_bytes_origin channel history before ->channel_operation tables channel before event after ->
  channel_bytes_origin channel(history++[(tables,event)])after.
Proof.
  intros PRIOR STEP;inversion STEP;subst;unfold channel_bytes_origin in *.
  - destruct side;cbn[channel_enqueue].
    + apply Forall_app;split.
      * eapply Forall_impl;[|exact PRIOR];intros byte ORIGIN;apply channel_byte_origin_extend;exact ORIGIN.
      * destruct H as[binding[PRESENT OBJECT]].
        apply Forall_forall;intros byte MEMBER;unfold channel_tag in MEMBER.
        apply in_map_iff in MEMBER as[value[SAME MEMBER]];subst byte.
        exists tables,actor,fd,bytes,lost,binding.
        split;[apply in_or_app;right;left;reflexivity|]. repeat split;assumption.
    + eapply Forall_impl;[|exact PRIOR];intros byte ORIGIN;apply channel_byte_origin_extend;exact ORIGIN.
  - destruct side;cbn[channel_consume].
    + eapply Forall_impl;[|exact PRIOR];intros byte ORIGIN;apply channel_byte_origin_extend;exact ORIGIN.
    + apply channel_skipn_preserves;eapply Forall_impl;[|exact PRIOR];
        intros byte ORIGIN;apply channel_byte_origin_extend;exact ORIGIN.
  - cbn;apply channel_skipn_preserves;eapply Forall_impl;[|exact PRIOR];
      intros byte ORIGIN;apply channel_byte_origin_extend;exact ORIGIN.
  - eapply Forall_impl;[|exact PRIOR];intros byte ORIGIN;apply channel_byte_origin_extend;exact ORIGIN.
Qed.

Theorem channel_execution_retains_byte_origins channel before history events after:
  channel_bytes_origin channel history before ->channel_execution channel before events after ->
  channel_bytes_origin channel(history++events)after.
Proof.
  intros INITIAL RUN;revert history INITIAL;induction RUN;intros history INITIAL.
  - rewrite app_nil_r;exact INITIAL.
  - replace(history++(tables,event)::rest)with((history++[(tables,event)])++rest)
      by(rewrite <-app_assoc;reflexivity).
    apply IHRUN;eapply channel_operation_retains_byte_origins;eassumption.
Qed.

Theorem read_byte_has_exact_parent_endpoint_send channel history before tables actor fd wanted bytes after byte:
  channel_execution channel channel_empty history before ->
  (exists binding,tables actor fd=Some binding /\descriptor_object binding=release_endpoint channel child_endpoint) ->
  channel_operation tables channel before(channel_read actor fd wanted bytes)after ->In byte bytes ->
  exists source_tables sender source_fd sent lost binding,
    In(source_tables,channel_sent sender source_fd sent lost)history /\
    source_tables sender source_fd=Some binding /\descriptor_object binding=release_endpoint channel parent_endpoint /\
    In byte sent.
Proof.
  intros RUN CHILD READ MEMBER.
  pose proof(channel_execution_retains_byte_origins channel channel_empty[]history before(Forall_nil _)RUN)as ORIGINS.
  cbn[app]in ORIGINS.
  inversion READ;subst.
  destruct CHILD as[child_binding[PRESENT OBJECT]].
  match goal with BINDING:exists binding,tables actor fd=Some binding /\
    descriptor_object binding=release_endpoint channel side|-_=>destruct BINDING as[read_binding[READ_FD READ_OBJECT]]end.
  assert(SAME:child_binding=read_binding)by congruence;subst child_binding.
  assert(SIDE:side=child_endpoint)by congruence;subst side.
  cbn[channel_incoming]in MEMBER;apply in_map_iff in MEMBER as[queued[VALUE QUEUED]].
  pose proof(channel_firstn_member(channel_byte_origin channel history)count(channel_to_child before)ORIGINS)as PREFIX.
  rewrite Forall_forall in PREFIX;destruct(PREFIX _ QUEUED)
    as[source_tables[sender[source_fd[sent[lost[binding[EARLIER[FD[ENDPOINT[BYTE WRITER]]]]]]]]]].
  exists source_tables,sender,source_fd,sent,lost,binding;repeat split;try assumption;congruence.
Qed.

Lemma byte_origin_some_injective(A:Type)(left right:A):Some left=Some right ->left=right.
Proof. intro SAME;injection SAME;trivial. Qed.

Theorem actual_read_has_exact_prior_send channel ticks after read_position tick actor fd wanted bytes binding:
  physical_queue_execution channel channel_empty ticks after ->nth_error ticks read_position=Some tick ->
  ProcessImport.socket tick=LeanCage_Entry_CallerPhysical_SocketObservation_read actor
    (NamespaceHandles.native_descriptor_number fd)(Lean.Nat_of_nat wanted)bytes ->
  physical_bytes_valid bytes=true ->(0<=Int.signed fd)%Z ->
  physical_tick_table tick(Lean.nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor))fd=Some binding ->
  descriptor_object binding=release_endpoint channel child_endpoint ->In(Byte.repr 165)(physical_bytes bytes) ->
  exists send_position sent_tick sender source_fd sent lost source_binding,
    nth_error ticks send_position=Some sent_tick /\(send_position<read_position)%nat /\
    physical_tick_projection channel sent_tick=(physical_tick_table sent_tick,channel_sent sender source_fd sent lost) /\
    physical_tick_table sent_tick sender source_fd=Some source_binding /\
    descriptor_object source_binding=release_endpoint channel parent_endpoint /\In(Byte.repr 165)sent.
Proof.
  intros RUN SELECTED SOCKET BYTES NONNEGATIVE PRESENT OBJECT BYTE.
  destruct(nth_error_split _ _ SELECTED)as[prefix[suffix[TICKS POSITION]]];subst ticks.
  destruct(physical_queue_execution_split _ _ _ _ _ RUN)as[before[PRIOR REMAINING]].
  inversion REMAINING;subst.
  pose proof(physical_tick_read_projection _ _ _ _ _ _ _ SOCKET BYTES NONNEGATIVE PRESENT OBJECT)as READ.
  match goal with OPERATION:physical_queue_operation _ _ _ _|-_=>
    unfold physical_queue_operation in OPERATION;rewrite READ in OPERATION;cbn beta iota zeta in OPERATION end.
  destruct(read_byte_has_exact_parent_endpoint_send channel(map(physical_tick_projection channel)prefix)before
    (physical_tick_table tick)(Lean.nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor))fd wanted(physical_bytes bytes)
    _ (Byte.repr 165)(physical_queue_execution_projects _ _ _ _ PRIOR)
      ltac:(exists binding;auto)ltac:(eassumption)BYTE)
    as[source_tables[sender[source_fd[sent[lost[source_binding[EARLIER[FD[ENDPOINT SENT]]]]]]]]].
  apply In_nth_error in EARLIER as[position OBSERVED];rewrite nth_error_map in OBSERVED.
  destruct(nth_error prefix position)as[raw|]eqn:RAW;[|discriminate].
  change(Some(physical_tick_projection channel raw)=Some(source_tables,channel_sent sender source_fd sent lost))in OBSERVED.
  pose proof(byte_origin_some_injective _ _ _ OBSERVED)as PROJECT.
  assert(TABLES:Datatypes.fst(physical_tick_projection channel raw)=physical_tick_table raw).
  { unfold physical_tick_projection;destruct(ProcessImport.socket raw);
      cbn beta iota zeta;try reflexivity;destruct(physical_bytes_valid _);reflexivity. }
  pose proof(f_equal(Datatypes.fst)PROJECT)as SAME_TABLE;change(Datatypes.fst(physical_tick_projection channel raw)=source_tables)in SAME_TABLE.
  rewrite TABLES in SAME_TABLE;subst source_tables.
  assert(BEFORE:(position<length prefix)%nat).
  { apply nth_error_Some;rewrite RAW;discriminate. }
  exists position,raw,sender,source_fd,sent,lost,source_binding.
  split;[rewrite nth_error_app1 by exact BEFORE;exact RAW|]. split;[exact BEFORE|].
  split;[exact PROJECT|]. auto.
Qed.
