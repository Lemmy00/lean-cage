(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-entry.release: The actual socketpair birth resets its queues before the shared fork. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Values Memory Events Clight.
Require Import IO Machine LibraryMachine.
From EntryNative Require Import NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine.
From EntryNamespace Require Import NamespaceObjects NamespaceMachine NamespaceKernel NamespaceWorldTrace
  NamespaceTraceRegion NamespaceChannel NamespaceSocket NamespaceForkWorld NamespaceMemory NamespaceChildResult
  NamespaceForkPrefix NamespacePaths.
Import ListNotations.
Open Scope Z_scope.

Definition NamespaceQueues:=nat->ChannelBuffers.
Definition namespace_partial_io event:=match namespace_socket_io event with
  |Some io=>source_socket_lost io|None=>false end.
Definition namespace_queue_neutral event:=match event with
  |namespace_paired _ _ _ _ _ _ _ _|namespace_pair_lost _ _ _ _ _=>false
  |_=>match namespace_socket_io event with Some _=>false|None=>true end end.

(* These are individual Linux operations. Successful socketpair creates a new
   empty object even if an observation label was previously used. No source
   ordering, fork frontier, owner, or whole-run queue conclusion is a field. *)
Record NamespaceQueueContract:Type:={
  queued_return:NamespaceWorld->NamespaceQueues->namespace_event->NamespaceWorld->NamespaceQueues->Prop;
  queued_kernel:forall world queues event after result,
    queued_return world queues event after result ->namespace_kernel_event world event after;
  queued_pair:forall world queues output offset first second after result,
    queued_return world queues
      (namespace_paired(Int.repr 1)(Int.repr 524289)Int.zero output offset Int.zero first second)after result ->
    exists created,socketpair_table(namespace_table world)first second created(namespace_table after) /\
      forall query,result query=if Nat.eqb query created then channel_empty else queues query;
  queued_frame:forall world queues event after result,
    queued_return world queues event after result ->namespace_queue_neutral event=true ->result=queues
}.

(* A compatible broader model supplies useful witnesses. The non-pair case
   retains arbitrary queue effects for I/O, interruption and lost pair creation. *)
Inductive namespace_queue_primitive:
    NamespaceWorld->NamespaceQueues->namespace_event->NamespaceWorld->NamespaceQueues->Prop:=
| namespace_queue_created:forall before queues output offset first second created table,
    socketpair_table(namespace_table before)first second created table ->
    Forall(fun outside=>channel_absent outside created)(namespace_ambient before) ->
    namespace_queue_primitive before queues
      (namespace_paired(Int.repr 1)(Int.repr 524289)Int.zero output offset Int.zero first second)
      (namespace_retable before table)
      (fun query=>if Nat.eqb query created then channel_empty else queues query)
| namespace_queue_other:forall before queues event after result,
    namespace_kernel_event before event after ->
    (forall output offset first second,event<>
      namespace_paired(Int.repr 1)(Int.repr 524289)Int.zero output offset Int.zero first second) ->
    (namespace_queue_neutral event=true ->result=queues) ->
    namespace_queue_primitive before queues event after result.

Definition namespace_queue_model:NamespaceQueueContract.
Proof.
  refine{|queued_return:=namespace_queue_primitive|}.
  - intros before queues event after result OPERATION;inversion OPERATION;subst.
    + eapply namespace_kernel_pair_success;eassumption.
    + assumption.
  - intros before queues output offset first second after result OPERATION;inversion OPERATION;subst.
    + eexists;split;[eassumption|reflexivity].
    + exfalso;match goal with EXCLUDED:forall _ _ _ _,_<>_|-_=>eapply EXCLUDED;reflexivity end.
  - intros before queues event after result OPERATION NEUTRAL;inversion OPERATION;subst.
    + discriminate.
    + eauto.
Defined.

Theorem namespace_queue_model_operation before queues event after:
  namespace_kernel_event before event after ->
  exists result,namespace_queue_primitive before queues event after result.
Proof.
  intro KERNEL;inversion KERNEL;subst.
  { eexists;eapply namespace_queue_created;eassumption. }
  all:exists queues;eapply namespace_queue_other;[exact KERNEL| |intros;reflexivity].
  all:intros output' offset' first' second' SAME;try discriminate.
  all:match goal with PASSIVE:namespace_passive_event _=true|-_=>
    rewrite SAME in PASSIVE;discriminate end.
Qed.

Inductive namespace_queue_steps(platform:NamespaceQueueContract):
    NamespaceWorld->NamespaceQueues->list namespace_event->NamespaceWorld->NamespaceQueues->Prop:=
| namespace_queue_nil:forall world queues,namespace_queue_steps platform world queues[]world queues
| namespace_queue_cons:forall world queues event middle changed rest after result,
    queued_return platform world queues event middle changed ->
    namespace_queue_steps platform middle changed rest after result ->
    namespace_queue_steps platform world queues(event::rest)after result.

Theorem namespace_queue_steps_kernel platform before queues events after result:
  namespace_queue_steps platform before queues events after result ->namespace_kernel_steps before events after.
Proof. intro RUN;induction RUN;[constructor|econstructor;[eapply queued_kernel;eassumption|exact IHRUN]]. Qed.

Theorem namespace_queue_model_kernel_lift before events after:
  namespace_kernel_steps before events after ->forall queues,
  exists result,namespace_queue_steps namespace_queue_model before queues events after result.
Proof.
  intro RUN;induction RUN;intro queues.
  - exists queues;constructor.
  - destruct(namespace_queue_model_operation _ queues _ _ H)as[changed OPERATION].
    destruct(IHRUN changed)as[result REST].
    exists result;econstructor;[exact OPERATION|exact REST].
Qed.

Lemma namespace_queue_unselected_neutral event:
  namespace_fd_event event=false ->namespace_partial_io event=false ->namespace_queue_neutral event=true.
Proof.
  unfold namespace_fd_event,namespace_partial_io,namespace_queue_neutral,namespace_socket_io,process_socket_io.
  repeat match goal with
  |e:namespace_event|-_=>destruct e;cbn;try discriminate;try reflexivity
  |e:process_event|-_=>destruct e;cbn;try discriminate;try reflexivity
  |e:entry_handoff_event|-_=>destruct e;cbn;try discriminate;try reflexivity
  |e:library_event|-_=>destruct e;cbn;try discriminate;try reflexivity
  |e:Machine.event|-_=>destruct e;cbn;try discriminate;try reflexivity
  |r:reply|-_=>destruct r;cbn;try discriminate;try reflexivity
  end.
Qed.

Lemma namespace_partial_io_step_dead ge cell before event target:
  namespace_step ge cell before event target ->namespace_partial_io event=true ->
  exists after,target=dead after.
Proof.
  intros STEP PARTIAL;unfold namespace_partial_io,namespace_socket_io,process_socket_io in PARTIAL.
  repeat match goal with
  |e:namespace_event|-_=>destruct e;cbn in PARTIAL;try discriminate
  |e:process_event|-_=>destruct e;cbn in PARTIAL;try discriminate
  |e:entry_handoff_event|-_=>destruct e;cbn in PARTIAL;try discriminate
  |e:library_event|-_=>destruct e;cbn in PARTIAL;try discriminate
  |e:Machine.event|-_=>destruct e;cbn in PARTIAL;try discriminate
  |r:reply|-_=>destruct r;cbn in PARTIAL;try discriminate
  end.
  inversion STEP;subst;try discriminate.
  match goal with PROCESS:process_step _ _ _ _ _|-_=>inversion PROCESS;subst;try discriminate end.
  match goal with ENTRY:entry_handoff_step _ _ _ _ _|-_=>inversion ENTRY;subst;try discriminate end.
  match goal with LIBRARY:library_step _ _ _ _ _|-_=>inversion LIBRARY;subst;try discriminate end.
  match goal with ORIGINAL:Machine.step _ _ _ _ _|-_=>inversion ORIGINAL;subst;try discriminate end.
  eexists;reflexivity.
Qed.

Theorem namespace_live_prefix_has_no_partial_io ge cell before events final:
  namespace_steps ge cell before events(live final) ->
  Forall(fun event=>namespace_partial_io event=false)events.
Proof.
  revert before;induction events as[|event rest IH];intros before RUN;[constructor|].
  inversion RUN as[|initial observed middle remaining last STEP TAIL];subst.
  constructor.
  - destruct(namespace_partial_io event)eqn:PARTIAL;[|reflexivity].
    destruct(namespace_partial_io_step_dead _ _ _ _ _ STEP PARTIAL)as[memory TARGET];subst middle.
    destruct(namespace_dead_steps _ _ _ _ _ TAIL)as[EMPTY IMPOSSIBLE];discriminate.
  - eapply IH;exact TAIL.
Qed.

Theorem namespace_queue_filter_is_same_run platform before queues events after result:
  Forall(fun event=>namespace_partial_io event=false)events ->
  namespace_queue_steps platform before queues events after result ->
  namespace_queue_steps platform before queues(namespace_fd_events events)after result.
Proof.
  intros LIVE RUN;revert LIVE;induction RUN;intros LIVE;[constructor|].
  inversion LIVE;subst;unfold namespace_fd_events in *;cbn.
  destruct(namespace_fd_event event)eqn:SELECTED.
  - econstructor;[exact H|apply IHRUN;assumption].
  - assert(WORLD:middle=world).
    { eapply namespace_unselected_kernel_frame;[eapply queued_kernel;exact H|exact SELECTED]. }
    assert(QUEUES:changed=queues).
    { eapply queued_frame;[exact H|apply namespace_queue_unselected_neutral;assumption]. }
    subst middle changed;apply IHRUN;assumption.
Qed.

Theorem namespace_queue_neutral_run platform before queues events after result:
  Forall(fun event=>namespace_queue_neutral event=true)events ->
  namespace_queue_steps platform before queues events after result ->result=queues.
Proof.
  intros NEUTRAL RUN;revert NEUTRAL;induction RUN;intros NEUTRAL;[reflexivity|].
  inversion NEUTRAL;subst;rewrite(IHRUN H3);eapply queued_frame;eassumption.
Qed.

Theorem actual_channel_prefix_has_empty_birth platform before queues after result output first second failure reply:
  0<=Int.signed failure ->
  namespace_queue_steps platform before queues
    (child_channel_prefix_events output first second failure reply)after result ->
  exists channel,result channel=channel_empty /\
    namespace_table after first=Some(endpoint_binding channel parent_endpoint) /\
    namespace_table after failure=Some(endpoint_binding channel child_endpoint).
Proof.
  intros FAILURE RUN;unfold child_channel_prefix_events in RUN.
  inversion RUN;subst;clear RUN.
  match goal with PAIR:queued_return _ _ _ (namespace_paired _ _ _ _ _ _ _ _) _ _|-_=>
    destruct(queued_pair _ _ _ _ _ _ _ _ _ PAIR)as[channel[PAIRTABLE RESET]]end.
  assert(QUEUES:result=changed).
  { eapply namespace_queue_neutral_run;[|eassumption];repeat constructor;reflexivity. }
  assert(EMPTY:result channel=channel_empty).
  { rewrite QUEUES,RESET,Nat.eqb_refl;reflexivity. }
  match goal with REST:namespace_queue_steps _ _ _ _ _ _|-_=>
    pose proof(namespace_queue_steps_kernel _ _ _ _ _ _ REST)as KERNEL end.
  match goal with PAIR:queued_return _ _ _ (namespace_paired _ _ _ _ _ _ _ _) _ _|-_=>
    pose proof(queued_kernel _ _ _ _ _ _ PAIR)as PAIR_KERNEL end.
  destruct(namespace_pair_kernel_details _ _ _ _ _ PAIR_KERNEL)
    as[original[paired[ORIGINAL[AMBIENT WORLD]]]];subst.
  change(socketpair_table(namespace_table before)first second channel paired)in PAIRTABLE.
  destruct(pair_child_binding _ _ _ _ _ PAIRTABLE)as[PAIR_CHILD PAIR_PARENT].
  destruct(pair_child_binding _ _ _ _ _ ORIGINAL)as[ORIGINAL_CHILD ORIGINAL_PARENT].
  unfold endpoint_binding in PAIR_PARENT,ORIGINAL_PARENT.
  assert(CHANNEL:original=channel)by congruence;subst original.
  inversion KERNEL;subst;clear KERNEL.
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
  match goal with REST:namespace_kernel_steps _ [] _|-_=>inversion REST;subst;clear REST end.
  cbn[namespace_retable]in DUPTABLE,CLOSETABLE.
  destruct(local_child_channel _ _ _ _ _ _ _ _ _ PAIRTABLE DUPTABLE CLOSETABLE)
    as[D0[D1[MINIMUM[PEER[CHILD FLAGS]]]]].
  exists channel;split;[exact EMPTY|].
  change(inherited first=Some(endpoint_binding channel parent_endpoint) /\
    inherited failure=Some(endpoint_binding channel child_endpoint));auto.
Qed.

Theorem actual_common_fork_has_empty_channel platform scope start events before_world before_queues
    fork_world fork_queues first second failure reply le memory:
  scope_history scope=[] ->
  ChildPrefixResult scope(namespace_fd_events events)
    (Callstate namespace_fork_definition[]
      (child_fork_cont(storage_pair(scope_storage scope))le(scope_continuation scope))memory) ->
  namespace_fd_events events=child_signal_log scope first second failure reply ->
  namespace_steps NamespaceStructure.namespace_ge(scope_cell scope)start events
    (live(Callstate namespace_fork_definition[]
      (child_fork_cont(storage_pair(scope_storage scope))le(scope_continuation scope))memory)) ->
  namespace_queue_steps platform before_world before_queues events fork_world fork_queues ->
  exists channel inherited,
    fork_world=child_fork_world before_world inherited /\
    inherited first=Some(endpoint_binding channel parent_endpoint) /\
    inherited failure=Some(endpoint_binding channel child_endpoint) /\fork_queues channel=channel_empty.
Proof.
  intros HISTORY FRONTIER LOG SOURCE QUEUES.
  pose proof(namespace_queue_steps_kernel _ _ _ _ _ _ QUEUES)as KERNEL.
  destruct(source_common_fork_world _ _ _ _ _ _ _ _ _ _ HISTORY FRONTIER LOG KERNEL)
    as[channel[inherited[WORLD[DEFAULT[MASK[D0[D1[MINIMUM[PEER[CHILD REST]]]]]]]]]].
  assert(FILTERED:namespace_queue_steps platform before_world before_queues
      (child_channel_prefix_events(storage_pair(scope_storage scope))first second failure reply)fork_world fork_queues).
  { pose proof(namespace_queue_filter_is_same_run _ _ _ _ _ _
      (namespace_live_prefix_has_no_partial_io _ _ _ _ _ SOURCE)QUEUES)as FILTERED.
    rewrite LOG in FILTERED.
    unfold child_signal_log,child_mask_log,child_closed_log,child_duplicate_log,child_pair_log in FILTERED.
    rewrite HISTORY in FILTERED;cbn in FILTERED;exact FILTERED. }
  destruct(actual_channel_prefix_has_empty_birth platform before_world before_queues fork_world fork_queues
      (storage_pair(scope_storage scope))first second failure reply ltac:(lia)FILTERED)
    as[created[EMPTY[ACTUAL_PEER ACTUAL_CHILD]]].
  assert(TABLE:namespace_table fork_world=inherited).
  { rewrite WORLD;unfold child_fork_world,namespace_default_action;rewrite Int.eq_true;reflexivity. }
  rewrite TABLE,PEER in ACTUAL_PEER.
  unfold endpoint_binding in ACTUAL_PEER;inversion ACTUAL_PEER;subst created.
  exists channel,inherited;auto.
Qed.
