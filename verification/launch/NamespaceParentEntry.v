(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Derive the parent's actual setup frontier after its own local fork. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps LibraryMachine StoreSteps LocalAccess CallAccess WriteAll ProcessEffects.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine.
From EntryNamespace Require Import NamespaceMachine NamespaceStructure NamespacePaths NamespaceCaller
  NamespaceLibrary NamespaceAdmission NamespaceRelease NamespaceParentSafety NamespaceTLS NamespacePrepared.
Import ListNotations.
Open Scope Z_scope.

Lemma namespace_close_until_call ge cell fd k before events called arguments continuation final:
  called<>close_definition ->
  namespace_steps ge cell(live(Callstate close_definition[Vint fd]k before))events
    (live(Callstate called arguments continuation final)) ->
  exists waits reply after rest,
    events=repeat(namespace_process(process_entry(entry_library library_wait)))waits++
      namespace_close_event fd reply::rest /\close_effect cell before reply after /\
    namespace_steps ge cell(live(Callstate close_definition[Vint fd]k before))
      (repeat(namespace_process(process_entry(entry_library library_wait)))waits++[namespace_close_event fd reply])
      (live(Returnstate(Vint(close_value reply))k after)) /\
    namespace_steps ge cell(live(Returnstate(Vint(close_value reply))k after))rest
      (live(Callstate called arguments continuation final)).
Proof.
  intro OUTSIDE;revert before;induction events as[|event events IH];intros before RUN.
  - inversion RUN;subst;contradiction.
  - inversion RUN as[|initial observed middle remaining last STEP TAIL];subst.
  destruct(namespace_close_cases ge cell fd k before event middle STEP)
    as[[reply[after[EFFECT[EVENT TARGET]]]]|[[EVENT TARGET]|[EVENT TARGET]]];subst event middle.
  + exists 0%nat,reply,after,events;cbn;split;[reflexivity|].
    split;[exact EFFECT|]. split;[econstructor;[exact STEP|constructor]|exact TAIL].
  + destruct(IH _ TAIL)as[waits[reply[after[rest[EVENTS[EFFECT[PREFIX CONTINUE]]]]]]].
    exists(S waits),reply,after,rest;cbn;split;[rewrite EVENTS;reflexivity|].
    split;[exact EFFECT|]. split;[econstructor;[exact STEP|exact PREFIX]|exact CONTINUE].
  + destruct(namespace_dead_steps _ _ _ _ _ TAIL)as[EMPTY IMPOSSIBLE];discriminate.
Qed.

Lemma namespace_parent_first_close e le memory k input:
  e!_close=None ->le!_input=Some(Vint input) ->
  namespace_first_call_path namespace_ge
    (fun endpoint=>endpoint=Callstate close_definition[Vint input]
      (namespace_close_cont e(namespace_created_env le)11 k)memory)9
    (Returnstate(Vint Int.zero)(namespace_creation_cont e le k)memory).
Proof.
  intros CLOSE INPUT.
  unfold namespace_creation_cont,namespace_creation_set,namespace_created_env,
    namespace_close_cont,namespace_tail,child_tail;cbn[fn_body].
  admission_frontier_route;admission_frontier_route;admission_frontier_set.
  - apply old_expression_value,value_temp;apply PTree.gss.
  - admission_frontier_route;admission_frontier_route.
    eapply namespace_first_call_next;[intros;discriminate|apply certified_if_edge with(v:=Vint Int.zero)(b:=false)|].
    + apply old_expression_value,value_temp;apply PTree.gss.
    + reflexivity.
    + admission_frontier_route;admission_frontier_route;admission_frontier_call _close.
      * child_argument;apply no_argument_values.
      * apply namespace_first_call_stop;reflexivity.
Qed.

Lemma namespace_parent_next_close e le memory k index id fd returned:
  namespace_tail(S index)=Ssequence
    (Scall None(Evar _close(Tfunction[tint]tint cc_default))[Etempvar id tint])
    (namespace_tail(S(S index))) ->
  e!_close=None ->le!id=Some(Vint fd) ->
  namespace_first_call_path namespace_ge
    (fun endpoint=>endpoint=Callstate close_definition[Vint fd]
      (namespace_close_cont e le(S index)k)memory)4
    (Returnstate returned(namespace_close_cont e le index k)memory).
Proof.
  intros SOURCE CLOSE VALUE;unfold namespace_close_cont.
  admission_frontier_route;admission_frontier_route;rewrite SOURCE.
  admission_frontier_route;admission_frontier_call _close.
  - child_argument;apply no_argument_values.
  - apply namespace_first_call_stop;reflexivity.
Qed.

Definition namespace_parent_status_assignment :=
  Sassign(Evar _status tint)(Econst_int Int.zero tint).

Lemma namespace_parent_before_status e le memory k childobject child returned:
  e!_child=Some(childobject,tint) ->Mem.load Mint32 memory childobject 0=Some(Vint child) ->
  0<=Int.signed child ->
  namespace_first_call_path namespace_ge
    (fun endpoint=>endpoint=State f_namespace_init namespace_parent_status_assignment
      (Kseq(namespace_tail 17)k)e(namespace_parent_checked_env le child)memory)9
    (Returnstate returned(namespace_close_cont e le 14 k)memory).
Proof.
  intros CHILD PID NONNEGATIVE.
  unfold namespace_close_cont,namespace_parent_checked_env,namespace_parent_status_assignment,
    namespace_tail,child_tail;cbn[fn_body].
  admission_frontier_route;admission_frontier_route;admission_frontier_route;admission_frontier_route;
    admission_frontier_set.
  - eapply namespace_local_int_value;[exact CHILD|exact PID].
  - admission_frontier_route.
    eapply namespace_first_call_next;[intros;discriminate|apply certified_if_edge with(v:=Vint Int.zero)(b:=false)|].
    + eapply binary_expression_value;[apply old_expression_value,value_temp;apply PTree.gss|
        apply old_expression_value,value_int|].
      change(Some(Val.of_bool(Int.lt child Int.zero))=Some(Vint Int.zero)).
      unfold Int.lt;rewrite Int.signed_zero;destruct(zlt(Int.signed child)0);[lia|reflexivity].
    + reflexivity.
    + admission_frontier_route;admission_frontier_route;apply namespace_first_call_stop;reflexivity.
Qed.

Definition namespace_parent_wait:=namespace_process(process_entry(entry_library library_wait)).
Definition namespace_parent_prelude_event event:=
  match event with
  |namespace_process(process_entry(entry_library(original_event(source_step _))))=>true
  |namespace_process(process_entry(entry_library library_wait))=>true
  |namespace_process(process_entry(entry_library(close_returned _ _)))=>true
  |_=>false
  end.

Definition namespace_parent_closed_fd event:=
  match event with
  |namespace_process(process_entry(entry_library(close_returned fd _)))=>Some fd
  |_=>None
  end.
Definition namespace_parent_closes_from descriptors event:=forall fd,
  namespace_parent_closed_fd event=Some fd ->In fd descriptors.

Lemma namespace_parent_closes_repeat event count descriptors:
  namespace_parent_closes_from descriptors event ->
  Forall(namespace_parent_closes_from descriptors)(repeat event count).
Proof.
  intro VALID;apply Forall_forall;intros observed MEMBER;apply repeat_spec in MEMBER;subst;exact VALID.
Qed.

Lemma namespace_parent_closes_weaken before after events:
  (forall fd,In fd before ->In fd after) ->
  Forall(namespace_parent_closes_from before)events ->Forall(namespace_parent_closes_from after)events.
Proof.
  intros INCLUDED CLOSED;apply Forall_forall;intros event MEMBER fd ACTUAL.
  apply INCLUDED;apply Forall_forall with(x:=event)in CLOSED;[exact(CLOSED fd ACTUAL)|exact MEMBER].
Qed.

Lemma namespace_parent_closes_source descriptors:
  namespace_parent_closes_from descriptors namespace_source_event.
Proof. intros fd IMPOSSIBLE;discriminate. Qed.
Lemma namespace_parent_closes_wait descriptors:
  namespace_parent_closes_from descriptors(namespace_process(process_entry(entry_library library_wait))).
Proof. intros fd IMPOSSIBLE;discriminate. Qed.
Lemma namespace_parent_closes_close descriptors fd reply:
  In fd descriptors ->namespace_parent_closes_from descriptors(namespace_close_event fd reply).
Proof.
  intros MEMBER actual SAME;change(Some fd=Some actual)in SAME;injection SAME as SAME;subst;exact MEMBER.
Qed.

Lemma namespace_parent_prelude_repeat event count:
  namespace_parent_prelude_event event=true ->
  Forall(fun observed=>namespace_parent_prelude_event observed=true)(repeat event count).
Proof.
  intro VALID;apply Forall_forall;intros observed MEMBER;apply repeat_spec in MEMBER;subst;exact VALID.
Qed.

Definition namespace_parent_close_log input output errors parent w0 r0 w1 r1 w2 r2 w3 r3:=
  repeat namespace_source_event 9++(repeat namespace_parent_wait w0++[namespace_close_event input r0])++
    repeat namespace_source_event 4++(repeat namespace_parent_wait w1++[namespace_close_event output r1])++
    repeat namespace_source_event 4++(repeat namespace_parent_wait w2++[namespace_close_event errors r2])++
    repeat namespace_source_event 4++(repeat namespace_parent_wait w3++[namespace_close_event parent r3]).

Lemma namespace_parent_close_log_closed input output errors parent w0 r0 w1 r1 w2 r2 w3 r3:
  Forall(namespace_parent_closes_from[input;output;errors;parent])
    (namespace_parent_close_log input output errors parent w0 r0 w1 r1 w2 r2 w3 r3).
Proof.
  unfold namespace_parent_close_log,namespace_parent_wait.
  repeat first[apply Forall_app;split|
    apply namespace_parent_closes_repeat;apply namespace_parent_closes_source|
    apply namespace_parent_closes_repeat;apply namespace_parent_closes_wait|
    apply Forall_cons|apply Forall_nil|apply namespace_parent_closes_close;cbn;tauto].
Qed.

Theorem actual_parent_closes_sources cell e le before k input output errors parent events called args cont final:
  e!_close=None ->le!_input=Some(Vint input) ->le!_output=Some(Vint output) ->
  le!_errors=Some(Vint errors) ->le!_parentfd=Some(Vint parent) ->
  called<>close_definition ->
  namespace_steps namespace_ge cell(live(Returnstate(Vint Int.zero)(namespace_creation_cont e le k)before))events
    (live(Callstate called args cont final)) ->
  exists w0 r0 m1 w1 r1 m2 w2 r2 m3 w3 r3 after rest,
    events=namespace_parent_close_log input output errors parent w0 r0 w1 r1 w2 r2 w3 r3++rest /\
    close_effect cell before r0 m1 /\close_effect cell m1 r1 m2 /\
    close_effect cell m2 r2 m3 /\close_effect cell m3 r3 after /\
    namespace_steps namespace_ge cell
      (live(Returnstate(Vint Int.zero)(namespace_creation_cont e le k)before))
      (namespace_parent_close_log input output errors parent w0 r0 w1 r1 w2 r2 w3 r3)
      (live(Returnstate(Vint(close_value r3))(namespace_close_cont e(namespace_created_env le)14 k)after)) /\
    namespace_steps namespace_ge cell
      (live(Returnstate(Vint(close_value r3))(namespace_close_cont e(namespace_created_env le)14 k)after))rest
      (live(Callstate called args cont final)).
Proof.
  intros CLOSE INPUT OUTPUT ERRORS PARENT OUTSIDE RUN.
  destruct(namespace_first_callback_exact _ _ _ _ _ _ _ _ _ _
    (namespace_parent_first_close e le before k input CLOSE INPUT)RUN)
    as[endpoint[first[S0[SAME[ROUTE0 TAIL0]]]]];subst endpoint.
  destruct(namespace_close_until_call _ _ _ _ _ _ _ _ _ _ OUTSIDE TAIL0)
    as[w0[r0[m1[rest1[C0[E0[STEP0 NEXT0]]]]]]].
  assert(OUTPUT0:(namespace_created_env le)!_output=Some(Vint output))by(unfold namespace_created_env;WriteAll.lookup).
  destruct(namespace_first_callback_exact _ _ _ _ _ _ _ _ _ _
    (namespace_parent_next_close e(namespace_created_env le)m1 k 11 _output output(Vint(close_value r0))
      ltac:(reflexivity)CLOSE OUTPUT0)NEXT0)as[endpoint[second[S1[SAME[ROUTE1 TAIL1]]]]];subst endpoint.
  destruct(namespace_close_until_call _ _ _ _ _ _ _ _ _ _ OUTSIDE TAIL1)
    as[w1[r1[m2[rest2[C1[E1[STEP1 NEXT1]]]]]]].
  assert(ERRORS0:(namespace_created_env le)!_errors=Some(Vint errors))by(unfold namespace_created_env;WriteAll.lookup).
  destruct(namespace_first_callback_exact _ _ _ _ _ _ _ _ _ _
    (namespace_parent_next_close e(namespace_created_env le)m2 k 12 _errors errors(Vint(close_value r1))
      ltac:(reflexivity)CLOSE ERRORS0)NEXT1)as[endpoint[third[S2[SAME[ROUTE2 TAIL2]]]]];subst endpoint.
  destruct(namespace_close_until_call _ _ _ _ _ _ _ _ _ _ OUTSIDE TAIL2)
    as[w2[r2[m3[rest3[C2[E2[STEP2 NEXT2]]]]]]].
  assert(PARENT0:(namespace_created_env le)!_parentfd=Some(Vint parent))by(unfold namespace_created_env;WriteAll.lookup).
  destruct(namespace_first_callback_exact _ _ _ _ _ _ _ _ _ _
    (namespace_parent_next_close e(namespace_created_env le)m3 k 13 _parentfd parent(Vint(close_value r2))
      ltac:(reflexivity)CLOSE PARENT0)NEXT2)as[endpoint[fourth[S3[SAME[ROUTE3 TAIL3]]]]];subst endpoint.
  destruct(namespace_close_until_call _ _ _ _ _ _ _ _ _ _ OUTSIDE TAIL3)
    as[w3[r3[after[rest[C3[E3[STEP3 NEXT3]]]]]]].
  exists w0,r0,m1,w1,r1,m2,w2,r2,m3,w3,r3,after,rest.
  split.
  - rewrite S0,C0,S1,C1,S2,C2,S3,C3;unfold namespace_parent_close_log,namespace_parent_wait.
    repeat rewrite <-app_assoc;reflexivity.
  - split;[exact E0|]. split;[exact E1|]. split;[exact E2|]. split;[exact E3|]. split;[|exact NEXT3].
    unfold namespace_parent_close_log,namespace_parent_wait.
    eapply namespace_steps_append;[exact ROUTE0|].
    eapply namespace_steps_append;[exact STEP0|].
    eapply namespace_steps_append;[exact ROUTE1|].
    eapply namespace_steps_append;[exact STEP1|].
    eapply namespace_steps_append;[exact ROUTE2|].
    eapply namespace_steps_append;[exact STEP2|].
    eapply namespace_steps_append;[exact ROUTE3|exact STEP3].
Qed.

Lemma namespace_parent_after_status e le memory k:
  namespace_first_call_path namespace_ge
    (fun endpoint=>endpoint=State f_namespace_init(namespace_tail 20)k e(namespace_admission_ready_env le)memory)10
    (State f_namespace_init Sskip(Kseq(namespace_tail 17)k)e le memory).
Proof.
  unfold namespace_admission_ready_env,namespace_tail,child_tail;cbn[fn_body].
  admission_frontier_route;admission_frontier_route;admission_frontier_set.
  - apply old_expression_value,value_int.
  - admission_frontier_route;admission_frontier_route;admission_frontier_set.
    + apply old_expression_value,value_int.
    + admission_frontier_route;admission_frontier_route;admission_frontier_set.
      * apply old_expression_value,value_int.
      * admission_frontier_route;apply namespace_first_call_stop;reflexivity.
Qed.

Definition namespace_parent_setup_env le child:=
  namespace_admission_ready_env(namespace_parent_checked_env(namespace_created_env le)child).

Lemma namespace_parent_setup_values le child report sequence:
  le!_report=Some(Vint report) ->le!_sequence=Some(Vlong sequence) ->
  (namespace_parent_setup_env le child)!_bad=Some(Vint Int.zero) /\
    (namespace_parent_setup_env le child)!_report=Some(Vint report) /\
    (namespace_parent_setup_env le child)!_sequence=Some(Vlong sequence).
Proof.
  intros REPORT SEQUENCE;unfold namespace_parent_setup_env,namespace_admission_ready_env,
    namespace_parent_checked_env,namespace_created_env;repeat split;WriteAll.lookup.
Qed.

Lemma namespace_close_chain_load cell before r0 m1 r1 m2 r2 m3 r3 after object offset value:
  close_effect cell before r0 m1 ->close_effect cell m1 r1 m2 ->
  close_effect cell m2 r2 m3 ->close_effect cell m3 r3 after ->
  object<>tls_block cell ->Mem.load Mint32 before object offset=Some value ->
  Mem.load Mint32 after object offset=Some value.
Proof.
  intros C0 C1 C2 C3 SEPARATE LOAD.
  eapply namespace_close_preserves_load;[exact C3|exact SEPARATE|].
  eapply namespace_close_preserves_load;[exact C2|exact SEPARATE|].
  eapply namespace_close_preserves_load;[exact C1|exact SEPARATE|].
  eapply namespace_close_preserves_load;[exact C0|exact SEPARATE|exact LOAD].
Qed.

(* The target can be the actual pending private write. No release invocation or
   initialized status cell is assumed: reaching that target forces these real
   close operations and the source status store first. *)
Theorem actual_parent_creation_reaches_setup cell e le before k input output errors parent childobject pipe status
    child peer cgroup checking report sequence events called args cont final:
  e!_close=None ->le!_input=Some(Vint input) ->le!_output=Some(Vint output) ->
  le!_errors=Some(Vint errors) ->le!_parentfd=Some(Vint parent) ->
  le!_report=Some(Vint report) ->le!_sequence=Some(Vlong sequence) ->
  e!_child=Some(childobject,tint) ->e!_pipefd=Some(pipe,tarray tint 2) ->e!_status=Some(status,tint) ->
  Mem.load Mint32 before childobject 0=Some(Vint child) ->0<=Int.signed child ->
  Mem.load Mint32 before pipe 0=Some(Vint peer) ->
  Mem.load Mint32 before(namespace_symbol _admission_cgroup)0=Some(Vint cgroup) ->
  Mem.load Mint32 before(namespace_symbol _preflight)0=Some(Vint checking) ->
  childobject<>tls_block cell ->pipe<>tls_block cell ->
  namespace_symbol _admission_cgroup<>tls_block cell ->namespace_symbol _preflight<>tls_block cell ->
  status<>childobject ->status<>pipe ->status<>namespace_symbol _admission_cgroup ->status<>namespace_symbol _preflight ->
  Mem.valid_block before(tls_block cell) ->called<>close_definition ->
  namespace_steps namespace_ge cell(live(Returnstate(Vint Int.zero)(namespace_creation_cont e le k)before))events
    (live(Callstate called args cont final)) ->
  exists prefix ready rest,
    Forall(fun event=>namespace_parent_prelude_event event=true)prefix /\
    Forall(namespace_parent_closes_from[input;output;errors;parent])prefix /\events=prefix++rest /\
    namespace_steps namespace_ge cell(live(Returnstate(Vint Int.zero)(namespace_creation_cont e le k)before))prefix
      (live(State f_namespace_init(namespace_tail 20)k e(namespace_parent_setup_env le child)ready)) /\
    namespace_steps namespace_ge cell
      (live(State f_namespace_init(namespace_tail 20)k e(namespace_parent_setup_env le child)ready))rest
      (live(Callstate called args cont final)) /\
    Mem.load Mint32 ready childobject 0=Some(Vint child) /\Mem.load Mint32 ready pipe 0=Some(Vint peer) /\
    Mem.load Mint32 ready(namespace_symbol _admission_cgroup)0=Some(Vint cgroup) /\
    Mem.load Mint32 ready(namespace_symbol _preflight)0=Some(Vint checking) /\
    Mem.load Mint32 ready status 0=Some(Vint Int.zero) /\Mem.valid_block ready(tls_block cell) /\
    (namespace_parent_setup_env le child)!_bad=Some(Vint Int.zero) /\
    (namespace_parent_setup_env le child)!_report=Some(Vint report) /\
    (namespace_parent_setup_env le child)!_sequence=Some(Vlong sequence).
Proof.
  intros CLOSE INPUT OUTPUT ERRORS PARENT REPORT SEQUENCE CHILD PIPE STATUS PID POSITIVE PEER CGROUP CHECK
    CHILD_TLS PIPE_TLS CGROUP_TLS CHECK_TLS STATUS_CHILD STATUS_PIPE STATUS_CGROUP STATUS_CHECK TLS OUTSIDE RUN.
  destruct(actual_parent_closes_sources _ _ _ _ _ _ _ _ _ _ _ _ _ _
    CLOSE INPUT OUTPUT ERRORS PARENT OUTSIDE RUN)
    as[w0[r0[m1[w1[r1[m2[w2[r2[m3[w3[r3[closed[rest
      [EVENTS[C0[C1[C2[C3[PREFIX CONTINUE]]]]]]]]]]]]]]]]]]].
  assert(PID4:Mem.load Mint32 closed childobject 0=Some(Vint child))
    by(eapply(namespace_close_chain_load cell before r0 m1 r1 m2 r2 m3 r3 closed);eassumption).
  assert(PEER4:Mem.load Mint32 closed pipe 0=Some(Vint peer))
    by(eapply(namespace_close_chain_load cell before r0 m1 r1 m2 r2 m3 r3 closed);eassumption).
  assert(CGROUP4:Mem.load Mint32 closed(namespace_symbol _admission_cgroup)0=Some(Vint cgroup))
    by(eapply(namespace_close_chain_load cell before r0 m1 r1 m2 r2 m3 r3 closed);eassumption).
  assert(CHECK4:Mem.load Mint32 closed(namespace_symbol _preflight)0=Some(Vint checking))
    by(eapply(namespace_close_chain_load cell before r0 m1 r1 m2 r2 m3 r3 closed);eassumption).
  destruct(namespace_first_callback_exact _ _ _ _ _ _ _ _ _ _
    (namespace_parent_before_status e(namespace_created_env le)closed k childobject child(Vint(close_value r3))
      CHILD PID4 POSITIVE)CONTINUE)as[endpoint[assignment_rest[STATUS_EVENTS[SAME[STATUS_PREFIX STATUS_RUN]]]]];subst endpoint.
  unfold namespace_parent_status_assignment in STATUS_RUN.
  assert(LOCATION:location_value namespace_ge e(namespace_parent_checked_env(namespace_created_env le)child)closed
    (Evar _status tint)status Ptrofs.zero).
  { apply local_location_value;exact STATUS. }
  assert(EXPRESSION:expression_value namespace_ge e(namespace_parent_checked_env(namespace_created_env le)child)closed
    (Econst_int Int.zero tint)(Vint Int.zero)).
  { apply old_expression_value,value_int. }
  destruct(namespace_actual_assignment namespace_ge cell f_namespace_init(Evar _status tint)(Econst_int Int.zero tint)
    (Kseq(namespace_tail 17)k)e(namespace_parent_checked_env(namespace_created_env le)child)closed status Ptrofs.zero
    (Vint Int.zero)(Vint Int.zero)assignment_rest called args cont final
    LOCATION EXPRESSION eq_refl STATUS_RUN)as[ready[remaining[STORE_EVENTS[ASSIGN AFTER_STORE]]]].
  assert(STORE:Mem.store Mint32 closed status 0(Vint Int.zero)=Some ready).
  { inversion ASSIGN;subst;cbn in *;try discriminate.
    match goal with MODE:By_value Mint32=By_value _|-_=>inversion MODE;subst end;assumption. }
  destruct(namespace_first_callback_exact _ _ _ _ _ _ _ _ _ _
    (namespace_parent_after_status e(namespace_parent_checked_env(namespace_created_env le)child)ready k)AFTER_STORE)
    as[endpoint[suffix[AFTER_EVENTS[SAME[AFTER_PREFIX SUFFIX]]]]];subst endpoint.
  set(log:=namespace_parent_close_log input output errors parent w0 r0 w1 r1 w2 r2 w3 r3).
  set(prefix:=log++repeat namespace_source_event 9++namespace_source_event::repeat namespace_source_event 10).
  assert(ACTUAL:namespace_steps namespace_ge cell
    (live(Returnstate(Vint Int.zero)(namespace_creation_cont e le k)before))prefix
    (live(State f_namespace_init(namespace_tail 20)k e(namespace_parent_setup_env le child)ready))).
  { unfold prefix; eapply namespace_steps_append;[exact PREFIX|].
    eapply namespace_steps_append;[exact STATUS_PREFIX|].
    econstructor;[|exact AFTER_PREFIX].
    apply namespace_process_step,process_entry_step,entry_library_step,original_step,internal;[exact I|].
    eapply step_assign;[exact(proj1 LOCATION)|exact(proj1 EXPRESSION)|reflexivity|exact ASSIGN]. }
  exists prefix,ready,suffix;split.
  - unfold prefix,log,namespace_parent_close_log,namespace_parent_wait.
    repeat rewrite Forall_app;repeat split;
      try(apply namespace_parent_prelude_repeat;reflexivity);repeat constructor.
  - split.
    + unfold prefix;apply Forall_app;split;[apply namespace_parent_close_log_closed|].
      apply Forall_app;split;[apply namespace_parent_closes_repeat;apply namespace_parent_closes_source|].
      constructor;[apply namespace_parent_closes_source|].
      apply namespace_parent_closes_repeat;apply namespace_parent_closes_source.
    + split;[rewrite EVENTS,STATUS_EVENTS,STORE_EVENTS,AFTER_EVENTS;unfold prefix,log;repeat rewrite <-app_assoc;reflexivity|].
      split;[exact ACTUAL|]. split;[exact SUFFIX|].
    split;[erewrite Mem.load_store_other;[exact PID4|exact STORE|left;congruence]|].
    split;[erewrite Mem.load_store_other;[exact PEER4|exact STORE|left;congruence]|].
    split;[erewrite Mem.load_store_other;[exact CGROUP4|exact STORE|left;congruence]|].
    split;[erewrite Mem.load_store_other;[exact CHECK4|exact STORE|left;congruence]|].
    split;[erewrite Mem.load_store_same by exact STORE;reflexivity|].
    split;[exact(namespace_steps_tls_valid namespace_ge cell _ _ _ ACTUAL TLS)|].
    apply namespace_parent_setup_values;assumption.
Qed.
