(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-entry.release: Recover the real positive-fork parent return before its checked setup. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import IO Machine LibraryMachine ProcessEffects ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine.
From EntryNamespace Require Import NamespaceMachine NamespaceStructure NamespaceAllocation NamespacePaths
  NamespaceAdmission NamespaceParentEntry NamespaceCaller NamespaceBorrow NamespaceMemory NamespaceChildResult NamespaceTLS.
Import ListNotations.
Open Scope Z_scope.

Definition child_pid_assignment:=Sassign(Ederef(Etempvar _child(tptr tint))tint)(Etempvar _forked tint).

Lemma positive_fork_store_frontier pair le memory k returned:
  namespace_first_call_path namespace_ge
    (fun endpoint=>endpoint=State f_create_entry_child child_pid_assignment(Kseq(child_tail 9(fn_body f_create_entry_child))k)
      (child_env pair)(child_fork_return_env le returned)memory)5
    (Returnstate(Vint returned)(child_fork_cont pair le k)memory).
Proof.
  unfold child_fork_cont,child_fork_set,child_fork_return_env,child_pid_assignment,child_tail;cbn[fn_body].
  admission_frontier_route;admission_frontier_route;admission_frontier_set.
  - apply old_expression_value,value_temp;apply PTree.gss.
  - admission_frontier_route;admission_frontier_route;apply namespace_first_call_stop;reflexivity.
Qed.

Lemma positive_fork_close_frontier pair le memory k returned failure:
  le!_forked=Some(Vint returned) ->le!_failure=Some(Vint failure) ->returned<>Int.zero ->
  namespace_first_call_path namespace_ge
    (fun endpoint=>endpoint=Callstate close_definition[Vint failure](child_failure_close_cont pair le k)memory)6
    (State f_create_entry_child Sskip(Kseq(child_tail 9(fn_body f_create_entry_child))k)(child_env pair)le memory).
Proof.
  intros FORKED FAILURE NONZERO.
  assert(CLOSE:(child_env pair)!_close=None)by(apply child_nonlocal_bindings;discriminate).
  unfold child_failure_close_cont,child_return,child_tail;cbn[fn_body].
  admission_frontier_route;admission_frontier_route.
  eapply namespace_first_call_next;[intros;discriminate|apply certified_if_edge with(v:=Vint Int.zero)(b:=false)|].
  - eapply binary_expression_value;[apply old_expression_value,value_temp;exact FORKED|
      apply old_expression_value,value_int|].
    change(Some(Val.of_bool(Int.eq returned Int.zero))=Some(Vint Int.zero)).
    rewrite Int.eq_false by exact NONZERO;reflexivity.
  - reflexivity.
  - admission_frontier_route;admission_frontier_route;admission_frontier_call _close.
    + child_argument;apply no_argument_values.
    + apply namespace_first_call_stop;reflexivity.
Qed.

Lemma positive_fork_return_frontier pair le memory k returned:
  namespace_first_call_path namespace_ge
    (fun endpoint=>endpoint=State f_create_entry_child(Sreturn(Some(Econst_int Int.zero tint)))k(child_env pair)le memory)2
    (Returnstate returned(child_failure_close_cont pair le k)memory).
Proof.
  unfold child_failure_close_cont,child_return,child_phase,child_tail;cbn[fn_body].
  admission_frontier_route;admission_frontier_route;apply namespace_first_call_stop;reflexivity.
Qed.

Lemma actual_child_zero_return cell pair le memory k events called arguments continuation final:
  namespace_steps namespace_ge cell
    (live(State f_create_entry_child(Sreturn(Some(Econst_int Int.zero tint)))k(child_env pair)le memory))events
    (live(Callstate called arguments continuation final)) ->
  exists after rest,events=namespace_source_event::rest /\
    Mem.free_list memory(blocks_of_env namespace_ge(child_env pair))=Some after /\
    namespace_steps namespace_ge cell
      (live(State f_create_entry_child(Sreturn(Some(Econst_int Int.zero tint)))k(child_env pair)le memory))
      [namespace_source_event](live(Returnstate(Vint Int.zero)(call_cont k)after)) /\
    namespace_steps namespace_ge cell(live(Returnstate(Vint Int.zero)(call_cont k)after))rest
      (live(Callstate called arguments continuation final)).
Proof.
  intro RUN;inversion RUN;subst;try discriminate.
  destruct(namespace_internal_step_exact namespace_ge cell
    (State f_create_entry_child(Sreturn(Some(Econst_int Int.zero tint)))k(child_env pair)le memory)
    event middle I H)as[original[EVENT REAL]].
  inversion REAL;subst;try contradiction;try discriminate;
    try match goal with B:boundary _ _ _|-_=>inversion B end.
  - match goal with SOURCE:step2 _ _ _ _|-_=>inversion SOURCE;subst end.
    all:try solve[match goal with BAD:_=_\/_=_|-_=>destruct BAD;discriminate end].
    match goal with VALUE:eval_expr _ _ _ _ (Econst_int Int.zero tint)_|-_=>inversion VALUE;subst end.
    all:try match goal with LOCATION:eval_lvalue _ _ _ _ (Econst_int _ _) _ _ _|-_=>inversion LOCATION end.
    all:match goal with CAST:sem_cast _ _ _ _=Some _|-_=>cbn[sem_cast classify_cast]in CAST;inversion CAST;subst end.
    all:do 2 eexists;split;[reflexivity|];split;[eassumption|];
      split;[econstructor;[eassumption|constructor]|eassumption].
  - match goal with REST:namespace_steps _ _ (dead _) _ _|-_=>
      destruct(namespace_dead_steps _ _ _ _ _ REST)as[EMPTY IMPOSSIBLE];discriminate end.
Qed.

Theorem actual_positive_fork_parent_return cell pair le before k returned failure pid
    events called arguments continuation final:
  le!_child=Some(Vptr pid Ptrofs.zero) ->le!_failure=Some(Vint failure) ->returned<>Int.zero ->
  pid<>tls_block cell ->pid<>pair ->called<>close_definition ->
  namespace_steps namespace_ge cell(live(Returnstate(Vint returned)(child_fork_cont pair le k)before))events
    (live(Callstate called arguments continuation final)) ->
  exists prefix after suffix,Forall(fun event=>namespace_parent_prelude_event event=true)prefix /\
    Forall(namespace_parent_closes_from[failure])prefix /\events=prefix++suffix /\
    namespace_steps namespace_ge cell(live(Returnstate(Vint returned)(child_fork_cont pair le k)before))prefix
      (live(Returnstate(Vint Int.zero)(call_cont k)after)) /\
    namespace_steps namespace_ge cell(live(Returnstate(Vint Int.zero)(call_cont k)after))suffix
      (live(Callstate called arguments continuation final)) /\
    Mem.load Mint32 after pid 0=Some(Vint returned) /\
    (forall object offset value,object<>pid ->object<>pair ->object<>tls_block cell ->
      Mem.load Mint32 before object offset=Some value ->Mem.load Mint32 after object offset=Some value).
Proof.
  intros CHILD FAILURE NONZERO PID_TLS PID_PAIR OUTSIDE RUN.
  destruct(namespace_first_callback_exact _ _ _ _ _ _ _ _ _ _
    (positive_fork_store_frontier pair le before k returned)RUN)
    as[endpoint[store_rest[S0[SAME[P0 STORE_RUN]]]]];subst endpoint.
  pose(temps:=child_fork_return_env le returned).
  assert(LOCATION:location_value namespace_ge(child_env pair)temps before
    (Ederef(Etempvar _child(tptr tint))tint)pid Ptrofs.zero).
  { apply pointer_location_value,old_expression_value,value_temp;unfold temps,child_fork_return_env;WriteAll.lookup. }
  assert(EXPRESSION:expression_value namespace_ge(child_env pair)temps before(Etempvar _forked tint)(Vint returned)).
  { apply old_expression_value,value_temp;unfold temps,child_fork_return_env;WriteAll.lookup. }
  destruct(namespace_actual_assignment namespace_ge cell f_create_entry_child
    (Ederef(Etempvar _child(tptr tint))tint)(Etempvar _forked tint)
    (Kseq(child_tail 9(fn_body f_create_entry_child))k)(child_env pair)temps before pid Ptrofs.zero
    (Vint returned)(Vint returned)store_rest called arguments continuation final LOCATION EXPRESSION eq_refl STORE_RUN)
    as[assigned[after_store[S1[ASSIGN NEXT]]]].
  assert(STORE:Mem.store Mint32 before pid 0(Vint returned)=Some assigned).
  { inversion ASSIGN;subst;cbn in *;try discriminate.
    match goal with MODE:By_value Mint32=By_value _|-_=>inversion MODE;subst end;assumption. }
  assert(FORKED:temps!_forked=Some(Vint returned))by(unfold temps,child_fork_return_env;WriteAll.lookup).
  assert(FAILURE':temps!_failure=Some(Vint failure))by(unfold temps,child_fork_return_env;WriteAll.lookup).
  destruct(namespace_first_callback_exact _ _ _ _ _ _ _ _ _ _
    (positive_fork_close_frontier pair temps assigned k returned failure FORKED FAILURE' NONZERO)NEXT)
    as[endpoint[close_rest[S2[SAME[P2 CLOSE_RUN]]]]];subst endpoint.
  destruct(namespace_close_until_call _ _ _ _ _ _ _ _ _ _ OUTSIDE CLOSE_RUN)
    as[waits[reply[closed[after_close[S3[EFFECT[P3 CONTINUE]]]]]]].
  destruct(namespace_first_callback_exact _ _ _ _ _ _ _ _ _ _
    (positive_fork_return_frontier pair temps closed k(Vint(close_value reply)))CONTINUE)
    as[endpoint[return_rest[S4[SAME[P4 RETURN_RUN]]]]];subst endpoint.
  destruct(actual_child_zero_return _ _ _ _ _ _ _ _ _ _ RETURN_RUN)
    as[after[suffix[S5[FREE[P5 TAIL]]]]].
  pose(prefix:=((((repeat namespace_source_event 5++[namespace_source_event])++repeat namespace_source_event 6)++
    (repeat(namespace_process(process_entry(entry_library library_wait)))waits++[namespace_close_event failure reply]))++
    repeat namespace_source_event 2)++[namespace_source_event]).
  assert(PREFIX:namespace_steps namespace_ge cell
    (live(Returnstate(Vint returned)(child_fork_cont pair le k)before))prefix
    (live(Returnstate(Vint Int.zero)(call_cont k)after))).
  { unfold prefix;eapply namespace_steps_append;[|exact P5].
    eapply namespace_steps_append;[|exact P4].
    eapply namespace_steps_append;[|exact P3].
    eapply namespace_steps_append;[|exact P2].
    eapply namespace_steps_append;[exact P0|].
    econstructor;[|constructor].
    apply namespace_process_step,process_entry_step,entry_library_step,original_step,internal;[exact I|].
    eapply step_assign;[exact(proj1 LOCATION)|exact(proj1 EXPRESSION)|reflexivity|exact ASSIGN]. }
  assert(EVENTS:events=prefix++suffix).
  { rewrite S0,S1,S2,S3,S4,S5;unfold prefix;repeat rewrite <-app_assoc;reflexivity. }
  change(Mem.free_list closed[(pair,0,8)]=Some after)in FREE;cbn in FREE.
  destruct(Mem.free closed pair 0 8)as[freed|]eqn:FREE_ONE;[|discriminate].
  inversion FREE;subst after.
  exists prefix,freed,suffix;split.
  - unfold prefix;repeat rewrite Forall_app;repeat split;
      try(apply namespace_parent_prelude_repeat;reflexivity);repeat constructor.
  - split.
    + unfold prefix.
      repeat first[apply Forall_app;split|
        apply namespace_parent_closes_repeat;apply namespace_parent_closes_source|
        apply namespace_parent_closes_repeat;apply namespace_parent_closes_wait|
        apply Forall_cons|apply Forall_nil|apply namespace_parent_closes_source|
        apply namespace_parent_closes_close;cbn;auto].
    + split;[exact EVENTS|]. split;[exact PREFIX|]. split;[exact TAIL|]. split.
      * eapply namespace_free_preserves_load;[exact FREE_ONE|exact PID_PAIR|].
    eapply namespace_close_preserves_load;[exact EFFECT|exact PID_TLS|].
    erewrite Mem.load_store_same by exact STORE;reflexivity.
      * intros object offset value NOT_PID NOT_PAIR NOT_TLS LOAD.
    eapply namespace_free_preserves_load;[exact FREE_ONE|exact NOT_PAIR|].
    eapply namespace_close_preserves_load;[exact EFFECT|exact NOT_TLS|].
    erewrite Mem.load_store_other;[exact LOAD|exact STORE|left;exact NOT_PID].
Qed.
