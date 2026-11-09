(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Extract the actual parent callbacks from every grant-producing source prefix. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess CallContexts WriteAll LibraryMachine.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessContexts.
From EntryReporting Require Import ResultLayout.
From EntryNamespace Require Import NamespaceMachine NamespaceStructure NamespacePaths NamespaceCaller
  NamespaceRelease NamespaceReporting NamespacePublication NamespaceContexts.
Import ListNotations.
Open Scope Z_scope.

Definition namespace_not_call (state:Clight.state) : Prop :=
  forall definition arguments continuation memory,
    state<>Callstate definition arguments continuation memory.

(* Proper nodes are not calls. Thus reaching any actual Callstate must cross
   this segment's exact first callback, including arbitrary terminal loss. *)
Inductive namespace_first_call_path ge (leaf:Clight.state->Prop) : nat->Clight.state->Prop :=
| namespace_first_call_stop : forall state,leaf state ->namespace_first_call_path ge leaf 0 state
| namespace_first_call_next : forall count state next,
    namespace_not_call state ->store_edge ge state next ->
    namespace_first_call_path ge leaf count next ->namespace_first_call_path ge leaf(S count)state.

Theorem namespace_first_callback_reached ge cell leaf count start
    events definition arguments continuation after :
  namespace_first_call_path ge leaf count start ->
  namespace_steps ge cell(live start)events(live(Callstate definition arguments continuation after)) ->
  exists prefix endpoint rest,
    events=prefix++rest /\leaf endpoint /\
    namespace_steps ge cell(live start)prefix(live endpoint) /\
    namespace_steps ge cell(live endpoint)rest(live(Callstate definition arguments continuation after)).
Proof.
  intros PATH;revert events;induction PATH as[state LEAF|count state next NOTCALL EDGE PATH IH];
    intros events RUN.
  - exists[],state,events;cbn;repeat split;try assumption;constructor.
  - inversion RUN;subst.
    + exfalso;eapply NOTCALL;reflexivity.
    + match goal with STEP:namespace_step _ _ _ _ _|-_=>
        destruct(namespace_store_edge_cases _ _ _ _ _ _ EDGE STEP)
          as[[EVENT TARGET]|[EVENT TARGET]]end;subst middle event.
      * destruct(IH _ H0)as[prefix[endpoint[remaining[EVENTS[LEAF[PREFIX SUFFIX]]]]]].
        exists(namespace_source_event::prefix),endpoint,remaining;cbn;split;[rewrite EVENTS;reflexivity|].
        split;[exact LEAF|]. split;[econstructor;eassumption|exact SUFFIX].
      * match goal with REST:namespace_steps _ _ (dead _) _ _|-_=>
          destruct(namespace_dead_steps _ _ _ _ _ REST)as[EVENTS IMPOSSIBLE];discriminate end.
Qed.

Fixpoint namespace_statement_weight (source:statement) : nat :=
  match source with
  |Ssequence first rest|Sifthenelse _ first rest|Sloop first rest=>
    S(namespace_statement_weight first+namespace_statement_weight rest)
  |Sswitch _ labels=>S(namespace_labels_weight labels)
  |Slabel _ body=>S(namespace_statement_weight body)
  |_=>1%nat
  end
with namespace_labels_weight (source:labeled_statements) : nat :=
  match source with
  |LSnil=>0%nat
  |LScons _ body rest=>S(namespace_statement_weight body+namespace_labels_weight rest)
  end.

Fixpoint namespace_cont_weight (continuation:cont) : nat :=
  match continuation with
  |Kstop=>0%nat
  |Kseq body rest=>S(namespace_statement_weight body+namespace_cont_weight rest)
  |Kloop1 first second rest|Kloop2 first second rest=>
    S(namespace_statement_weight first+namespace_statement_weight second+namespace_cont_weight rest)
  |Kswitch rest|Kcall _ _ _ _ rest=>S(namespace_cont_weight rest)
  end.

Lemma namespace_plug_cont_weight local suffix :
  namespace_cont_weight(plug_cont local suffix)=
    (namespace_cont_weight local+namespace_cont_weight suffix)%nat.
Proof. induction local;cbn;try rewrite IHlocal;lia. Qed.

Lemma namespace_plug_cannot_shrink local suffix definition arguments target after :
  (namespace_cont_weight target<namespace_cont_weight suffix)%nat ->
  plug_machine local suffix<>live(Callstate definition arguments target after).
Proof.
  intros SMALL SAME;destruct local as[state|memory];[destruct state as[fn body k env temps memory|
    called args k memory|value k memory];cbn in SAME|discriminate].
  all:try discriminate.
  inversion SAME;subst;pose proof(namespace_plug_cont_weight k suffix);lia.
Qed.

Theorem namespace_callback_returns_before_later_call ge cell definition arguments suffix before events
    target_definition target_arguments target_cont after :
  is_call_cont suffix ->
  (namespace_cont_weight target_cont<namespace_cont_weight suffix)%nat ->
  namespace_steps ge cell(live(Callstate definition arguments suffix before))events
    (live(Callstate target_definition target_arguments target_cont after)) ->
  exists prefix rest returned memory,
    events=prefix++rest /\
    namespace_steps ge cell(live(Callstate definition arguments Kstop before))prefix
      (live(Returnstate returned Kstop memory)) /\
    namespace_steps ge cell(live(Returnstate returned suffix memory))rest
      (live(Callstate target_definition target_arguments target_cont after)).
Proof.
  intros CALL SMALL RUN.
  destruct(namespace_caller_run_decomposition ge cell suffix(Callstate definition arguments Kstop before)
    events(live(Callstate target_definition target_arguments target_cont after))CALL RUN)
    as[[local[LOCAL SAME]]|[prefix[rest[returned[memory[EVENTS[LOCAL CONTINUE]]]]]]].
  - exfalso;eapply namespace_plug_cannot_shrink;[exact SMALL|symmetry;exact SAME].
  - exists prefix,rest,returned,memory;auto.
Qed.

Ltac admission_frontier_route :=
  eapply namespace_first_call_next;[intros;discriminate|apply unchanged_store_edge;WriteAll.structural|].
Ltac admission_frontier_set :=
  eapply namespace_first_call_next;[intros;discriminate|apply certified_set_edge|].
Ltac admission_frontier_call id :=
  eapply namespace_first_call_next;[intros;discriminate|namespace_call id|].

Theorem namespace_admit_first_callback e le memory k child cgroup status :
  e!_admit_child=None ->e!_status=Some(status,tint) ->
  le!_launch_child=Some(Vint child) ->le!_launch_cgroup=Some(Vint cgroup) ->
  namespace_first_call_path namespace_ge
    (fun endpoint=>endpoint=Callstate(Internal f_admit_child)
      [Vint child;Vint cgroup;Vptr status Ptrofs.zero](namespace_admit_cont e le child cgroup k)memory)3
    (State f_namespace_init(namespace_tail 24)k e le memory).
Proof.
  intros ADMIT STATUS CHILD CGROUP.
  unfold namespace_admit_cont,namespace_admit_guard,namespace_phase,namespace_tail,child_tail;cbn[fn_body].
  admission_frontier_route;admission_frontier_route;admission_frontier_call _admit_child.
  - child_argument;child_argument.
    eapply cons_argument_values with(v:=Vptr status Ptrofs.zero);
      [apply namespace_local_address;exact STATUS|reflexivity|apply no_argument_values].
  - apply namespace_first_call_stop;reflexivity.
Qed.

Lemma namespace_release_later_than_admit e le child peer e' le' child' cgroup k :
  (namespace_cont_weight(namespace_release_cont e le child peer k)<
    namespace_cont_weight(namespace_admit_cont e' le' child' cgroup k))%nat.
Proof.
  unfold namespace_release_cont,namespace_admit_cont;cbn[namespace_cont_weight];vm_compute;lia.
Qed.

Lemma namespace_release_later_than_close e le child peer e' le' cgroup k :
  (namespace_cont_weight(namespace_release_cont e le child peer k)<
    namespace_cont_weight(namespace_cgroup_close_cont e' le' cgroup k))%nat.
Proof.
  unfold namespace_release_cont,namespace_cgroup_close_cont;cbn[namespace_cont_weight];vm_compute;lia.
Qed.

Lemma namespace_release_later_than_result e le child peer e' le' k :
  (namespace_cont_weight(namespace_release_cont e le child peer k)<
    namespace_cont_weight(namespace_admission_result_cont e' le' k))%nat.
Proof.
  unfold namespace_release_cont,namespace_admission_result_cont;cbn[namespace_cont_weight];vm_compute;lia.
Qed.

Lemma namespace_release_later_than_clock e le child peer e' le' k :
  (namespace_cont_weight(namespace_release_cont e le child peer k)<
    namespace_cont_weight(namespace_admission_clock_cont e' le' k))%nat.
Proof.
  unfold namespace_release_cont,namespace_admission_clock_cont;cbn[namespace_cont_weight];vm_compute;lia.
Qed.

Lemma namespace_release_later_than_publication e le child peer e' le' sequence k :
  (namespace_cont_weight(namespace_release_cont e le child peer k)<
    namespace_cont_weight(namespace_publication_cont e' le' sequence k))%nat.
Proof.
  unfold namespace_release_cont,namespace_publication_cont;cbn[namespace_cont_weight];vm_compute;lia.
Qed.

Theorem namespace_admit_return_frontier e le memory k child cgroup returned :
  exists count,namespace_first_call_path namespace_ge
    (fun endpoint=>endpoint=State f_namespace_init(namespace_tail 25)k e
      (namespace_checked_admit_env le child cgroup returned)memory)count
    (Returnstate(Vint returned)(namespace_admit_cont e le child cgroup k)memory).
Proof.
  unfold namespace_admit_cont,namespace_checked_admit_env,namespace_after_admit_env.
  destruct(Int.eq_dec returned Int.zero)as[ZERO|NONZERO].
  - subst returned;rewrite Int.eq_true;eexists;admission_frontier_route;admission_frontier_route.
    eapply namespace_first_call_next;[intros;discriminate|apply certified_if_edge with(v:=Vint Int.zero)(b:=false)|].
    + apply old_expression_value,value_temp;apply PTree.gss.
    + reflexivity.
    + admission_frontier_route;apply namespace_first_call_stop;reflexivity.
  - rewrite Int.eq_false by exact NONZERO;eexists;admission_frontier_route;admission_frontier_route.
    eapply namespace_first_call_next;[intros;discriminate|apply certified_if_edge with(v:=Vint returned)(b:=true)|].
    + apply old_expression_value,value_temp;apply PTree.gss.
    + cbn;rewrite Int.eq_false by exact NONZERO;reflexivity.
    + admission_frontier_set;[apply old_expression_value,value_int|].
      admission_frontier_route;apply namespace_first_call_stop;reflexivity.
Qed.

Theorem namespace_cgroup_close_first_callback e le memory k cgroup :
  e!_close=None ->le!_launch_cgroup=Some(Vint cgroup) ->
  namespace_first_call_path namespace_ge
    (fun endpoint=>endpoint=Callstate close_definition[Vint cgroup]
      (namespace_cgroup_close_cont e le cgroup k)memory)3
    (State f_namespace_init(namespace_tail 25)k e le memory).
Proof.
  intros CLOSE VALUE;unfold namespace_cgroup_close_cont,namespace_cgroup_close_guard,
    namespace_phase,namespace_tail,child_tail;cbn[fn_body].
  admission_frontier_route;admission_frontier_route;admission_frontier_call _close.
  - child_argument;apply no_argument_values.
  - apply namespace_first_call_stop;reflexivity.
Qed.

Theorem namespace_cgroup_close_return_frontier e le memory k cgroup returned :
  exists count,namespace_first_call_path namespace_ge
    (fun endpoint=>endpoint=State f_namespace_init(namespace_tail 26)k e
      (namespace_checked_cgroup_close_env le cgroup returned)memory)count
    (Returnstate(Vint returned)(namespace_cgroup_close_cont e le cgroup k)memory).
Proof.
  unfold namespace_cgroup_close_cont,namespace_checked_cgroup_close_env,namespace_after_cgroup_close_env.
  destruct(Int.eq_dec returned Int.zero)as[ZERO|NONZERO].
  - subst returned;rewrite Int.eq_true;eexists;admission_frontier_route;admission_frontier_route.
    eapply namespace_first_call_next;[intros;discriminate|apply certified_if_edge with(v:=Vint Int.zero)(b:=false)|].
    + apply old_expression_value,value_temp;apply PTree.gss.
    + reflexivity.
    + admission_frontier_route;apply namespace_first_call_stop;reflexivity.
  - rewrite Int.eq_false by exact NONZERO;eexists;admission_frontier_route;admission_frontier_route.
    eapply namespace_first_call_next;[intros;discriminate|apply certified_if_edge with(v:=Vint returned)(b:=true)|].
    + apply old_expression_value,value_temp;apply PTree.gss.
    + cbn;rewrite Int.eq_false by exact NONZERO;reflexivity.
    + admission_frontier_set;[apply old_expression_value,value_int|].
      admission_frontier_route;apply namespace_first_call_stop;reflexivity.
Qed.

(* This starts at the actual captured-values source state; the callback transcript is
   extracted from that same run, rather than supplied as a callee hypothesis. *)
Theorem actual_parent_release_crosses_admit cell e le memory k child cgroup status
    final_env final_temps final_child peer events after :
  e!_admit_child=None ->e!_status=Some(status,tint) ->
  le!_launch_child=Some(Vint child) ->le!_launch_cgroup=Some(Vint cgroup) ->
  namespace_steps namespace_ge cell
    (live(State f_namespace_init(namespace_tail 24)k e le memory))events
    (live(Callstate(Internal f_release_child)[Vint final_child;Vint peer]
      (namespace_release_cont final_env final_temps final_child peer k)after)) ->
  exists before_call callback after_call returned result_memory,
    events=before_call++callback++after_call /\
    namespace_steps namespace_ge cell
      (live(State f_namespace_init(namespace_tail 24)k e le memory))before_call
      (live(Callstate(Internal f_admit_child)[Vint child;Vint cgroup;Vptr status Ptrofs.zero]
        (namespace_admit_cont e le child cgroup k)memory)) /\
    namespace_steps namespace_ge cell
      (live(Callstate(Internal f_admit_child)[Vint child;Vint cgroup;Vptr status Ptrofs.zero]Kstop memory))callback
      (live(Returnstate returned Kstop result_memory)) /\
    namespace_steps namespace_ge cell
      (live(Returnstate returned(namespace_admit_cont e le child cgroup k)result_memory))after_call
      (live(Callstate(Internal f_release_child)[Vint final_child;Vint peer]
        (namespace_release_cont final_env final_temps final_child peer k)after)).
Proof.
  intros ADMIT STATUS CHILD CGROUP RUN.
  destruct(namespace_first_callback_reached _ _ _ _ _ _ _ _ _ _
    (namespace_admit_first_callback e le memory k child cgroup status
      ADMIT STATUS CHILD CGROUP)RUN)
    as[prefix[endpoint[remaining[EVENTS[SAME[PREFIX TAIL]]]]]].
  subst endpoint.
  destruct(namespace_callback_returns_before_later_call namespace_ge cell
    (Internal f_admit_child)[Vint child;Vint cgroup;Vptr status Ptrofs.zero]
    (namespace_admit_cont e le child cgroup k)memory remaining
    (Internal f_release_child)[Vint final_child;Vint peer]
    (namespace_release_cont final_env final_temps final_child peer k)after
    I(namespace_release_later_than_admit final_env final_temps final_child peer e le child cgroup k)TAIL)
    as[callback[rest[returned[result_memory[CALLS[CALLEE CONTINUE]]]]]].
  exists prefix,callback,rest,returned,result_memory;split;[rewrite EVENTS,CALLS;reflexivity|auto].
Qed.


Lemma namespace_first_call_bind ge first_leaf last_leaf count start extra :
  namespace_first_call_path ge first_leaf count start ->
  (forall endpoint,first_leaf endpoint->namespace_first_call_path ge last_leaf extra endpoint) ->
  namespace_first_call_path ge last_leaf(count+extra)start.
Proof.
  intros PATH NEXT;induction PATH;cbn;[apply NEXT;assumption|].
  econstructor;eassumption.
Qed.

Theorem namespace_launch_capture_frontier e le memory k childobject pipe child peer cgroup checking :
  e!_child=Some(childobject,tint) ->e!_pipefd=Some(pipe,tarray tint 2) ->
  e!_admission_cgroup=None ->e!_preflight=None ->
  Mem.load Mint32 memory childobject 0=Some(Vint child) ->
  Mem.load Mint32 memory pipe 0=Some(Vint peer) ->
  Mem.load Mint32 memory(namespace_symbol _admission_cgroup)0=Some(Vint cgroup) ->
  Mem.load Mint32 memory(namespace_symbol _preflight)0=Some(Vint checking) ->
  namespace_first_call_path namespace_ge
    (fun endpoint=>endpoint=State f_namespace_init(namespace_tail 24)k e
      (namespace_launch_env le child peer cgroup checking)memory)12
    (State f_namespace_init(namespace_tail 20)k e le memory).
Proof.
  intros CHILD PIPE CGROUP PREFLIGHT PID PEER CGFD CHECK.
  unfold namespace_launch_env,namespace_tail,child_tail;cbn[fn_body].
  admission_frontier_route;admission_frontier_set.
  - eapply namespace_local_int_value;[exact CHILD|exact PID].
  - admission_frontier_route;admission_frontier_route;admission_frontier_set.
    + eapply location_read_value with(b:=pipe)(ofs:=Ptrofs.zero).
      * apply pointer_location_value;eapply binary_expression_value.
        -- eapply location_read_value;[apply local_location_value;exact PIPE|apply deref_loc_reference;reflexivity].
        -- apply old_expression_value,value_int.
        -- reflexivity.
      * eapply deref_loc_value;[reflexivity|exact PEER].
    + admission_frontier_route;admission_frontier_route;admission_frontier_set.
      * eapply namespace_global_int_value;[exact CGROUP|reflexivity|exact CGFD].
      * admission_frontier_route;admission_frontier_route;admission_frontier_set.
        -- eapply namespace_global_int_value;[exact PREFLIGHT|reflexivity|exact CHECK].
        -- admission_frontier_route;apply namespace_first_call_stop;reflexivity.
Qed.

Theorem namespace_captured_admit_first_callback e le memory k childobject pipe child peer cgroup checking status :
  e!_admit_child=None ->e!_status=Some(status,tint) ->
  e!_child=Some(childobject,tint) ->e!_pipefd=Some(pipe,tarray tint 2) ->
  e!_admission_cgroup=None ->e!_preflight=None ->
  Mem.load Mint32 memory childobject 0=Some(Vint child) ->
  Mem.load Mint32 memory pipe 0=Some(Vint peer) ->
  Mem.load Mint32 memory(namespace_symbol _admission_cgroup)0=Some(Vint cgroup) ->
  Mem.load Mint32 memory(namespace_symbol _preflight)0=Some(Vint checking) ->
  namespace_first_call_path namespace_ge
    (fun endpoint=>endpoint=Callstate(Internal f_admit_child)
      [Vint child;Vint cgroup;Vptr status Ptrofs.zero]
      (namespace_admit_cont e(namespace_launch_env le child peer cgroup checking)child cgroup k)memory)15
    (State f_namespace_init(namespace_tail 20)k e le memory).
Proof.
  intros ADMIT STATUS CHILD PIPE CGROUP PREFLIGHT PID PEER CGFD CHECK.
  replace 15%nat with(12+3)%nat by lia.
  eapply namespace_first_call_bind with(first_leaf:=fun endpoint=>
    endpoint=State f_namespace_init(namespace_tail 24)k e(namespace_launch_env le child peer cgroup checking)memory).
  - eapply namespace_launch_capture_frontier;eassumption.
  - intros endpoint SAME;subst endpoint.
    apply namespace_admit_first_callback;[exact ADMIT|exact STATUS| |];
      unfold namespace_launch_env;WriteAll.lookup.
Qed.

Theorem namespace_first_callback_exact ge cell leaf count start
    events definition arguments continuation after :
  namespace_first_call_path ge leaf count start ->
  namespace_steps ge cell(live start)events(live(Callstate definition arguments continuation after)) ->
  exists endpoint rest,
    events=repeat namespace_source_event count++rest /\leaf endpoint /\
    namespace_steps ge cell(live start)(repeat namespace_source_event count)(live endpoint) /\
    namespace_steps ge cell(live endpoint)rest(live(Callstate definition arguments continuation after)).
Proof.
  intros PATH;revert events;induction PATH as[state LEAF|count state next NOTCALL EDGE PATH IH];
    intros events RUN.
  - exists state,events;cbn;repeat split;try assumption;constructor.
  - inversion RUN;subst.
    + exfalso;eapply NOTCALL;reflexivity.
    + match goal with STEP:namespace_step _ _ _ _ _|-_=>
        destruct(namespace_store_edge_cases _ _ _ _ _ _ EDGE STEP)
          as[[EVENT TARGET]|[EVENT TARGET]]end;subst middle event.
      * destruct(IH _ H0)as[endpoint[remaining[EVENTS[LEAF[PREFIX SUFFIX]]]]].
        exists endpoint,remaining;cbn;split;[rewrite EVENTS;reflexivity|].
        split;[exact LEAF|]. split;[econstructor;eassumption|exact SUFFIX].
      * match goal with REST:namespace_steps _ _ (dead _) _ _|-_=>
          destruct(namespace_dead_steps _ _ _ _ _ REST)as[EVENTS IMPOSSIBLE];discriminate end.
Qed.

(* §FS-entry.release: The same actual run captures and passes its original selected values. *)
Theorem actual_parent_capture_and_admit cell e le memory k childobject pipe child peer cgroup checking status
    final_env final_temps final_child final_peer events after :
  e!_admit_child=None ->e!_status=Some(status,tint) ->
  e!_child=Some(childobject,tint) ->e!_pipefd=Some(pipe,tarray tint 2) ->
  e!_admission_cgroup=None ->e!_preflight=None ->
  Mem.load Mint32 memory childobject 0=Some(Vint child) ->
  Mem.load Mint32 memory pipe 0=Some(Vint peer) ->
  Mem.load Mint32 memory(namespace_symbol _admission_cgroup)0=Some(Vint cgroup) ->
  Mem.load Mint32 memory(namespace_symbol _preflight)0=Some(Vint checking) ->
  namespace_steps namespace_ge cell
    (live(State f_namespace_init(namespace_tail 20)k e le memory))events
    (live(Callstate(Internal f_release_child)[Vint final_child;Vint final_peer]
      (namespace_release_cont final_env final_temps final_child final_peer k)after)) ->
  exists callback after_call returned result_memory,
    events=repeat namespace_source_event 15++callback++after_call /\
    namespace_steps namespace_ge cell
      (live(Callstate(Internal f_admit_child)[Vint child;Vint cgroup;Vptr status Ptrofs.zero]Kstop memory))callback
      (live(Returnstate returned Kstop result_memory)) /\
    namespace_steps namespace_ge cell
      (live(Returnstate returned
        (namespace_admit_cont e(namespace_launch_env le child peer cgroup checking)child cgroup k)result_memory))after_call
      (live(Callstate(Internal f_release_child)[Vint final_child;Vint final_peer]
        (namespace_release_cont final_env final_temps final_child final_peer k)after)).
Proof.
  intros ADMIT STATUS CHILD PIPE CGROUP PREFLIGHT PID PEER CGFD CHECK RUN.
  destruct(namespace_first_callback_exact _ _ _ _ _ _ _ _ _ _
    (namespace_captured_admit_first_callback e le memory k childobject pipe child peer cgroup checking status
      ADMIT STATUS CHILD PIPE CGROUP PREFLIGHT PID PEER CGFD CHECK)RUN)
    as[endpoint[remaining[EVENTS[SAME[PREFIX TAIL]]]]].
  subst endpoint.
  destruct(namespace_callback_returns_before_later_call namespace_ge cell
    (Internal f_admit_child)[Vint child;Vint cgroup;Vptr status Ptrofs.zero]
    (namespace_admit_cont e(namespace_launch_env le child peer cgroup checking)child cgroup k)memory remaining
    (Internal f_release_child)[Vint final_child;Vint final_peer]
    (namespace_release_cont final_env final_temps final_child final_peer k)after
    I(namespace_release_later_than_admit final_env final_temps final_child final_peer e
      (namespace_launch_env le child peer cgroup checking)child cgroup k)TAIL)
    as[callback[rest[returned[result_memory[CALLS[CALLEE CONTINUE]]]]]].
  exists callback,rest,returned,result_memory;split;[rewrite EVENTS,CALLS;reflexivity|auto].
Qed.

Lemma namespace_admit_retains_values le child peer cgroup checking returned :
  namespace_launch_values le child peer cgroup checking ->
  namespace_launch_values(namespace_checked_admit_env le child cgroup returned)child peer cgroup checking.
Proof.
  unfold namespace_launch_values;intros[CHILD[PEER[CGROUP CHECK]]];repeat split;
    unfold namespace_checked_admit_env;destruct(Int.eq returned Int.zero);
    unfold namespace_after_admit_env,namespace_admit_env;WriteAll.lookup.
Qed.

Lemma namespace_close_retains_values le child peer cgroup checking returned :
  namespace_launch_values le child peer cgroup checking ->
  namespace_launch_values(namespace_checked_cgroup_close_env le cgroup returned)child peer cgroup checking.
Proof.
  unfold namespace_launch_values;intros[CHILD[PEER[CGROUP CHECK]]];repeat split;
    unfold namespace_checked_cgroup_close_env;destruct(Int.eq returned Int.zero);
    unfold namespace_after_cgroup_close_env,namespace_cgroup_close_env;WriteAll.lookup.
Qed.

Lemma namespace_clock_retains_values le child peer cgroup checking milliseconds :
  namespace_launch_values le child peer cgroup checking ->
  namespace_launch_values(namespace_checked_clock_env le milliseconds)child peer cgroup checking.
Proof.
  unfold namespace_launch_values;intros[CHILD[PEER[CGROUP CHECK]]];repeat split;
    unfold namespace_checked_clock_env;destruct(Int64.eq milliseconds Int64.zero);
    unfold namespace_admission_clock_env;WriteAll.lookup.
Qed.

Lemma namespace_publication_retains_values le child peer cgroup checking sequence returned :
  namespace_launch_values le child peer cgroup checking ->
  namespace_launch_values(namespace_checked_publication_env le sequence returned)child peer cgroup checking.
Proof.
  unfold namespace_launch_values;intros[CHILD[PEER[CGROUP CHECK]]];repeat split;
    unfold namespace_checked_publication_env;destruct(Int.eq returned Int.zero);
    unfold namespace_publication_return_env,namespace_publication_call_env;WriteAll.lookup.
Qed.

Lemma successful_admit_guard_requires_return_zero le child cgroup returned :
  (namespace_checked_admit_env le child cgroup returned)!_bad=Some(Vint Int.zero) ->
  returned=Int.zero /\le!_bad=Some(Vint Int.zero).
Proof.
  unfold namespace_checked_admit_env;destruct(Int.eq_dec returned Int.zero)as[ZERO|NONZERO].
  - subst returned;rewrite Int.eq_true;unfold namespace_after_admit_env,namespace_admit_env.
    repeat rewrite PTree.gso by discriminate;auto.
  - rewrite Int.eq_false by exact NONZERO;rewrite PTree.gss;discriminate.
Qed.

Lemma successful_close_guard_requires_return_zero le cgroup returned :
  (namespace_checked_cgroup_close_env le cgroup returned)!_bad=Some(Vint Int.zero) ->
  returned=Int.zero /\le!_bad=Some(Vint Int.zero).
Proof.
  unfold namespace_checked_cgroup_close_env;destruct(Int.eq_dec returned Int.zero)as[ZERO|NONZERO].
  - subst returned;rewrite Int.eq_true;unfold namespace_after_cgroup_close_env,namespace_cgroup_close_env.
    repeat rewrite PTree.gso by discriminate;auto.
  - rewrite Int.eq_false by exact NONZERO;rewrite PTree.gss;discriminate.
Qed.

(* Successful later calls force this source assignment to have executed. The
   store/copy is recovered from that actual step; it is not a callee frame. *)
Theorem namespace_actual_assignment ge cell fn lhs rhs k e le before
    block offset value cast_value events called arguments continuation final :
  location_value ge e le before lhs block offset ->
  expression_value ge e le before rhs value ->
  sem_cast value(typeof rhs)(typeof lhs)before=Some cast_value ->
  namespace_steps ge cell(live(State fn(Sassign lhs rhs)k e le before))events
    (live(Callstate called arguments continuation final)) ->
  exists after rest,
    events=namespace_source_event::rest /\
    assign_loc ge(typeof lhs)before block offset Full cast_value after /\
    namespace_steps ge cell(live(State fn Sskip k e le after))rest
      (live(Callstate called arguments continuation final)).
Proof.
  intros[LOCATION UNIQUE_LOCATION][EXPRESSION UNIQUE_EXPRESSION]CAST RUN.
  inversion RUN;subst;try discriminate.
  destruct(namespace_internal_step_exact ge cell (State fn(Sassign lhs rhs)k e le before)event middle I H)as[original[EVENT REAL]].
  inversion REAL;subst;try contradiction;try discriminate;
    try match goal with BOUND:boundary _ _ _|-_=>inversion BOUND end.
  - match goal with SOURCE:step2 _ _ _ _|-_=>inversion SOURCE;subst end.
    all:try solve[match goal with IMPOSSIBLE:_=_\/_=_|-_=>destruct IMPOSSIBLE;discriminate end].
    match goal with LV:eval_lvalue _ _ _ _ _ _ _ _|-_=>
      destruct(UNIQUE_LOCATION _ _ _ LV)as[BLOCK[OFFSET BITFIELD]];subst end.
    match goal with EV:eval_expr _ _ _ _ _ _|-_=>
      pose proof(UNIQUE_EXPRESSION _ EV)as VALUE;subst end.
    match goal with ASSIGN:assign_loc _ _ _ _ _ _ ?actual _|-_=>
      assert(SAME:actual=cast_value)by congruence;subst actual end.
    eexists;eexists;split;[reflexivity|];split;eassumption.
  - match goal with REST:namespace_steps _ _ (dead _) _ _|-_=>
      destruct(namespace_dead_steps _ _ _ _ _ REST)as[EMPTY IMPOSSIBLE];discriminate end.
Qed.

Theorem namespace_actual_test ge cell fn condition yes no k e le memory value
    events called arguments continuation final :
  expression_value ge e le memory condition value ->
  namespace_steps ge cell(live(State fn(Sifthenelse condition yes no)k e le memory))events
    (live(Callstate called arguments continuation final)) ->
  exists choice rest,
    events=namespace_source_event::rest /\bool_val value(typeof condition)memory=Some choice /\
    namespace_steps ge cell(live(State fn(if choice then yes else no)k e le memory))rest
      (live(Callstate called arguments continuation final)).
Proof.
  intros[EXPRESSION UNIQUE]RUN;inversion RUN;subst;try discriminate.
  destruct(namespace_internal_step_exact ge cell(State fn(Sifthenelse condition yes no)k e le memory)
    event middle I H)as[original[EVENT REAL]].
  inversion REAL;subst;try contradiction;try discriminate;
    try match goal with BOUND:boundary _ _ _|-_=>inversion BOUND end.
  - match goal with SOURCE:step2 _ _ _ _|-_=>inversion SOURCE;subst end.
    all:try solve[match goal with IMPOSSIBLE:_=_\/_=_|-_=>destruct IMPOSSIBLE;discriminate end].
    match goal with EV:eval_expr _ _ _ _ _ _|-_=>pose proof(UNIQUE _ EV)as SAME;subst end.
    eexists;eexists;split;[reflexivity|];split;eassumption.
  - match goal with REST:namespace_steps _ _ (dead _) _ _|-_=>
      destruct(namespace_dead_steps _ _ _ _ _ REST)as[EMPTY IMPOSSIBLE];discriminate end.
Qed.

Lemma namespace_tint_test_requires_integer value memory choice :
  bool_val value tint memory=Some choice ->exists number,value=Vint number.
Proof. destruct value;cbn;try discriminate;eauto. Qed.

Definition namespace_admit_raw_test e le memory k child cgroup returned:=
  State f_namespace_init namespace_admit_guard(Kseq(namespace_tail 25)k)e
    (PTree.set _t'12 returned(namespace_admit_env le child cgroup))memory.

Lemma namespace_admit_raw_test_frontier e le memory k child cgroup returned:
  namespace_first_call_path namespace_ge
    (fun endpoint=>endpoint=namespace_admit_raw_test e le memory k child cgroup returned)2
    (Returnstate returned(namespace_admit_cont e le child cgroup k)memory).
Proof.
  unfold namespace_admit_raw_test,namespace_admit_cont.
  admission_frontier_route;admission_frontier_route;apply namespace_first_call_stop;reflexivity.
Qed.

Theorem namespace_admit_actual_return_type cell e le memory k child cgroup returned
    events called arguments continuation final:
  namespace_steps namespace_ge cell
    (live(Returnstate returned(namespace_admit_cont e le child cgroup k)memory))events
    (live(Callstate called arguments continuation final)) ->exists number,returned=Vint number.
Proof.
  intro RUN;destruct(namespace_first_callback_reached _ _ _ _ _ _ _ _ _ _
    (namespace_admit_raw_test_frontier e le memory k child cgroup returned)RUN)
    as[prefix[endpoint[rest[EVENTS[SAME[PREFIX TAIL]]]]]].
  subst endpoint;unfold namespace_admit_raw_test,namespace_admit_guard,namespace_phase in TAIL;
    cbn[namespace_tail child_tail fn_body]in TAIL.
  destruct(namespace_actual_test _ _ _ _ _ _ _ _ _ _ returned _ _ _ _ _
    (old_expression_value _ _ _ _ _ _ (value_temp _ _ _ _ _ _ _ (PTree.gss _ _ _)))TAIL)
    as[choice[remaining[ORDER[TEST CONTINUE]]]].
  exact(namespace_tint_test_requires_integer returned memory choice TEST).
Qed.

Definition namespace_close_raw_test e le memory k cgroup returned:=
  State f_namespace_init namespace_cgroup_close_guard(Kseq(namespace_tail 26)k)e
    (PTree.set _t'13 returned(namespace_cgroup_close_env le cgroup))memory.

Lemma namespace_close_raw_test_frontier e le memory k cgroup returned:
  namespace_first_call_path namespace_ge
    (fun endpoint=>endpoint=namespace_close_raw_test e le memory k cgroup returned)2
    (Returnstate returned(namespace_cgroup_close_cont e le cgroup k)memory).
Proof.
  unfold namespace_close_raw_test,namespace_cgroup_close_cont.
  admission_frontier_route;admission_frontier_route;apply namespace_first_call_stop;reflexivity.
Qed.

Theorem namespace_close_actual_return_type cell e le memory k cgroup returned
    events called arguments continuation final:
  namespace_steps namespace_ge cell
    (live(Returnstate returned(namespace_cgroup_close_cont e le cgroup k)memory))events
    (live(Callstate called arguments continuation final)) ->exists number,returned=Vint number.
Proof.
  intro RUN;destruct(namespace_first_callback_reached _ _ _ _ _ _ _ _ _ _
    (namespace_close_raw_test_frontier e le memory k cgroup returned)RUN)
    as[prefix[endpoint[rest[EVENTS[SAME[PREFIX TAIL]]]]]].
  subst endpoint;unfold namespace_close_raw_test,namespace_cgroup_close_guard,namespace_phase in TAIL;
    cbn[namespace_tail child_tail fn_body]in TAIL.
  destruct(namespace_actual_test _ _ _ _ _ _ _ _ _ _ returned _ _ _ _ _
    (old_expression_value _ _ _ _ _ _ (value_temp _ _ _ _ _ _ _ (PTree.gss _ _ _)))TAIL)
    as[choice[remaining[ORDER[TEST CONTINUE]]]].
  exact(namespace_tint_test_requires_integer returned memory choice TEST).
Qed.

Theorem namespace_actual_set ge cell fn identifier expression k e le memory
    events called arguments continuation final :
  namespace_steps ge cell(live(State fn(Sset identifier expression)k e le memory))events
    (live(Callstate called arguments continuation final)) ->
  exists value rest,
    events=namespace_source_event::rest /\eval_expr ge e le memory expression value /\
    namespace_steps ge cell(live(State fn Sskip k e(PTree.set identifier value le)memory))rest
      (live(Callstate called arguments continuation final)).
Proof.
  intro RUN;inversion RUN;subst;try discriminate.
  destruct(namespace_internal_step_exact ge cell(State fn(Sset identifier expression)k e le memory)
    event middle I H)as[original[EVENT REAL]].
  inversion REAL;subst;try contradiction;try discriminate;
    try match goal with BOUND:boundary _ _ _|-_=>inversion BOUND end.
  - match goal with SOURCE:step2 _ _ _ _|-_=>inversion SOURCE;subst end.
    all:try solve[match goal with IMPOSSIBLE:_=_\/_=_|-_=>destruct IMPOSSIBLE;discriminate end].
    eexists;eexists;split;[reflexivity|];split;eassumption.
  - match goal with REST:namespace_steps _ _ (dead _) _ _|-_=>
      destruct(namespace_dead_steps _ _ _ _ _ REST)as[EMPTY IMPOSSIBLE];discriminate end.
Qed.

Definition namespace_publication_raw_cast e le memory k sequence returned:=
  State f_namespace_init namespace_publication_cast
    (Kseq namespace_publication_guard(Kseq(namespace_tail 30)k))e
    (PTree.set _t'19 returned(namespace_publication_call_env le sequence))memory.

Lemma namespace_publication_raw_cast_frontier e le memory k sequence returned:
  namespace_first_call_path namespace_ge
    (fun endpoint=>endpoint=namespace_publication_raw_cast e le memory k sequence returned)2
    (Returnstate returned(namespace_publication_cont e le sequence k)memory).
Proof.
  unfold namespace_publication_raw_cast,namespace_publication_cont.
  admission_frontier_route;admission_frontier_route;apply namespace_first_call_stop;reflexivity.
Qed.

Theorem namespace_publication_actual_return_type cell e le memory k sequence returned
    events called arguments continuation final:
  namespace_steps namespace_ge cell
    (live(Returnstate returned(namespace_publication_cont e le sequence k)memory))events
    (live(Callstate called arguments continuation final)) ->exists number,returned=Vint number.
Proof.
  intro RUN;destruct(namespace_first_callback_reached _ _ _ _ _ _ _ _ _ _
    (namespace_publication_raw_cast_frontier e le memory k sequence returned)RUN)
    as[prefix[endpoint[rest[EVENTS[SAME[PREFIX TAIL]]]]]].
  subst endpoint;unfold namespace_publication_raw_cast,namespace_publication_cast in TAIL.
  destruct(namespace_actual_set _ _ _ _ _ _ _ _ _ _ _ _ _ _ TAIL)
    as[value[remaining[ORDER[EXPRESSION CONTINUE]]]].
  inversion EXPRESSION;subst.
  - match goal with EV:eval_expr _ _ _ _ (Etempvar _t'19 tint) _|-_=>
      pose proof(evaluated_unique _ _ _ _ _ _
        (value_temp _ _ _ _ _ _ _ (PTree.gss _ _ _))_ EV)as SAME;subst end.
    match goal with CAST:sem_cast returned _ _ _=Some _|-_=>
      destruct returned;cbn in CAST;try discriminate;eauto end.
  - match goal with LV:eval_lvalue _ _ _ _ (Ecast _ _) _ _ _|-_=>inversion LV end.
Qed.

Definition namespace_cgroup_forget:=
  Sassign(Evar _admission_cgroup tint)(Eunop Oneg(Econst_int Int.one tint)tint).

Lemma namespace_cgroup_forget_frontier e le memory k:
  namespace_first_call_path namespace_ge
    (fun endpoint=>endpoint=State f_namespace_init namespace_cgroup_forget(Kseq(namespace_tail 27)k)e le memory)1
    (State f_namespace_init(namespace_tail 26)k e le memory).
Proof.
  unfold namespace_tail,namespace_cgroup_forget,child_tail;cbn[fn_body].
  admission_frontier_route;apply namespace_first_call_stop;reflexivity.
Qed.

Lemma namespace_result_first_callback e le memory k temporary:
  e!_result_of=None ->e!__res__6=Some(temporary,EntryReporting.ResultLayout.result_type) ->
  namespace_first_call_path namespace_ge
    (fun endpoint=>endpoint=Callstate(Internal f_result_of)
      [Vptr temporary Ptrofs.zero;Vint(Int.repr 5);Vint Int.zero;Vint Int.zero;Vint Int.zero]
      (namespace_admission_result_cont e le k)memory)3
    (State f_namespace_init(namespace_tail 27)k e le memory).
Proof.
  intros GLOBAL TEMPORARY.
  unfold namespace_admission_result_cont,namespace_admission_copy,namespace_tail,child_tail;cbn[fn_body].
  admission_frontier_route;admission_frontier_route;admission_frontier_call _result_of.
  - eapply cons_argument_values.
    + apply namespace_local_address;exact TEMPORARY.
    + reflexivity.
    + repeat child_argument;apply no_argument_values.
  - apply namespace_first_call_stop;reflexivity.
Qed.

Lemma namespace_clock_first_callback e le memory k:
  e!_now_ms=None ->
  namespace_first_call_path namespace_ge
    (fun endpoint=>endpoint=Callstate(Internal f_now_ms)[](namespace_admission_clock_cont e le k)memory)5
    (State f_namespace_init(namespace_tail 28)k e le memory).
Proof.
  intro GLOBAL;unfold namespace_admission_clock_cont,namespace_admission_clock_cast,namespace_admission_clock_guard,
    namespace_admission_elapsed,namespace_tail,child_tail;cbn[fn_body].
  admission_frontier_route;admission_frontier_route;admission_frontier_route;admission_frontier_route;
    admission_frontier_call _now_ms;[apply no_argument_values|apply namespace_first_call_stop;reflexivity].
Qed.

Lemma namespace_result_return_copy_frontier e le memory k returned:
  namespace_first_call_path namespace_ge
    (fun endpoint=>endpoint=State f_namespace_init namespace_admission_copy(Kseq(namespace_tail 28)k)e le memory)2
    (Returnstate returned(namespace_admission_result_cont e le k)memory).
Proof.
  unfold namespace_admission_result_cont.
  admission_frontier_route;admission_frontier_route;apply namespace_first_call_stop;reflexivity.
Qed.

Lemma namespace_clock_return_elapsed_frontier e le memory k milliseconds:
  namespace_first_call_path namespace_ge
    (fun endpoint=>endpoint=State f_namespace_init namespace_admission_elapsed
      (Kseq namespace_admission_clock_guard(Kseq(namespace_tail 29)k))e
      (namespace_admission_clock_env le milliseconds)memory)4
    (Returnstate(Vlong milliseconds)(namespace_admission_clock_cont e le k)memory).
Proof.
  unfold namespace_admission_clock_cont,namespace_admission_clock_cast,namespace_admission_clock_env.
  admission_frontier_route;admission_frontier_route;admission_frontier_set;
    [apply old_expression_value;WriteAll.expression|].
  admission_frontier_route;apply namespace_first_call_stop;reflexivity.
Qed.

Lemma namespace_after_forget_result_frontier e le memory k temporary:
  e!_result_of=None ->e!__res__6=Some(temporary,EntryReporting.ResultLayout.result_type) ->
  namespace_first_call_path namespace_ge
    (fun endpoint=>endpoint=Callstate(Internal f_result_of)
      [Vptr temporary Ptrofs.zero;Vint(Int.repr 5);Vint Int.zero;Vint Int.zero;Vint Int.zero]
      (namespace_admission_result_cont e le k)memory)4
    (State f_namespace_init Sskip(Kseq(namespace_tail 27)k)e le memory).
Proof.
  intros GLOBAL TEMPORARY;admission_frontier_route;apply namespace_result_first_callback;assumption.
Qed.

Lemma namespace_after_copy_clock_frontier e le memory k:
  e!_now_ms=None ->
  namespace_first_call_path namespace_ge
    (fun endpoint=>endpoint=Callstate(Internal f_now_ms)[](namespace_admission_clock_cont e le k)memory)6
    (State f_namespace_init Sskip(Kseq(namespace_tail 28)k)e le memory).
Proof. intro GLOBAL;admission_frontier_route;apply namespace_clock_first_callback;assumption. Qed.

Theorem namespace_actual_admit_then_close cell e le memory k child peer cgroup checking returned
    final_env final_temps final_child final_peer events final:
  e!_close=None ->namespace_launch_values le child peer cgroup checking ->
  namespace_steps namespace_ge cell
    (live(Returnstate returned(namespace_admit_cont e le child cgroup k)memory))events
    (live(Callstate(Internal f_release_child)[Vint final_child;Vint final_peer]
      (namespace_release_cont final_env final_temps final_child final_peer k)final)) ->
  exists admit_result close_result count callback suffix after,
    returned=Vint admit_result /\events=repeat namespace_source_event count++callback++suffix /\
    namespace_steps namespace_ge cell
      (live(Callstate close_definition[Vint cgroup]Kstop memory))callback
      (live(Returnstate(Vint close_result)Kstop after)) /\
    namespace_steps namespace_ge cell
      (live(Returnstate(Vint close_result)
        (namespace_cgroup_close_cont e(namespace_checked_admit_env le child cgroup admit_result)cgroup k)after))suffix
      (live(Callstate(Internal f_release_child)[Vint final_child;Vint final_peer]
        (namespace_release_cont final_env final_temps final_child final_peer k)final)).
Proof.
  intros CLOSE VALUES RUN.
  destruct(namespace_admit_actual_return_type _ _ _ _ _ _ _ _ _ _ _ _ _ RUN)as[admit_result SAME];subst returned.
  destruct(namespace_admit_return_frontier e le memory k child cgroup admit_result)as[count GUARD].
  pose proof(namespace_admit_retains_values le child peer cgroup checking admit_result VALUES)as KEPT.
  destruct KEPT as[CHILD[PEER[CGROUP CHECK]]].
  assert(PATH:namespace_first_call_path namespace_ge
    (fun endpoint=>endpoint=Callstate close_definition[Vint cgroup]
      (namespace_cgroup_close_cont e(namespace_checked_admit_env le child cgroup admit_result)cgroup k)memory)
    (count+3)
    (Returnstate(Vint admit_result)(namespace_admit_cont e le child cgroup k)memory)).
  { eapply namespace_first_call_bind with(count:=count)(extra:=3%nat)
      (first_leaf:=fun endpoint=>endpoint=State f_namespace_init(namespace_tail 25)k e
        (namespace_checked_admit_env le child cgroup admit_result)memory);[exact GUARD|].
    intros endpoint END;subst endpoint.
    eapply namespace_cgroup_close_first_callback;eassumption. }
  destruct(namespace_first_callback_exact _ _ _ _ _ _ _ _ _ _ PATH RUN)
    as[endpoint[rest[EVENTS[SAME[PREFIX TAIL]]]]];subst endpoint.
  destruct(namespace_callback_returns_before_later_call namespace_ge cell close_definition[Vint cgroup]
    (namespace_cgroup_close_cont e(namespace_checked_admit_env le child cgroup admit_result)cgroup k)memory rest
    (Internal f_release_child)[Vint final_child;Vint final_peer]
    (namespace_release_cont final_env final_temps final_child final_peer k)final
    I(namespace_release_later_than_close _ _ _ _ _ _ _ _)TAIL)
    as[callback[suffix[value[after[ORDER[CALLEE CONTINUE]]]]]].
  destruct(namespace_close_actual_return_type _ _ _ _ _ _ _ _ _ _ _ _ CONTINUE)as[close_result SAME];subst value.
  exists admit_result,close_result,(count+3)%nat,callback,suffix,after.
  split;[reflexivity|]. split;[rewrite EVENTS,ORDER;reflexivity|auto].
Qed.

Lemma namespace_source_repeat count:
  Forall(fun event=>event=namespace_source_event)(repeat namespace_source_event count).
Proof. apply Forall_forall;intros event MEMBER;apply repeat_spec in MEMBER;exact MEMBER. Qed.

Theorem namespace_actual_close_then_result cell e le memory k cgroup close_result temporary
    final_env final_temps final_child final_peer events final:
  e!_admission_cgroup=None ->e!_result_of=None ->e!__res__6=Some(temporary,result_type) ->
  namespace_steps namespace_ge cell
    (live(Returnstate(Vint close_result)(namespace_cgroup_close_cont e le cgroup k)memory))events
    (live(Callstate(Internal f_release_child)[Vint final_child;Vint final_peer]
      (namespace_release_cont final_env final_temps final_child final_peer k)final)) ->
  exists prefix callback suffix forgotten result result_memory,
    events=prefix++callback++suffix /\Forall(fun event=>event=namespace_source_event)prefix /\
    Mem.store Mint32 memory(namespace_symbol _admission_cgroup)0(Vint Int.mone)=Some forgotten /\
    namespace_steps namespace_ge cell
      (live(Callstate(Internal f_result_of)
        [Vptr temporary Ptrofs.zero;Vint(Int.repr 5);Vint Int.zero;Vint Int.zero;Vint Int.zero]Kstop forgotten))callback
      (live(Returnstate result Kstop result_memory)) /\
    namespace_steps namespace_ge cell
      (live(Returnstate result(namespace_admission_result_cont e
        (namespace_checked_cgroup_close_env le cgroup close_result)k)result_memory))suffix
      (live(Callstate(Internal f_release_child)[Vint final_child;Vint final_peer]
        (namespace_release_cont final_env final_temps final_child final_peer k)final)).
Proof.
  intros GLOBAL RESULT TEMPORARY RUN.
  destruct(namespace_cgroup_close_return_frontier e le memory k cgroup close_result)as[count GUARD].
  assert(PATH:namespace_first_call_path namespace_ge
    (fun endpoint=>endpoint=State f_namespace_init namespace_cgroup_forget(Kseq(namespace_tail 27)k)e
      (namespace_checked_cgroup_close_env le cgroup close_result)memory)(count+1)
    (Returnstate(Vint close_result)(namespace_cgroup_close_cont e le cgroup k)memory)).
  { eapply namespace_first_call_bind with(count:=count)(extra:=1%nat)
      (first_leaf:=fun endpoint=>endpoint=State f_namespace_init(namespace_tail 26)k e
        (namespace_checked_cgroup_close_env le cgroup close_result)memory);[exact GUARD|].
    intros endpoint SAME;subst endpoint;apply namespace_cgroup_forget_frontier. }
  destruct(namespace_first_callback_exact _ _ _ _ _ _ _ _ _ _ PATH RUN)
    as[endpoint[rest[EVENTS[SAME[PREFIX TAIL]]]]];subst endpoint.
  unfold namespace_cgroup_forget in TAIL.
  assert(EXPRESSION:expression_value namespace_ge e
    (namespace_checked_cgroup_close_env le cgroup close_result)memory
    (Eunop Oneg(Econst_int Int.one tint)tint)(Vint Int.mone)).
  { apply old_expression_value;eapply value_unary;[apply value_int|reflexivity]. }
  destruct(namespace_actual_assignment namespace_ge cell f_namespace_init
    (Evar _admission_cgroup tint)(Eunop Oneg(Econst_int Int.one tint)tint)(Kseq(namespace_tail 27)k)e
    (namespace_checked_cgroup_close_env le cgroup close_result)memory(namespace_symbol _admission_cgroup)Ptrofs.zero
    (Vint Int.mone)(Vint Int.mone)rest(Internal f_release_child)[Vint final_child;Vint final_peer]
    (namespace_release_cont final_env final_temps final_child final_peer k)final
    (global_location_value _ _ _ _ _ _ _ GLOBAL namespace_admission_symbol)
    EXPRESSION eq_refl TAIL)
    as[forgotten[remaining[ASSIGN_EVENTS[ASSIGN NEXT]]]].
  assert(STORE:Mem.store Mint32 memory(namespace_symbol _admission_cgroup)0(Vint Int.mone)=Some forgotten).
  { inversion ASSIGN;subst;cbn in *;try discriminate.
    match goal with MODE:By_value Mint32=By_value _|-_=>inversion MODE;subst end;assumption. }
  destruct(namespace_first_callback_exact _ _ _ _ _ _ _ _ _ _
    (namespace_after_forget_result_frontier e(namespace_checked_cgroup_close_env le cgroup close_result)
      forgotten k temporary RESULT TEMPORARY)NEXT)
    as[endpoint[result_rest[RESULT_EVENTS[SAME[RESULT_PREFIX RESULT_TAIL]]]]];subst endpoint.
  destruct(namespace_callback_returns_before_later_call namespace_ge cell(Internal f_result_of)
    [Vptr temporary Ptrofs.zero;Vint(Int.repr 5);Vint Int.zero;Vint Int.zero;Vint Int.zero]
    (namespace_admission_result_cont e(namespace_checked_cgroup_close_env le cgroup close_result)k)forgotten result_rest
    (Internal f_release_child)[Vint final_child;Vint final_peer]
    (namespace_release_cont final_env final_temps final_child final_peer k)final
    I(namespace_release_later_than_result _ _ _ _ _ _ _)RESULT_TAIL)
    as[callback[suffix[result[result_memory[ORDER[CALLEE CONTINUE]]]]]].
  exists(repeat namespace_source_event(count+1)++namespace_source_event::repeat namespace_source_event 4),
    callback,suffix,forgotten,result,result_memory.
  split.
  - rewrite EVENTS,ASSIGN_EVENTS,RESULT_EVENTS,ORDER;repeat rewrite <-app_assoc;reflexivity.
  - split;[apply Forall_app;split;[apply namespace_source_repeat|constructor;[reflexivity|apply namespace_source_repeat]]|auto].
Qed.

Theorem namespace_actual_result_then_clock cell e le memory k temporary admission returned
    final_env final_temps final_child final_peer events final:
  e!__res__6=Some(temporary,result_type) ->e!_admission=Some(admission,result_type) ->e!_now_ms=None ->
  namespace_steps namespace_ge cell
    (live(Returnstate returned(namespace_admission_result_cont e le k)memory))events
    (live(Callstate(Internal f_release_child)[Vint final_child;Vint final_peer]
      (namespace_release_cont final_env final_temps final_child final_peer k)final)) ->
  exists prefix callback suffix copied clock_result clock_memory,
    events=prefix++callback++suffix /\Forall(fun event=>event=namespace_source_event)prefix /\
    assign_loc namespace_ge result_type memory admission Ptrofs.zero Full(Vptr temporary Ptrofs.zero)copied /\
    namespace_steps namespace_ge cell
      (live(Callstate(Internal f_now_ms)[]Kstop copied))callback
      (live(Returnstate clock_result Kstop clock_memory)) /\
    namespace_steps namespace_ge cell
      (live(Returnstate clock_result(namespace_admission_clock_cont e le k)clock_memory))suffix
      (live(Callstate(Internal f_release_child)[Vint final_child;Vint final_peer]
        (namespace_release_cont final_env final_temps final_child final_peer k)final)).
Proof.
  intros TEMPORARY ADMISSION CLOCK RUN.
  destruct(namespace_first_callback_exact _ _ _ _ _ _ _ _ _ _
    (namespace_result_return_copy_frontier e le memory k returned)RUN)
    as[endpoint[rest[EVENTS[SAME[PREFIX TAIL]]]]];subst endpoint.
  unfold namespace_admission_copy in TAIL.
  assert(EXPRESSION:expression_value namespace_ge e le memory(Evar __res__6 result_type)(Vptr temporary Ptrofs.zero)).
  { eapply location_read_value;[apply local_location_value;exact TEMPORARY|apply deref_loc_copy;reflexivity]. }
  destruct(namespace_actual_assignment namespace_ge cell f_namespace_init
    (Evar _admission result_type)(Evar __res__6 result_type)(Kseq(namespace_tail 28)k)e le memory
    admission Ptrofs.zero(Vptr temporary Ptrofs.zero)(Vptr temporary Ptrofs.zero)rest
    (Internal f_release_child)[Vint final_child;Vint final_peer]
    (namespace_release_cont final_env final_temps final_child final_peer k)final
    (local_location_value _ _ _ _ _ _ _ ADMISSION)
    EXPRESSION eq_refl TAIL)
    as[copied[remaining[ASSIGN_EVENTS[ASSIGN NEXT]]]].
  destruct(namespace_first_callback_exact _ _ _ _ _ _ _ _ _ _
    (namespace_after_copy_clock_frontier e le copied k CLOCK)NEXT)
    as[endpoint[clock_rest[CLOCK_EVENTS[SAME[CLOCK_PREFIX CLOCK_TAIL]]]]];subst endpoint.
  destruct(namespace_callback_returns_before_later_call namespace_ge cell(Internal f_now_ms)[]
    (namespace_admission_clock_cont e le k)copied clock_rest
    (Internal f_release_child)[Vint final_child;Vint final_peer]
    (namespace_release_cont final_env final_temps final_child final_peer k)final
    I(namespace_release_later_than_clock _ _ _ _ _ _ _)CLOCK_TAIL)
    as[callback[suffix[clock_result[clock_memory[ORDER[CALLEE CONTINUE]]]]]].
  exists(repeat namespace_source_event 2++namespace_source_event::repeat namespace_source_event 6),
    callback,suffix,copied,clock_result,clock_memory.
  split.
  - rewrite EVENTS,ASSIGN_EVENTS,CLOCK_EVENTS,ORDER;repeat rewrite <-app_assoc;reflexivity.
  - split;[apply Forall_app;split;[apply namespace_source_repeat|constructor;[reflexivity|apply namespace_source_repeat]]|auto].
Qed.

Lemma namespace_after_elapsed_clock_guard e le memory k milliseconds:
  exists count,namespace_first_call_path namespace_ge
    (fun endpoint=>endpoint=State f_namespace_init(namespace_tail 29)k e(namespace_checked_clock_env le milliseconds)memory)count
    (State f_namespace_init Sskip(Kseq namespace_admission_clock_guard(Kseq(namespace_tail 29)k))e
      (namespace_admission_clock_env le milliseconds)memory).
Proof.
  unfold namespace_checked_clock_env.
  destruct(Int64.eq_dec milliseconds Int64.zero)as[ZERO|NONZERO].
  - subst milliseconds;rewrite Int64.eq_true;eexists;admission_frontier_route.
    unfold namespace_admission_clock_guard.
    eapply namespace_first_call_next;[intros;discriminate|apply certified_if_edge with(v:=Vint Int.one)(b:=true)|].
    + apply old_expression_value;unfold namespace_admission_clock_env;WriteAll.expression.
    + reflexivity.
    + admission_frontier_set;[apply old_expression_value,value_int|].
      admission_frontier_route;apply namespace_first_call_stop;reflexivity.
  - rewrite Int64.eq_false by exact NONZERO;eexists;admission_frontier_route.
    unfold namespace_admission_clock_guard.
    eapply namespace_first_call_next;[intros;discriminate|apply certified_if_edge with(v:=Vint Int.zero)(b:=false)|].
    + apply old_expression_value;eapply value_unary.
      * apply value_temp;unfold namespace_admission_clock_env;apply PTree.gss.
      * cbn;rewrite Int64.eq_false by exact NONZERO;reflexivity.
    + reflexivity.
    + admission_frontier_route;apply namespace_first_call_stop;reflexivity.
Qed.

Theorem namespace_actual_clock_then_publication cell e le memory k admission milliseconds
    final_env final_temps final_child final_peer events final:
  e!_admission=Some(admission,result_type) ->
  namespace_steps namespace_ge cell
    (live(Returnstate(Vlong milliseconds)(namespace_admission_clock_cont e le k)memory))events
    (live(Callstate(Internal f_release_child)[Vint final_child;Vint final_peer]
      (namespace_release_cont final_env final_temps final_child final_peer k)final)) ->
  exists prefix suffix stored,
    events=prefix++suffix /\Forall(fun event=>event=namespace_source_event)prefix /\
    Mem.store Mint64 memory admission 72(Vlong milliseconds)=Some stored /\
    namespace_steps namespace_ge cell
      (live(State f_namespace_init(namespace_tail 29)k e(namespace_checked_clock_env le milliseconds)stored))suffix
      (live(Callstate(Internal f_release_child)[Vint final_child;Vint final_peer]
        (namespace_release_cont final_env final_temps final_child final_peer k)final)).
Proof.
  intros ADMISSION RUN.
  destruct(namespace_first_callback_exact _ _ _ _ _ _ _ _ _ _
    (namespace_clock_return_elapsed_frontier e le memory k milliseconds)RUN)
    as[endpoint[rest[EVENTS[SAME[PREFIX TAIL]]]]];subst endpoint.
  unfold namespace_admission_elapsed in TAIL.
  assert(LOCATION:location_value namespace_ge e(namespace_admission_clock_env le milliseconds)memory
    (Efield(Evar _admission result_type)_elapsed tulong)admission(Ptrofs.repr 72)).
  { rewrite namespace_reporting_environment.
    eapply current_result_field_location with(offset:=Ptrofs.zero)(delta:=72).
    - eapply location_read_value;[apply local_location_value;exact ADMISSION|apply deref_loc_copy;reflexivity].
    - reflexivity.
    - reflexivity. }
  assert(EXPRESSION:expression_value namespace_ge e(namespace_admission_clock_env le milliseconds)memory
    (Etempvar _t'15 tulong)(Vlong milliseconds)).
  { apply old_expression_value,value_temp;unfold namespace_admission_clock_env;apply PTree.gss. }
  destruct(namespace_actual_assignment namespace_ge cell f_namespace_init
    (Efield(Evar _admission result_type)_elapsed tulong)(Etempvar _t'15 tulong)
    (Kseq namespace_admission_clock_guard(Kseq(namespace_tail 29)k))e
    (namespace_admission_clock_env le milliseconds)memory admission(Ptrofs.repr 72)
    (Vlong milliseconds)(Vlong milliseconds)rest(Internal f_release_child)[Vint final_child;Vint final_peer]
    (namespace_release_cont final_env final_temps final_child final_peer k)final LOCATION EXPRESSION eq_refl TAIL)
    as[stored[remaining[ASSIGN_EVENTS[ASSIGN NEXT]]]].
  assert(STORE:Mem.store Mint64 memory admission 72(Vlong milliseconds)=Some stored).
  { inversion ASSIGN;subst;cbn in *;try discriminate.
    match goal with MODE:By_value Mint64=By_value _|-_=>inversion MODE;subst end;assumption. }
  destruct(namespace_after_elapsed_clock_guard e le stored k milliseconds)as[count GUARD].
  destruct(namespace_first_callback_exact _ _ _ _ _ _ _ _ _ _ GUARD NEXT)
    as[endpoint[suffix[GUARD_EVENTS[SAME[GUARD_PREFIX CONTINUE]]]]];subst endpoint.
  exists(repeat namespace_source_event 4++namespace_source_event::repeat namespace_source_event count),suffix,stored.
  split;[rewrite EVENTS,ASSIGN_EVENTS,GUARD_EVENTS;repeat rewrite <-app_assoc;reflexivity|].
  split;[apply Forall_app;split;[apply namespace_source_repeat|constructor;[reflexivity|apply namespace_source_repeat]]|auto].
Qed.

Lemma namespace_failed_publication_frontier e le memory k:
  le!_bad=Some(Vint Int.one) ->
  exists count final,final!_bad=Some(Vint Int.one) /\
    namespace_first_call_path namespace_ge
      (fun endpoint=>endpoint=State f_namespace_init(namespace_tail 30)k e final memory)count
      (State f_namespace_init(namespace_tail 29)k e le memory).
Proof.
  intro BAD;unfold namespace_tail,child_tail;cbn[fn_body].
  eexists;exists(PTree.set _t'17(Vint Int.zero)(PTree.set _t'16(Vint Int.zero)le));split;[WriteAll.lookup|].
  admission_frontier_route;admission_frontier_route;admission_frontier_route.
  eapply namespace_first_call_next;[intros;discriminate|apply certified_if_edge with(v:=Vint Int.zero)(b:=false)|].
  - apply old_expression_value;WriteAll.expression.
  - reflexivity.
  - admission_frontier_set;[apply old_expression_value,value_int|]. admission_frontier_route.
    eapply namespace_first_call_next;[intros;discriminate|apply certified_if_edge with(v:=Vint Int.zero)(b:=false)|].
    + apply old_expression_value,value_temp;apply PTree.gss.
    + reflexivity.
    + admission_frontier_set;[apply old_expression_value,value_int|]. admission_frontier_route.
      eapply namespace_first_call_next;[intros;discriminate|apply certified_if_edge with(v:=Vint Int.zero)(b:=false)|].
      * apply old_expression_value,value_temp;apply PTree.gss.
      * reflexivity.
      * admission_frontier_route;apply namespace_first_call_stop;reflexivity.
Qed.

Lemma namespace_failed_release_frontier e le memory k:
  le!_bad=Some(Vint Int.one) ->
  exists count final,final!_bad=Some(Vint Int.one) /\
    namespace_first_call_path namespace_ge
      (fun endpoint=>endpoint=State f_namespace_init(namespace_tail 31)k e final memory)count
      (State f_namespace_init(namespace_tail 30)k e le memory).
Proof.
  intro BAD;unfold namespace_tail,child_tail;cbn[fn_body].
  eexists;exists(PTree.set _t'20(Vint Int.zero)le);split;[WriteAll.lookup|].
  admission_frontier_route;admission_frontier_route.
  eapply namespace_first_call_next;[intros;discriminate|apply certified_if_edge with(v:=Vint Int.zero)(b:=false)|].
  - apply old_expression_value;WriteAll.expression.
  - reflexivity.
  - admission_frontier_set;[apply old_expression_value,value_int|]. admission_frontier_route.
    eapply namespace_first_call_next;[intros;discriminate|apply certified_if_edge with(v:=Vint Int.zero)(b:=false)|].
    + apply old_expression_value,value_temp;apply PTree.gss.
    + reflexivity.
    + admission_frontier_route;apply namespace_first_call_stop;reflexivity.
Qed.

Lemma namespace_normal_publication_first_callback e le memory k admission report sequence:
  le!_bad=Some(Vint Int.zero) ->le!_report=Some(Vint report) ->le!_sequence=Some(Vlong sequence) ->
  e!_send_frame=None ->e!_admission=Some(admission,result_type) ->le!_launch_check=Some(Vint Int.zero) ->
  exists count,namespace_first_call_path namespace_ge
    (fun endpoint=>endpoint=Callstate(Internal f_send_frame)[Vint report;Vlong sequence;Vptr admission Ptrofs.zero]
      (namespace_publication_cont e le sequence k)memory)count
    (State f_namespace_init(namespace_tail 29)k e le memory).
Proof.
  intros BAD REPORT SEQUENCE SEND ADMISSION CHECK.
  unfold namespace_publication_cont,namespace_publication_call_env,namespace_publication_guard,
    namespace_publication_cast,namespace_phase,namespace_tail,child_tail;cbn[fn_body].
  eexists;admission_frontier_route;admission_frontier_route;admission_frontier_route.
  eapply namespace_first_call_next;[intros;discriminate|apply certified_if_edge with(v:=Vint Int.one)(b:=true)|].
  - apply old_expression_value;WriteAll.expression.
  - reflexivity.
  - admission_frontier_set.
    + apply old_expression_value;WriteAll.expression.
    + admission_frontier_route.
      eapply namespace_first_call_next;[intros;discriminate|apply certified_if_edge with(v:=Vint Int.one)(b:=true)|].
      * apply old_expression_value,value_temp;apply PTree.gss.
      * reflexivity.
      * admission_frontier_route;admission_frontier_route;admission_frontier_route;admission_frontier_set.
        -- apply old_expression_value,value_temp;WriteAll.lookup.
        -- admission_frontier_route;admission_frontier_set.
           ++ apply old_expression_value;WriteAll.expression.
           ++ admission_frontier_route;admission_frontier_call _send_frame.
              ** child_argument;child_argument;eapply cons_argument_values.
                 --- eapply location_read_value;[apply local_location_value;exact ADMISSION|apply deref_loc_copy;reflexivity].
                 --- reflexivity.
                 --- apply no_argument_values.
              ** apply namespace_first_call_stop;reflexivity.
Qed.

Lemma namespace_publication_return_frontier e le memory k sequence returned:
  exists count,namespace_first_call_path namespace_ge
    (fun endpoint=>endpoint=State f_namespace_init(namespace_tail 30)k e
      (namespace_checked_publication_env le sequence returned)memory)count
    (Returnstate(Vint returned)(namespace_publication_cont e le sequence k)memory).
Proof.
  unfold namespace_publication_cont,namespace_publication_cast,namespace_checked_publication_env,
    namespace_publication_return_env.
  destruct(Int.eq_dec returned Int.zero)as[ZERO|NONZERO].
  - subst returned;rewrite Int.eq_true;eexists;admission_frontier_route;admission_frontier_route;admission_frontier_set.
    + apply old_expression_value;WriteAll.expression.
    + admission_frontier_route;eapply namespace_first_call_next;
        [intros;discriminate|apply certified_if_edge with(v:=Vint Int.zero)(b:=false)|].
      * apply old_expression_value,value_temp;apply PTree.gss.
      * reflexivity.
      * admission_frontier_route;apply namespace_first_call_stop;reflexivity.
  - rewrite Int.eq_false by exact NONZERO;eexists;admission_frontier_route;admission_frontier_route;admission_frontier_set.
    + apply old_expression_value;eapply value_cast;[apply value_temp;apply PTree.gss|].
      cbn;rewrite Int.eq_false by exact NONZERO;reflexivity.
    + admission_frontier_route;eapply namespace_first_call_next;
        [intros;discriminate|apply certified_if_edge with(v:=Vint Int.one)(b:=true)|].
      * apply old_expression_value,value_temp;apply PTree.gss.
      * reflexivity.
      * admission_frontier_set;[apply old_expression_value,value_int|].
        admission_frontier_route;apply namespace_first_call_stop;reflexivity.
Qed.

Lemma namespace_authorized_release_first_callback e le memory k child peer:
  le!_bad=Some(Vint Int.zero) ->e!_release_child=None ->
  le!_launch_child=Some(Vint child) ->le!_launch_peer=Some(Vint peer) ->
  namespace_first_call_path namespace_ge
    (fun endpoint=>endpoint=Callstate(Internal f_release_child)[Vint child;Vint peer]
      (namespace_release_cont e le child peer k)memory)5
    (State f_namespace_init(namespace_tail 30)k e le memory).
Proof.
  intros BAD RELEASE CHILD PEER.
  unfold namespace_release_cont,namespace_release_guard,namespace_release_cast,
    namespace_phase,namespace_tail,child_tail;cbn[fn_body].
  admission_frontier_route;admission_frontier_route.
  eapply namespace_first_call_next;[intros;discriminate|apply certified_if_edge with(v:=Vint Int.one)(b:=true)|].
  - apply old_expression_value;WriteAll.expression.
  - reflexivity.
  - admission_frontier_route;admission_frontier_call _release_child.
    + child_argument;child_argument;apply no_argument_values.
    + apply namespace_first_call_stop;reflexivity.
Qed.

Theorem namespace_actual_publication_then_release cell e le memory k admission report sequence
    final_env final_temps final_child final_peer events final:
  le!_bad=Some(Vint Int.zero) ->le!_report=Some(Vint report) ->le!_sequence=Some(Vlong sequence) ->
  e!_send_frame=None ->e!_admission=Some(admission,result_type) ->le!_launch_check=Some(Vint Int.zero) ->
  namespace_steps namespace_ge cell
    (live(State f_namespace_init(namespace_tail 29)k e le memory))events
    (live(Callstate(Internal f_release_child)[Vint final_child;Vint final_peer]
      (namespace_release_cont final_env final_temps final_child final_peer k)final)) ->
  exists prefix callback guard suffix returned after,
    events=prefix++callback++guard++suffix /\
    Forall(fun event=>event=namespace_source_event)prefix /\
    Forall(fun event=>event=namespace_source_event)guard /\
    namespace_steps namespace_ge cell
      (live(Callstate(Internal f_send_frame)[Vint report;Vlong sequence;Vptr admission Ptrofs.zero]Kstop memory))callback
      (live(Returnstate(Vint returned)Kstop after)) /\
    namespace_steps namespace_ge cell
      (live(State f_namespace_init(namespace_tail 30)k e(namespace_checked_publication_env le sequence returned)after))suffix
      (live(Callstate(Internal f_release_child)[Vint final_child;Vint final_peer]
        (namespace_release_cont final_env final_temps final_child final_peer k)final)).
Proof.
  intros BAD REPORT SEQUENCE SEND ADMISSION CHECK RUN.
  destruct(namespace_normal_publication_first_callback e le memory k admission report sequence
    BAD REPORT SEQUENCE SEND ADMISSION CHECK)as[count PATH].
  destruct(namespace_first_callback_exact _ _ _ _ _ _ _ _ _ _ PATH RUN)
    as[endpoint[rest[EVENTS[SAME[PREFIX TAIL]]]]];subst endpoint.
  destruct(namespace_callback_returns_before_later_call namespace_ge cell(Internal f_send_frame)
    [Vint report;Vlong sequence;Vptr admission Ptrofs.zero](namespace_publication_cont e le sequence k)memory rest
    (Internal f_release_child)[Vint final_child;Vint final_peer]
    (namespace_release_cont final_env final_temps final_child final_peer k)final
    I(namespace_release_later_than_publication _ _ _ _ _ _ _ _)TAIL)
    as[callback[remaining[value[after[ORDER[CALLEE CONTINUE]]]]]].
  destruct(namespace_publication_actual_return_type _ _ _ _ _ _ _ _ _ _ _ _ CONTINUE)as[returned SAME];subst value.
  destruct(namespace_publication_return_frontier e le after k sequence returned)as[guard_count GUARD].
  destruct(namespace_first_callback_exact _ _ _ _ _ _ _ _ _ _ GUARD CONTINUE)
    as[endpoint[suffix[GUARD_EVENTS[SAME[GUARD_PREFIX FINAL]]]]];subst endpoint.
  exists(repeat namespace_source_event count),callback,(repeat namespace_source_event guard_count),suffix,returned,after.
  split;[rewrite EVENTS,ORDER,GUARD_EVENTS;repeat rewrite <-app_assoc;reflexivity|].
  split;[apply namespace_source_repeat|]. split;[apply namespace_source_repeat|auto].
Qed.
