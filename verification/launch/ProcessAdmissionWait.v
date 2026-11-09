(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Matching stopped-child observations reach the formatter with owned storage. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import IO Machine ClightSteps StoreSteps WriteAll ErrorNumber LibraryMachine.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessAllocation ProcessStructure ProcessReturns
  ProcessPaths ProcessWait ProcessStatus ProcessWaitRejection ProcessPrimitiveCases ProcessRoutine ProcessCallee
  ProcessAdmissionEvents.
From LeanCageMainNumber Require Import NumberMemory.
Import ListNotations.
Open Scope Z_scope.

Theorem process_wait_return_decomposition ge cell before child status offset options k events value after :
  process_steps ge cell
    (live(Callstate process_wait_definition[Vint child;Vptr status offset;Vint options]k before))events
    (live(Returnstate value Kstop after)) ->
  exists waiting observation memory rest,
    events=repeat process_waiting waiting++process_waited child status offset options observation::rest /\
    process_wait_effect cell status offset before observation memory /\entry_errno_ready cell memory /\
    process_steps ge cell(live(Returnstate(Vint(wait_return observation))k memory))rest
      (live(Returnstate value Kstop after)).
Proof.
  remember(live(Callstate process_wait_definition[Vint child;Vptr status offset;Vint options]k before))as initial eqn:INITIAL.
  remember(live(Returnstate value Kstop after))as final eqn:FINAL.
  intro RUN;revert before INITIAL FINAL.
  induction RUN as[state|first event middle rest last STEP RUN IH];intros before INITIAL FINAL;[congruence|].
  subst first last.
  destruct(process_wait_cases _ _ _ _ _ _ _ _ _ _ STEP)
    as[[observation[memory[EFFECT[READY[EVENT TARGET]]]]]|[[EVENT TARGET]|
      [[EVENT TARGET]|[memory[EVENT[PARTIAL TARGET]]]]]];subst.
  - exists 0%nat,observation,memory,rest;cbn;auto.
  - destruct(IH before eq_refl eq_refl)as[waiting[observation[memory[tail[EVENTS[EFFECT[READY CONTINUE]]]]]]].
    exists(S waiting),observation,memory,tail;cbn;split;[congruence|auto].
  - destruct(process_dead_steps _ _ _ _ _ RUN)as[_ IMPOSSIBLE];discriminate.
  - destruct(process_dead_steps _ _ _ _ _ RUN)as[_ IMPOSSIBLE];discriminate.
Qed.

Lemma admission_wait_effect_permissions cell status offset before observation after :
  process_wait_effect cell status offset before observation after ->
  forall object position kind permission,
    Mem.perm after object position kind permission<->Mem.perm before object position kind permission.
Proof.
  intro EFFECT;inversion EFFECT;subst;intros object position kind permission.
  - split;eauto using Mem.perm_store_1,Mem.perm_store_2.
  - match goal with STORE:Mem.storev _ _ _ _=Some _|-_=>
      unfold Mem.storev in STORE;destruct(zle _ _);[|discriminate]end.
    match goal with ERRNO:errno_change _ _ _ _|-_=>inversion ERRNO;subst end.
    + split;eauto using Mem.perm_store_1,Mem.perm_store_2.
    + split;intro PERM;eauto 3 using Mem.perm_store_1,Mem.perm_store_2.
Qed.

Lemma admission_wait_preserves_output cell status offset before observation after encoded :
  process_wait_effect cell status offset before observation after ->
  number_output before encoded Ptrofs.zero ->number_output after encoded Ptrofs.zero.
Proof.
  intros EFFECT[BOUND[RANGE ALIGN]];split;[exact BOUND|]. split;[|exact ALIGN].
  intros position INTERVAL;apply(admission_wait_effect_permissions _ _ _ _ _ _ EFFECT);apply RANGE;exact INTERVAL.
Qed.

Definition admission_stopped_parameters le child word :=
  admission_stopsig_env(admission_stopped_env(admission_wait_return_env le child)word)word.

Theorem admission_matching_stop_source locals le memory child status offset word :
  1<=Int.signed child ->le!_child=Some(Vint child) ->le!_status=Some(Vptr status offset) ->
  Mem.loadv Mint32 memory(Vptr status offset)=Some(Vint word) ->
  admission_is_stopped word=true ->admission_is_sigstop word=true ->
  store_path admission_ge(fun _=>True)
    (Returnstate(Vint child)(admission_wait_call_cont(admission_env locals)le Kstop)memory)26
    (State f_admit_child(admission_tail 4(fn_body f_admit_child))Kstop(admission_env locals)
      (admission_stopped_parameters le child word)memory).
Proof.
  intros POSITIVE CHILD STATUS LOAD STOPPED SIGNAL.
  destruct(admission_wait_values le child child status offset CHILD STATUS)as[CHILD'[STATUS' GOT]].
  pose proof(admission_identity_guard(admission_env locals)(admission_wait_return_env le child)
    memory Kstop child child GOT CHILD')as IDENTITY;rewrite Int.eq_true in IDENTITY.
  pose proof(admission_stopped_guard(admission_env locals)(admission_wait_return_env le child)
    memory Kstop status offset word STATUS' LOAD)as STOP;rewrite STOPPED in STOP.
  assert(STATUS'':(admission_stopped_env(admission_wait_return_env le child)word)!_status=Some(Vptr status offset)).
  { unfold admission_stopped_env;rewrite PTree.gso by discriminate;exact STATUS'. }
  pose proof(admission_stopsig_guard(admission_env locals)
    (admission_stopped_env(admission_wait_return_env le child)word)memory Kstop status offset word STATUS'' LOAD)as SIG.
  rewrite SIGNAL in SIG;unfold admission_stopped_parameters.
  eapply store_path_trans with(n:=11%nat);[apply admission_wait_positive_source;lia|].
  eapply store_path_trans with(n:=3%nat);[exact IDENTITY|].
  eapply store_path_trans with(n:=6%nat);[exact STOP|exact SIG].
Qed.

Lemma admission_rejection_cannot_succeed cell locals start count continuation le memory events after :
  call_cont continuation=Kstop ->
  store_path admission_ge(fun _=>True)start count
    (State f_admit_child admission_failure continuation(admission_env locals)le memory) ->
  ~process_steps admission_ge cell(live start)events(live(Returnstate(Vint Int.zero)Kstop after)).
Proof.
  intros CLOSED PATH RUN.
  destruct(process_source_frontier_reached _ _ _ _ _ _ _ _ _ PATH ltac:(intros;discriminate)RUN)
    as[rest[EVENTS CONTINUE]].
  eapply process_negative_return_cannot_zero with(fn:=f_admit_child)(k:=continuation);
    [reflexivity|exact CLOSED|exact CONTINUE].
Qed.

Lemma admission_errno_return_decomposition cell locals le memory error events after :
  initialized_errno cell memory error ->
  process_steps admission_ge cell
    (live(Callstate(External errno_function[](tptr tint)cc_default)[]
      (admission_errno_cont(admission_env locals)le Kstop)memory))events
    (live(Returnstate(Vint Int.zero)Kstop after)) ->
  exists rest,events=process_entry(entry_library(original_event errno_step))::rest /\
    process_steps admission_ge cell
      (live(Returnstate(Vptr(tls_block cell)(Ptrofs.repr(tls_offset cell)))
        (admission_errno_cont(admission_env locals)le Kstop)memory))rest
      (live(Returnstate(Vint Int.zero)Kstop after)).
Proof.
  intros ERRNO RUN;inversion RUN;subst;try discriminate.
  match goal with STEP:process_step _ _ _ _ _|-_=>
    destruct(process_certain_step_cases _ _ _ _ _ _ _
      (ErrorNumber.errno_certain admission_ge cell(admission_errno_cont(admission_env locals)le Kstop)
        memory error ERRNO)STEP)as[[EVENT TARGET]|[EVENT TARGET]]end;subst.
  - eauto.
  - match goal with DEAD:process_steps _ _(dead _)_ _|-_=>
      destruct(process_dead_steps _ _ _ _ _ DEAD)as[_ IMPOSSIBLE];discriminate end.
Qed.

Theorem admission_wait_to_formatter cell locals before le child cgroup status offset events after :
  1<=Int.signed child ->status<>tls_block cell ->
  le!_child=Some(Vint child) ->le!_cgfd=Some(Vint cgroup) ->le!_status=Some(Vptr status offset) ->
  number_output before(admission_encoded locals)Ptrofs.zero ->
  process_steps admission_ge cell
    (live(Callstate process_wait_definition[Vint child;Vptr status offset;Vint Int.zero]
      (admission_wait_call_cont(admission_env locals)le Kstop)before))events
    (live(Returnstate(Vint Int.zero)Kstop after)) ->
  exists prefix suffix actual memory word,
    events=prefix++suffix /\
    In(process_waited child status offset Int.zero(wait_status child word))prefix /\
    admission_is_stopped word=true /\admission_is_sigstop word=true /\
    actual!_child=Some(Vint child) /\actual!_cgfd=Some(Vint cgroup) /\
    number_output memory(admission_encoded locals)Ptrofs.zero /\
    process_steps admission_ge cell
      (live(State f_admit_child(admission_tail 4(fn_body f_admit_child))Kstop(admission_env locals)actual memory))suffix
      (live(Returnstate(Vint Int.zero)Kstop after)) /\
    exists search,prefix=search++process_waited child status offset Int.zero(wait_status child word)::
      repeat process_source_event 26 /\Forall(admission_lease_event child status offset)search.
Proof.
  intros POSITIVE SEPARATE.
  remember(length events)as fuel eqn:FUEL;revert before le events FUEL.
  induction fuel using lt_wf_ind;intros before le events FUEL CHILD CGROUP STATUS OUTPUT RUN.
  destruct(process_wait_return_decomposition _ _ _ _ _ _ _ _ _ _ _ RUN)
    as[waiting[observation[memory[rest[EVENTS[EFFECT[READY CONTINUE]]]]]]].
  assert(OUTPUT':number_output memory(admission_encoded locals)Ptrofs.zero).
  { eapply admission_wait_preserves_output;eassumption. }
  destruct observation as[error|got word].
  - pose proof(admission_failed_errno_readback cell status offset before error memory EFFECT READY)as ERRNO.
    destruct(process_source_frontier_reached _ _ _ _ _ _ _ _ _
      (admission_wait_failed_to_errno(admission_env locals)le memory Kstop
        (admission_nonlocal_binding locals ___errno_location ltac:(discriminate)ltac:(discriminate)))
      ltac:(intros;discriminate)CONTINUE)as[errno_events[ERRNO_EVENTS ERRNO_RUN]].
    destruct(admission_errno_return_decomposition cell locals le memory error errno_events after ERRNO ERRNO_RUN)
      as[errno_rest[ERRNO_STEP ERRNO_REST]].
    destruct(admission_errno_rejoins cell locals le memory child status offset error
        POSITIVE CHILD STATUS ERRNO)as[[count RETRY]|[count[final[k[CLOSED REJECT]]]]].
      + destruct(process_source_frontier_reached _ _ _ _ _ _ _ _ _ RETRY ltac:(intros;discriminate)ERRNO_REST)
          as[retry_events[RETRY_EVENTS RETRY_RUN]].
        assert(SHORT:(length retry_events<fuel)%nat).
        { rewrite FUEL,EVENTS,ERRNO_EVENTS,ERRNO_STEP,RETRY_EVENTS;
          repeat rewrite length_app;repeat rewrite repeat_length;cbn;
          repeat rewrite length_app;repeat rewrite repeat_length;lia. }
        assert(CHILD':(admission_errno_env cell le error)!_child=Some(Vint child)).
        { unfold admission_errno_env,admission_wait_saved;repeat rewrite PTree.gso by discriminate;exact CHILD. }
        assert(CGROUP':(admission_errno_env cell le error)!_cgfd=Some(Vint cgroup)).
        { unfold admission_errno_env,admission_wait_saved;repeat rewrite PTree.gso by discriminate;exact CGROUP. }
        assert(STATUS':(admission_errno_env cell le error)!_status=Some(Vptr status offset)).
        { unfold admission_errno_env,admission_wait_saved;repeat rewrite PTree.gso by discriminate;exact STATUS. }
        destruct(H(length retry_events)SHORT memory(admission_errno_env cell le error)retry_events eq_refl
          CHILD' CGROUP' STATUS' OUTPUT' RETRY_RUN)
          as[prefix[suffix[actual[formatted[word FACTS]]]]].
        destruct FACTS as[ORDER[MEMBER[STOP[SIGNAL[CHILD''[CGROUP''[OUT[FINAL EXTRA]]]]]]]].
        destruct EXTRA as[search[SEARCH CLASS]].
        exists(repeat process_waiting waiting++process_waited child status offset Int.zero(wait_failed error)::
          (repeat process_source_event 8++process_entry(entry_library(original_event errno_step))::
            (repeat process_source_event count++prefix))),suffix,actual,formatted,word.
        split.
        -- rewrite EVENTS,ERRNO_EVENTS,ERRNO_STEP,RETRY_EVENTS,ORDER;
             repeat first[rewrite <-app_assoc|progress(cbn[app])];reflexivity.
        -- split.
           ++ apply in_or_app;right;right;apply in_or_app;right;right;apply in_or_app;right;exact MEMBER.
           ++ split;[exact STOP|]. split;[exact SIGNAL|]. split;[exact CHILD''|].
              split;[exact CGROUP''|]. split;[exact OUT|]. split;[exact FINAL|].
              exists(repeat process_waiting waiting++process_waited child status offset Int.zero(wait_failed error)::
                (repeat process_source_event 8++process_entry(entry_library(original_event errno_step))::
                  (repeat process_source_event count++search))).
              split.
              ** rewrite SEARCH;repeat first[rewrite <-app_assoc|progress(cbn[app])];reflexivity.
              ** apply Forall_app;split;[apply admission_passive_leases,admission_waiting_passive|].
                 constructor;[cbn;repeat split;reflexivity|].
                 apply Forall_app;split;[apply admission_passive_leases,admission_source_passive|].
                 constructor;[exact I|]. apply Forall_app;split;
                   [apply admission_passive_leases,admission_source_passive|exact CLASS].
      + exfalso;eapply admission_rejection_cannot_succeed;[exact CLOSED|exact REJECT|exact ERRNO_REST].
  - destruct(admission_wait_status_readback _ _ _ _ _ _ _ SEPARATE EFFECT)as[GOT LOAD].
    destruct(admission_stop_matches child got word)eqn:MATCHES.
    + unfold admission_stop_matches in MATCHES;apply andb_true_iff in MATCHES as[MATCHES SIGNAL].
      apply andb_true_iff in MATCHES as[SAME STOP];apply Int.same_if_eq in SAME;subst got.
      destruct(process_source_frontier_reached _ _ _ _ _ _ _ _ _
        (admission_matching_stop_source locals le memory child status offset word POSITIVE CHILD STATUS LOAD STOP SIGNAL)
        ltac:(intros;discriminate)CONTINUE)as[suffix[REST FINAL]].
      exists(repeat process_waiting waiting++process_waited child status offset Int.zero(wait_status child word)::
        repeat process_source_event 26),suffix,(admission_stopped_parameters le child word),memory,word.
      split.
      * rewrite EVENTS,REST;repeat first[rewrite <-app_assoc|progress(cbn[app])];reflexivity.
      * split;[apply in_or_app;right;left;reflexivity|].
        split;[exact STOP|]. split;[exact SIGNAL|]. split.
        -- unfold admission_stopped_parameters,admission_stopsig_env,admission_stopped_env,admission_wait_return_env;
          repeat rewrite PTree.gso by discriminate;exact CHILD.
        -- split.
           ++ unfold admission_stopped_parameters,admission_stopsig_env,admission_stopped_env,admission_wait_return_env;
             repeat rewrite PTree.gso by discriminate;exact CGROUP.
           ++ split;[exact OUTPUT'|]. split;[exact FINAL|].
              exists(repeat process_waiting waiting);split;[reflexivity|].
              apply admission_passive_leases,admission_waiting_passive.
    + destruct(admission_rejected_status_source locals le memory Kstop got child status offset word
        ltac:(lia)CHILD STATUS LOAD MATCHES)as[count[final[k[CLOSED REJECT]]]].
      exfalso;eapply admission_rejection_cannot_succeed;[exact CLOSED|exact REJECT|exact CONTINUE].
Qed.

Theorem admission_fresh_storage_from_live_tls cell before locals after :
  Mem.valid_block before(tls_block cell) ->admission_allocations before locals after ->
  admission_text locals<>admission_encoded locals /\
  admission_text locals<>tls_block cell /\admission_encoded locals<>tls_block cell /\
  number_output after(admission_encoded locals)Ptrofs.zero.
Proof.
  intros VALID ALLOC.
  destruct(admission_allocation_objects _ _ _ ALLOC)as[OLD[DISTINCT OBJECTS]].
  change(NoDup[admission_text locals;admission_encoded locals])in DISTINCT.
  change(Forall(fun object=>~Mem.valid_block before(fst object) /\
    Mem.range_perm after(fst object)0(snd object)Cur Freeable)
    [(admission_text locals,32);(admission_encoded locals,8)])in OBJECTS.
  inversion OBJECTS as[|text rest[TEXT_FRESH TEXT_FREE]MORE];subst.
  inversion MORE as[|encoded none[ENCODED_FRESH ENCODED_FREE]NIL];subst;cbn in *.
  split.
  - inversion DISTINCT as[|first rest ABSENT REST];subst.
    intro SAME;apply ABSENT;left;symmetry;exact SAME.
  - split;[congruence|]. split;[congruence|].
    split;[change(0+8<=18446744073709551616);lia|]. split.
    + intros position RANGE;eapply Mem.perm_implies;[apply ENCODED_FREE;exact RANGE|constructor].
    + change(8|0);apply Z.divide_0_r.
Qed.

Lemma admission_ready_valid cell memory:
  entry_errno_ready cell memory ->Mem.valid_block memory(tls_block cell).
Proof.
  intros[error[LOW[HIGH[ACCESS LOAD]]]].
  eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[exact ACCESS|constructor].
Qed.

Theorem admission_fresh_storage cell before locals after :
  entry_errno_ready cell before ->admission_allocations before locals after ->
  admission_text locals<>admission_encoded locals /\
  admission_text locals<>tls_block cell /\admission_encoded locals<>tls_block cell /\
  number_output after(admission_encoded locals)Ptrofs.zero.
Proof.
  intros READY ALLOC;apply admission_fresh_storage_from_live_tls with(before:=before);
    [eapply admission_ready_valid;exact READY|exact ALLOC].
Qed.
