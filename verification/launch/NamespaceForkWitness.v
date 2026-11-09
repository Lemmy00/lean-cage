(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.acceptance: One useful source fork publishes the selected peer and child PID. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ErrorNumber Library ProcessEffects FreshMemory ReceiverAllocation StoreSteps WriteAll LibraryMachine.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffInput.
From EntryProcess Require Import ProcessMachine.
From EntryNamespace Require Import NamespaceMachine NamespaceStructure NamespaceAllocation NamespacePaths NamespaceMemory
  NamespaceBorrow NamespaceParentWitness.
Import ListNotations.
Open Scope Z_scope.
Local Opaque namespace_ge.

Lemma namespace_partial_refl cell memory:entry_errno_partial cell memory memory.
Proof. split;[apply Mem.unchanged_on_refl|tauto]. Qed.

Definition namespace_child_old before peer pid object (_:Z):=
  Mem.valid_block before object /\object<>peer /\object<>pid.

Record namespace_useful_fork_arguments cell memory(parameters:temp_env)pid input output errors:Prop:={
  namespace_fork_input:parameters!_input=Some(Vint input);
  namespace_fork_output:parameters!_output=Some(Vint output);
  namespace_fork_errors:parameters!_errors=Some(Vint errors);
  namespace_fork_failure:parameters!_failure=Some(Vint(Int.repr 60));
  namespace_fork_pid:parameters!_child=Some(Vptr pid Ptrofs.zero);
  namespace_fork_pid_access:Mem.valid_access memory Mint32 pid 0 Writable;
  namespace_fork_pid_private:pid<>tls_block cell
}.

Definition namespace_useful_child_input cell borrowed memory parameters:=exists pid,
  namespace_useful_fork_arguments cell memory parameters pid(Int.repr 4)(Int.repr 5)(Int.repr 6) /\
  ~In pid(handoff_borrowed_blocks borrowed).

Definition namespace_child_common_log pair first second :=
  repeat namespace_source_event 1++repeat namespace_source_event 3++
    [namespace_paired(Int.repr 1)(Int.repr 524289)Int.zero pair Ptrofs.zero Int.zero first second]++
    repeat namespace_source_event 4++repeat namespace_source_event 6++
    [namespace_duplicated second(Int.repr 60)(Int.repr 60)]++repeat namespace_source_event 4++
    repeat namespace_source_event 5++[NamespaceCaller.namespace_close_event second(close_ok None)]++
    repeat namespace_source_event 2++repeat namespace_source_event 3++
    repeat namespace_source_event 3++[namespace_masked Int64.mone Int64.zero]++
    repeat namespace_source_event 4++repeat namespace_source_event 3++
    [namespace_defaulted(Int.repr 17)Int64.zero]++repeat namespace_source_event 4++
    repeat namespace_source_event 6++repeat namespace_source_event 3.

Theorem namespace_child_useful_source_framed cell before peer pid input output errors:
  entry_errno_ready cell before ->
  Mem.range_perm before peer 0 4 Cur Freeable ->Mem.range_perm before pid 0 4 Cur Freeable ->
  peer<>pid ->peer<>tls_block cell ->pid<>tls_block cell ->
  exists pair allocated paired published parameters final_temps after,
    child_allocations before pair allocated /\
    Mem.store Mint32 paired peer 0(Vint(Int.repr 9))=Some published /\
    namespace_steps namespace_ge cell
      (live(Callstate(Internal f_create_entry_child)
        [Vint input;Vint output;Vint errors;Vptr peer Ptrofs.zero;Vptr pid Ptrofs.zero]Kstop before))
      (namespace_child_common_log pair(Int.repr 9)(Int.repr 10))
      (live(Callstate namespace_fork_definition[](child_fork_cont pair parameters Kstop)published)) /\
    namespace_step namespace_ge cell
      (live(Callstate namespace_fork_definition[](child_fork_cont pair parameters Kstop)published))
      (namespace_forked(Int.repr 2))
      (live(Returnstate(Vint(Int.repr 2))(child_fork_cont pair parameters Kstop)published)) /\
    namespace_steps namespace_ge cell
      (live(Returnstate(Vint(Int.repr 2))(child_fork_cont pair parameters Kstop)published))
      (repeat namespace_source_event 4++repeat namespace_source_event 3++repeat namespace_source_event 3++
        repeat namespace_source_event 2++[NamespaceCaller.namespace_close_event(Int.repr 60)(close_ok None)]++
        repeat namespace_source_event 3)
      (live(Returnstate(Vint Int.zero)Kstop after)) /\
    final_temps=child_fork_return_env parameters(Int.repr 2) /\
    entry_errno_ready cell after /\Mem.load Mint32 after peer 0=Some(Vint(Int.repr 9)) /\
    Mem.load Mint32 after pid 0=Some(Vint(Int.repr 2)) /\
    Mem.unchanged_on(namespace_child_old before peer pid)before after /\
    (forall object position kind permission,Mem.perm before object position kind permission ->
      Mem.perm after object position kind permission) /\
    entry_errno_ready cell published /\
    Mem.unchanged_on(fun object _=>Mem.valid_block before object /\object<>peer)before published /\
    (forall object position kind permission,Mem.perm before object position kind permission ->
      Mem.perm published object position kind permission) /\
    namespace_useful_fork_arguments cell published parameters pid input output errors.
Proof.
  intros READY PEER PID PEER_PID PEER_TLS PID_TLS.
  set(args:={|child_input:=input;child_output:=output;child_errors:=errors;
    child_peer_pointer:=Vptr peer Ptrofs.zero;child_pid_pointer:=Vptr pid Ptrofs.zero|}).
  destruct(child_entry_allocates before args Kstop)as[pair[allocated[ENTRY[ALLOC[OLD[FRESH PAIR]]]]]].
  assert(VALID_PEER:Mem.valid_block before peer)by(eapply Mem.perm_valid_block with(ofs:=0);apply PEER;lia).
  assert(VALID_PID:Mem.valid_block before pid)by(eapply Mem.perm_valid_block with(ofs:=0);apply PID;lia).
  assert(VALID_TLS:Mem.valid_block before(tls_block cell)).
  { destruct READY as[error[LOW[HIGH[ACCESS LOAD]]]].
    eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[exact ACCESS|constructor]. }
  assert(PAIR_TLS:pair<>tls_block cell)by(intro SAME;apply FRESH;rewrite SAME;exact VALID_TLS).
  assert(PAIR_PEER:pair<>peer)by(intro SAME;apply FRESH;rewrite SAME;exact VALID_PEER).
  assert(PAIR_PID:pair<>pid)by(intro SAME;apply FRESH;rewrite SAME;exact VALID_PID).
  assert(ALLOC_READY:entry_errno_ready cell allocated).
  { eapply namespace_errno_unchanged;[exact READY|]. eapply Mem.unchanged_on_implies;[exact OLD|].
    intros object position SAME VALID;subst object;exact VALID_TLS. }
  assert(FIRST_ACCESS:Mem.valid_access allocated Mint32 pair 0 Writable).
  { split;[intros position RANGE;eapply Mem.perm_implies;[apply PAIR;cbn in RANGE;lia|constructor]|apply Z.divide_0_r]. }
  destruct(Mem.valid_access_store _ _ _ _(Vint(Int.repr 9))FIRST_ACCESS)as[first FIRST_STORE].
  assert(SECOND_ACCESS:Mem.valid_access first Mint32 pair 4 Writable).
  { split;[intros position RANGE;eapply Mem.perm_store_1;[exact FIRST_STORE|];
      eapply Mem.perm_implies;[apply PAIR;cbn in RANGE;lia|constructor]|exists 1;reflexivity]. }
  destruct(Mem.valid_access_store _ _ _ _(Vint(Int.repr 10))SECOND_ACCESS)as[paired SECOND_STORE].
  assert(PAIRED_READY:entry_errno_ready cell paired).
  { eapply namespace_errno_store;[exact PAIR_TLS| |exact SECOND_STORE].
    eapply namespace_errno_store;[exact PAIR_TLS|exact ALLOC_READY|exact FIRST_STORE]. }
  assert(PAIRED_FIRST:Mem.load Mint32 paired pair 0=Some(Vint(Int.repr 9))).
  { erewrite Mem.load_store_other;[|exact SECOND_STORE|right;left;cbn;lia].
    erewrite Mem.load_store_same by exact FIRST_STORE;reflexivity. }
  assert(PAIRED_SECOND:Mem.load Mint32 paired pair 4=Some(Vint(Int.repr 10))).
  { erewrite Mem.load_store_same by exact SECOND_STORE;reflexivity. }
  assert(PEER_ACCESS:Mem.valid_access paired Mint32 peer 0 Writable).
  { eapply Mem.store_valid_access_1;[exact SECOND_STORE|].
    eapply Mem.store_valid_access_1;[exact FIRST_STORE|].
    split;[intros position RANGE;eapply local_allocations_perms;[exact ALLOC|];
      eapply Mem.perm_implies;[apply PEER;exact RANGE|constructor]|apply Z.divide_0_r]. }
  destruct(Mem.valid_access_store _ _ _ _(Vint(Int.repr 9))PEER_ACCESS)as[published PEER_STORE].
  assert(PUBLISHED_READY:entry_errno_ready cell published).
  { eapply namespace_errno_store;[exact PEER_TLS|exact PAIRED_READY|exact PEER_STORE]. }
  assert(PID_ACCESS:Mem.valid_access published Mint32 pid 0 Writable).
  { eapply Mem.store_valid_access_1;[exact PEER_STORE|].
    eapply Mem.store_valid_access_1;[exact SECOND_STORE|].
    eapply Mem.store_valid_access_1;[exact FIRST_STORE|].
    split;[intros position RANGE;eapply local_allocations_perms;[exact ALLOC|];
      eapply Mem.perm_implies;[apply PID;exact RANGE|constructor]|apply Z.divide_0_r]. }
  destruct(Mem.valid_access_store _ _ _ _(Vint(Int.repr 2))PID_ACCESS)as[child_set PID_STORE].
  assert(CHILD_SET_READY:entry_errno_ready cell child_set).
  { eapply namespace_errno_store;[exact PID_TLS|exact PUBLISHED_READY|exact PID_STORE]. }
  assert(CHILD_SET_PAIR:Mem.range_perm child_set pair 0 8 Cur Freeable).
  { intros position RANGE;eapply Mem.perm_store_1;[exact PID_STORE|].
    eapply Mem.perm_store_1;[exact PEER_STORE|]. eapply Mem.perm_store_1;[exact SECOND_STORE|].
    eapply Mem.perm_store_1;[exact FIRST_STORE|apply PAIR;exact RANGE]. }
  destruct(child_free_locals pair child_set CHILD_SET_PAIR)as[after FREE].
  assert(FREE_PAIR:Mem.free child_set pair 0 8=Some after).
  { change(match Mem.free child_set pair 0 8 with Some final=>Some final|None=>None end=Some after)in FREE.
    destruct(Mem.free child_set pair 0 8);[congruence|discriminate]. }
  assert(AFTER_READY:entry_errno_ready cell after).
  { eapply namespace_errno_unchanged;[exact CHILD_SET_READY|].
    eapply Mem.free_unchanged_on;[exact FREE_PAIR|]. intros position RANGE SAME;subst pair;contradiction. }
  set(initial:=child_parameters args).
  set(socketed:=PTree.set _t'2(Vint Int.zero)initial).
  set(duplicated:=child_duplicate_return_env socketed(Int.repr 10)(Int.repr 60)).
  set(closed:=child_original_close_env duplicated(Int.repr 10)).
  set(masked:=PTree.set _t'6(Vlong Int64.zero)closed).
  set(defaulted:=PTree.set _t'8(Vlong Int64.zero)masked).
  set(parameters:=child_publish_peer_env defaulted(Int.repr 9)).
  set(forked:=child_fork_return_env parameters(Int.repr 2)).
  exists pair,allocated,paired,published,parameters,forked,after.
  split;[exact ALLOC|]. split;[exact PEER_STORE|]. split.
  - unfold namespace_child_common_log;eapply namespace_steps_append.
    + eapply namespace_store_path_actual with(P:=fun _=>True).
      eapply store_next;[exact I|exact ENTRY|apply store_done;exact I].
    + eapply namespace_steps_append;[eapply namespace_store_path_actual;apply child_socket_source|].
      eapply namespace_steps_cons.
      { apply namespace_pair_step.
        - split;[change(0+8<=18446744073709551616);lia|]. split;[reflexivity|].
          intros position RANGE;eapply Mem.perm_implies;[apply PAIR;exact RANGE|constructor].
        - eapply namespace_pair_succeeded with(middle:=first)(written:=paired);
            [exact FIRST_STORE|exact SECOND_STORE|apply namespace_partial_refl].
        - exact PAIRED_READY. }
      eapply namespace_steps_append;[eapply namespace_store_path_actual;apply child_socket_success_source|].
      eapply namespace_steps_append;[eapply namespace_store_path_actual;apply child_duplicate_source;exact PAIRED_SECOND|].
      eapply namespace_steps_cons;[apply namespace_duplicate_step;[apply namespace_partial_refl|exact PAIRED_READY]|].
      eapply namespace_steps_append;[eapply namespace_store_path_actual;apply child_duplicate_return_source|].
      eapply namespace_steps_append;[eapply namespace_store_path_actual;apply child_close_original_source;exact PAIRED_SECOND|].
      eapply namespace_steps_cons.
      { apply namespace_process_step,process_entry_step,entry_library_step,close_step.
        split;[apply entry_errno_ready_tls;exact PAIRED_READY|constructor]. }
      eapply namespace_steps_append;[eapply namespace_store_path_actual;apply child_close_original_return_source|].
      eapply namespace_steps_append;[eapply namespace_store_path_actual;apply child_duplicate_nonnegative_source with(failure:=Int.repr 60);
        [unfold closed,duplicated,child_original_close_env,child_duplicate_return_env;WriteAll.lookup|vm_compute;discriminate]|].
      eapply namespace_steps_append;[eapply namespace_store_path_actual;apply child_mask_source|].
      eapply namespace_steps_cons;[apply namespace_mask_step;[apply namespace_partial_refl|exact PAIRED_READY]|].
      eapply namespace_steps_append;[eapply namespace_store_path_actual;apply child_mask_success_source|].
      eapply namespace_steps_append;[eapply namespace_store_path_actual;apply child_default_source|].
      eapply namespace_steps_cons;[apply namespace_default_step;[apply namespace_partial_refl|exact PAIRED_READY]|].
      eapply namespace_steps_append;[eapply namespace_store_path_actual;apply child_default_success_source|].
      eapply namespace_steps_append.
      { eapply namespace_store_path_actual;apply child_publish_peer_source with(first:=Int.repr 9)(peer:=peer)(offset:=Ptrofs.zero).
        - exact PAIRED_FIRST.
        - unfold defaulted,masked,closed,duplicated,socketed,initial,child_original_close_env,child_duplicate_return_env,
            child_duplicate_call_env,child_parameters,args;WriteAll.lookup.
        - exact PEER_STORE. }
      eapply namespace_store_path_actual;apply child_fork_source.
  - split;[apply namespace_fork_step;[apply namespace_partial_refl|exact PUBLISHED_READY]|]. split.
    + eapply namespace_steps_append;[eapply namespace_store_path_actual;apply child_fork_return_source|].
      eapply namespace_steps_append.
      { eapply namespace_store_path_actual;apply child_publish_pid_source with(returned:=Int.repr 2)(object:=pid)(offset:=Ptrofs.zero).
        - unfold forked,child_fork_return_env;WriteAll.lookup.
        - unfold forked,parameters,defaulted,masked,closed,duplicated,socketed,initial,child_publish_peer_env,
            child_fork_return_env,child_original_close_env,child_duplicate_return_env,child_duplicate_call_env,child_parameters,args;WriteAll.lookup.
        - exact PID_STORE. }
      eapply namespace_steps_append;[eapply namespace_store_path_actual;apply child_select_parent_source with(returned:=Int.repr 2);
        [unfold forked,child_fork_return_env;WriteAll.lookup|vm_compute;discriminate]|].
      eapply namespace_steps_append;[eapply namespace_store_path_actual;apply child_close_failure_source with(failure:=Int.repr 60);
        unfold forked,parameters,defaulted,masked,closed,duplicated,socketed,initial,child_publish_peer_env,
          child_fork_return_env,child_original_close_env,child_duplicate_return_env;WriteAll.lookup|].
      eapply namespace_steps_cons.
      { apply namespace_process_step,process_entry_step,entry_library_step,close_step.
        split;[apply entry_errno_ready_tls;exact CHILD_SET_READY|constructor]. }
      eapply namespace_store_path_actual;apply child_finish_source;exact FREE.
    + split;[reflexivity|]. split;[exact AFTER_READY|]. split.
      * erewrite Mem.load_free;[|exact FREE_PAIR|left;intro SAME;apply PAIR_PEER;symmetry;exact SAME].
        erewrite Mem.load_store_other;[|exact PID_STORE|left;exact PEER_PID].
        erewrite Mem.load_store_same by exact PEER_STORE;reflexivity.
      * split.
        -- erewrite Mem.load_free;[|exact FREE_PAIR|left;intro SAME;apply PAIR_PID;symmetry;exact SAME].
           erewrite Mem.load_store_same by exact PID_STORE;reflexivity.
        -- split.
           ++ eapply Mem.unchanged_on_trans.
              ** eapply Mem.unchanged_on_implies;[exact OLD|intros object position[VALID REST]_;exact VALID].
              ** eapply Mem.unchanged_on_trans;[eapply Mem.store_unchanged_on;[exact FIRST_STORE|intros position RANGE[VALID REST];contradiction]|].
                 eapply Mem.unchanged_on_trans;[eapply Mem.store_unchanged_on;[exact SECOND_STORE|intros position RANGE[VALID REST];contradiction]|].
                 eapply Mem.unchanged_on_trans;[eapply Mem.store_unchanged_on;[exact PEER_STORE|intros position RANGE[_[NE REST]];contradiction]|].
                 eapply Mem.unchanged_on_trans;[eapply Mem.store_unchanged_on;[exact PID_STORE|intros position RANGE[_[_ NE]];contradiction]|].
                 eapply Mem.free_unchanged_on;[exact FREE_PAIR|intros position RANGE[VALID REST];contradiction].
           ++ split.
              ** intros object position kind permission PERM;eapply Mem.perm_free_1;[exact FREE_PAIR| |].
                 { left;intro SAME;subst object;apply FRESH;eapply Mem.perm_valid_block;exact PERM. }
                 eapply Mem.perm_store_1;[exact PID_STORE|]. eapply Mem.perm_store_1;[exact PEER_STORE|].
                 eapply Mem.perm_store_1;[exact SECOND_STORE|]. eapply Mem.perm_store_1;[exact FIRST_STORE|].
                 eapply local_allocations_perms;[exact ALLOC|exact PERM].
              ** split;[exact PUBLISHED_READY|]. split.
                 --- eapply Mem.unchanged_on_trans.
                     +++ eapply Mem.unchanged_on_implies;[exact OLD|intros object position[VALID REST]_;exact VALID].
                     +++ eapply Mem.unchanged_on_trans;[eapply Mem.store_unchanged_on;[exact FIRST_STORE|intros position RANGE[VALID REST];contradiction]|].
                         eapply Mem.unchanged_on_trans;[eapply Mem.store_unchanged_on;[exact SECOND_STORE|intros position RANGE[VALID REST];contradiction]|].
                         eapply Mem.store_unchanged_on;[exact PEER_STORE|intros position RANGE[_ NE];contradiction].
                 --- split.
                     +++ intros object position kind permission PERM;eapply Mem.perm_store_1;[exact PEER_STORE|].
                         eapply Mem.perm_store_1;[exact SECOND_STORE|]. eapply Mem.perm_store_1;[exact FIRST_STORE|].
                         eapply local_allocations_perms;[exact ALLOC|exact PERM].
                     +++ constructor;try exact PID_ACCESS;try exact PID_TLS.
                         all:unfold parameters,defaulted,masked,closed,duplicated,socketed,initial,child_publish_peer_env,
                           child_original_close_env,child_duplicate_return_env,child_duplicate_call_env,child_parameters,args;
                           WriteAll.lookup.
Qed.

Theorem namespace_child_useful_source cell before peer pid input output errors:
  entry_errno_ready cell before ->
  Mem.range_perm before peer 0 4 Cur Freeable ->Mem.range_perm before pid 0 4 Cur Freeable ->
  peer<>pid ->peer<>tls_block cell ->pid<>tls_block cell ->
  exists pair allocated paired published parameters final_temps after,
    child_allocations before pair allocated /\
    Mem.store Mint32 paired peer 0(Vint(Int.repr 9))=Some published /\
    namespace_steps namespace_ge cell
      (live(Callstate(Internal f_create_entry_child)
        [Vint input;Vint output;Vint errors;Vptr peer Ptrofs.zero;Vptr pid Ptrofs.zero]Kstop before))
      (namespace_child_common_log pair(Int.repr 9)(Int.repr 10))
      (live(Callstate namespace_fork_definition[](child_fork_cont pair parameters Kstop)published)) /\
    namespace_step namespace_ge cell
      (live(Callstate namespace_fork_definition[](child_fork_cont pair parameters Kstop)published))
      (namespace_forked(Int.repr 2))
      (live(Returnstate(Vint(Int.repr 2))(child_fork_cont pair parameters Kstop)published)) /\
    namespace_steps namespace_ge cell
      (live(Returnstate(Vint(Int.repr 2))(child_fork_cont pair parameters Kstop)published))
      (repeat namespace_source_event 4++repeat namespace_source_event 3++repeat namespace_source_event 3++
        repeat namespace_source_event 2++[NamespaceCaller.namespace_close_event(Int.repr 60)(close_ok None)]++
        repeat namespace_source_event 3)
      (live(Returnstate(Vint Int.zero)Kstop after)) /\
    final_temps=child_fork_return_env parameters(Int.repr 2) /\
    entry_errno_ready cell after /\Mem.load Mint32 after peer 0=Some(Vint(Int.repr 9)) /\
    Mem.load Mint32 after pid 0=Some(Vint(Int.repr 2)) /\
    Mem.unchanged_on(namespace_child_old before peer pid)before after /\
    (forall object position kind permission,Mem.perm before object position kind permission ->
      Mem.perm after object position kind permission).
Proof.
  intros READY PEER PID SEPARATE PEER_TLS PID_TLS.
  destruct(namespace_child_useful_source_framed cell before peer pid input output errors READY PEER PID SEPARATE PEER_TLS PID_TLS)
    as(pair &allocated &paired &published &parameters &final_temps &after &ALLOC &STORE &COMMON &FORK &PARENT
      &TEMPS &AFTER_READY &PEER_VALUE &PID_VALUE &FRAME &PERMS &COMMON_READY &COMMON_FRAME &COMMON_PERMS &ARGUMENTS).
  exists pair,allocated,paired,published,parameters,final_temps,after.
  split;[exact ALLOC|]. split;[exact STORE|]. split;[exact COMMON|]. split;[exact FORK|]. split;[exact PARENT|].
  split;[exact TEMPS|]. split;[exact AFTER_READY|]. split;[exact PEER_VALUE|]. split;[exact PID_VALUE|]. split;assumption.
Qed.
