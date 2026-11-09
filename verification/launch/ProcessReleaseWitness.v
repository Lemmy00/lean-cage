(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-entry.release: Actual source admits useful release under successful primitive returns. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import IO Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll ErrorNumber LibraryMachine.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessAllocation ProcessPaths ProcessReturns ProcessRelease
  ProcessReleaseSafety ProcessReleaseBytes.
Import ListNotations.
Open Scope Z_scope.

Lemma release_initial_errno cell before allocated grant after :
  entry_errno_ready cell before ->Mem.alloc before 0 1=(allocated,grant) ->
  Mem.store Mint8unsigned allocated grant 0(Vint(Int.repr 165))=Some after ->
  entry_errno_ready cell after /\grant<>tls_block cell.
Proof.
  intros[error[LOW[HIGH[ACCESS LOAD]]]]ALLOC STORE.
  assert(VALID:Mem.valid_block before(tls_block cell)).
  { eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[exact ACCESS|constructor]. }
  assert(SEPARATE:grant<>tls_block cell).
  { intro SAME;subst grant;eapply Mem.fresh_block_alloc;[exact ALLOC|exact VALID]. }
  split;[exists error|exact SEPARATE].
  unfold initialized_errno;split;[exact LOW|]. split;[exact HIGH|]. split.
  - eapply Mem.store_valid_access_1;[exact STORE|]. eapply Mem.valid_access_alloc_other;eassumption.
  - erewrite Mem.load_store_other;[|exact STORE|left;congruence].
    eapply Mem.load_alloc_other;eassumption.
Qed.

Lemma release_local_free memory grant : Mem.range_perm memory grant 0 1 Cur Freeable ->
  exists after,Mem.free_list memory(blocks_of_env admission_ge(release_env grant))=Some after.
Proof.
  intro OWN;destruct(Mem.range_perm_free _ _ _ _ OWN)as[after FREE].
  exists after;change(match Mem.free memory grant 0 1 with
    Some next=>Some next|None=>None end=Some after).
  rewrite FREE;reflexivity.
Qed.

Definition release_useful_events child request:=
  repeat process_source_event 7++release_resume_event child::
    (repeat process_source_event 4++(repeat process_source_event 3++
      process_entry(entry_library(original_event(io_step request(transfer[Byte.repr 165]None))))::
        (repeat process_source_event 4++repeat process_source_event 1))).

Theorem release_useful_source_execution_shaped_owned cell before child peer :
  entry_errno_ready cell before ->
  exists events after,
    process_steps admission_ge cell
      (live(Callstate(Internal f_release_child)[Vint child;Vint peer]Kstop before))events
      (live(Returnstate(Vint Int.zero)Kstop after)) /\
    exists request,descriptor request=peer /\operation request=writing /\
      In(process_entry(entry_library(original_event(io_step request(transfer[Byte.repr 165]None)))))events /\
      events=release_useful_events child request.
Proof.
  intro READY;destruct(Mem.alloc before 0 1)as[allocated grant]eqn:ALLOC.
  assert(GRANT:Mem.valid_access allocated Mint8unsigned grant 0 Freeable).
  { eapply Mem.valid_access_alloc_same;[exact ALLOC|lia|cbn;lia|exists 0;reflexivity]. }
  assert(WRITE:Mem.valid_access allocated Mint8unsigned grant 0 Writable).
  { eapply Mem.valid_access_implies;[exact GRANT|constructor]. }
  destruct(Mem.valid_access_store _ _ _ _(Vint(Int.repr 165))WRITE)as[memory STORE].
  destruct(release_initial_errno _ _ _ _ _ READY ALLOC STORE)as[ERRNO SEPARATE].
  assert(BYTE:release_byte memory grant)by(eapply release_store_byte;exact STORE).
  pose proof(release_request_owned cell peer grant memory ERRNO SEPARATE BYTE)as OWN.
  assert(FREEABLE:Mem.range_perm memory grant 0 1 Cur Freeable).
  { intros position BOUND;eapply Mem.perm_store_1;[exact STORE|apply(proj1 GRANT);cbn;exact BOUND]. }
  destruct(release_local_free _ _ FREEABLE)as[after FREE].
  set(parameters:=release_parameters child peer).
  set(resumed:=release_after_resume_env parameters Int64.zero).
  set(q:=release_request cell peer grant).
  set(ioevent:=process_entry(entry_library(original_event(io_step q(transfer[Byte.repr 165]None))))).
  exists(repeat process_source_event 7++release_resume_event child::
    (repeat process_source_event 4++(repeat process_source_event 3++
      ioevent::(repeat process_source_event 4++repeat process_source_event 1)))),after.
  split.
  - eapply process_steps_append;[eapply process_store_path_actual;eapply release_start_to_resume;eassumption|].
    econstructor.
    + unfold release_resume_event;apply process_ptrace_step.
      * unfold process_ptrace_frame;cbn;apply Mem.unchanged_on_refl.
      * exact ERRNO.
    + eapply process_steps_append.
      * eapply process_store_path_actual.
        pose proof(release_resume_return_source grant parameters memory Kstop Int64.zero)as RESUME.
        change(release_resumed Int64.zero)with true in RESUME;exact RESUME.
      * eapply process_steps_append.
        -- eapply process_store_path_actual;apply release_write_call_source.
           unfold resumed,release_after_resume_env,parameters,release_parameters;WriteAll.lookup.
        -- econstructor.
           ++ unfold ioevent;apply process_entry_step,entry_library_step,original_step.
              eapply effect with(q:=q)(r:=transfer[Byte.repr 165]None).
              ** constructor;reflexivity.
              ** apply write_returns;[exact OWN|reflexivity|cbn;lia|exact BYTE|constructor].
           ++ eapply process_steps_append.
              ** eapply process_store_path_actual.
                 pose proof(release_write_return_source grant resumed memory Kstop Int64.one)as WRITTEN.
                 change(release_written Int64.one)with true in WRITTEN;exact WRITTEN.
              ** eapply process_store_path_actual with(P:=fun _=>True).
                 eapply store_next;[exact I|eapply certified_local_return_edge|apply store_done;exact I].
                 --- apply old_expression_value,value_int.
                 --- reflexivity.
                 --- exact FREE.
  - exists q;split;[reflexivity|]. split;[reflexivity|]. split.
    + apply in_or_app;right;right;apply in_or_app;right;apply in_or_app;right;left;reflexivity.
    + reflexivity.
Qed.

Theorem release_useful_source_execution_shaped cell before child peer :
  entry_errno_ready cell before ->
  exists events after,
    process_steps admission_ge cell
      (live(Callstate(Internal f_release_child)[Vint child;Vint peer]Kstop before))events
      (live(Returnstate(Vint Int.zero)Kstop after)) /\
    exists request,descriptor request=peer /\
      In(process_entry(entry_library(original_event(io_step request(transfer[Byte.repr 165]None)))))events /\
      events=release_useful_events child request.
Proof.
  intro READY;destruct(release_useful_source_execution_shaped_owned cell before child peer READY)
    as[events[after[RUN[request[DESCRIPTOR[WRITING[WRITE SHAPE]]]]]]].
  exists events,after;split;[exact RUN|]. exists request;split;[exact DESCRIPTOR|]. split;assumption.
Qed.

Theorem release_useful_source_execution cell before child peer :
  entry_errno_ready cell before ->
  exists events after,
    process_steps admission_ge cell
      (live(Callstate(Internal f_release_child)[Vint child;Vint peer]Kstop before))events
      (live(Returnstate(Vint Int.zero)Kstop after)) /\
    exists request,descriptor request=peer /\
      In(process_entry(entry_library(original_event(io_step request(transfer[Byte.repr 165]None)))))events.
Proof.
  intro READY;destruct(release_useful_source_execution_shaped cell before child peer READY)
    as[events[after[RUN[request[DESCRIPTOR[WRITE SHAPE]]]]]].
  exists events,after;split;[exact RUN|]. exists request;split;assumption.
Qed.
