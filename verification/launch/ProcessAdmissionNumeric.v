(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.pid: Checked numeric source validates formatter bytes before placement. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import IO Machine StoreSteps WriteAll WriteMemory ErrorNumber.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessAllocation ProcessStructure ProcessPaths ProcessCallee
  ProcessNumeric ProcessPlacement ProcessAdmissionTail ProcessAdmissionEvents.
From LeanCageMainNumber Require Import NumberMath NumberMemory NumberStorage.
Import ListNotations.
Open Scope Z_scope.

Lemma admission_number_errno_ready cell before encoded value after :
  encoded<>tls_block cell ->entry_errno_ready cell before ->
  number_post before encoded Ptrofs.zero(Some value)after ->entry_errno_ready cell after.
Proof.
  intros SEPARATE[error[LOW[HIGH[ACCESS LOAD]]]]POST.
  unfold number_post,Mem.storev in POST;destruct(zle _ _);[|discriminate].
  exists error;unfold initialized_errno;split;[exact LOW|]. split;[exact HIGH|]. split.
  - eapply Mem.store_valid_access_1;eassumption.
  - erewrite Mem.load_store_other;[exact LOAD|exact POST|left;congruence].
Qed.

Theorem admission_readback_requires_placement_with_tail cell locals formatting_before before original child cgroup count events after :
  original!_child=Some(Vint child) ->1<=Int.signed child ->
  original!_cgfd=Some(Vint cgroup) ->original!_pidlength=Some(Vint count) ->
  entry_format_result cell formatting_before(admission_text locals)Ptrofs.zero count before ->
  number_output before(admission_encoded locals)Ptrofs.zero ->
  admission_text locals<>admission_encoded locals ->
  admission_text locals<>tls_block cell ->admission_encoded locals<>tls_block cell ->
  process_cgroup_whole_returns cgroup events ->
  process_steps admission_ge cell
    (live(State f_admit_child(admission_tail 5(fn_body f_admit_child))Kstop(admission_env locals)original before))events
    (live(Returnstate(Vint Int.zero)Kstop after)) ->
  exists bytes error before_write before_options suffix,
    Forall decimal_digit_ok bytes /\
    (exists first rest,bytes=first::rest /\first<>Byte.repr 48) /\
    decimal_number bytes=Some(Int.signed child) /\
    events=before_write++placement_lift(io_step(admission_write_request cell locals cgroup count)(transfer bytes error))::
      (before_options++process_traced(Int.repr 16896)child(Vlong Int64.zero)(Vlong(Int64.repr 1048592))Int64.zero::suffix) /\
    Forall admission_passive_event before_write /\Forall admission_quiet_event before_options /\
    Forall admission_quiet_event suffix.
Proof.
  intros CHILD POSITIVE CGROUP COUNT FORMATTED OUTPUT DISTINCT TEXT_TLS ENCODED_TLS WHOLE RUN.
  destruct(admission_numeric_source cell locals formatting_before before original child count Kstop
    CHILD ltac:(lia)COUNT FORMATTED OUTPUT DISTINCT)as[used[last[PATH[BOUND LEAF]]]].
  assert(NOT_RETURN:forall value memory,last<>Returnstate value Kstop memory).
  { intros value memory SAME;destruct LEAF as[[m[le[k[STATE REST]]]]|[m[le[bytes[first[rest[STATE FACTS]]]]]]];
      subst last;discriminate. }
  destruct(process_source_frontier_reached _ _ _ _ _ _ _ _ _ PATH NOT_RETURN RUN)
    as[rest[EVENTS CONTINUE]].
  destruct LEAF as[[memory[le[k[STATE[CLOSED FRAME]]]]]|[memory[le[bytes[first[remaining
    [STATE[FRAME[LENGTH[EXTENT[BYTES[LEADING[DIGITS[VALUE[INPUT POST]]]]]]]]]]]]]]].
  - subst last;exfalso;eapply process_negative_return_cannot_zero with(fn:=f_admit_child)(k:=k);
      [reflexivity|exact CLOSED|exact CONTINUE].
  - subst last.
    assert(CHILD':le!_child=Some(Vint child)).
    { rewrite(FRAME _child ltac:(cbn;intuition discriminate));exact CHILD. }
    assert(CGROUP':le!_cgfd=Some(Vint cgroup)).
    { rewrite(FRAME _cgfd ltac:(cbn;intuition discriminate));exact CGROUP. }
    assert(COUNT':le!_pidlength=Some(Vint count)).
    { rewrite(FRAME _pidlength ltac:(cbn;intuition discriminate));exact COUNT. }
    destruct(admission_number_errno_ready cell before(admission_encoded locals)(Int.signed child)memory
      ENCODED_TLS(entry_format_errno _ _ _ _ _ _ FORMATTED)POST)as[error ERRNO].
    assert(OWN:write_owned(admission_write_request cell locals cgroup count)bytes memory).
    { eapply admission_write_owned;[exact INPUT|exact LENGTH|lia|exact ERRNO|exact TEXT_TLS]. }
    assert(WHOLE_REST:process_cgroup_whole_returns cgroup rest).
    { intros actual part error' MEMBER DESCRIPTOR WRITING;eapply WHOLE;
      [rewrite EVENTS;apply in_or_app;right;exact MEMBER|exact DESCRIPTOR|exact WRITING]. }
    destruct(admission_success_requires_placement_options_with_tail cell locals le memory child cgroup count bytes rest after
      CHILD' CGROUP' COUNT' OWN ltac:(rewrite BYTES;discriminate)WHOLE_REST CONTINUE)
      as[ioerror[before_write[before_options[suffix[ORDER[PASSIVE[QUIET TAIL]]]]]]].
    exists bytes,ioerror,(repeat process_source_event used++before_write),before_options,suffix.
    split;[exact DIGITS|]. split.
    + exists first,remaining;auto.
    + split;[exact VALUE|]. split.
      * rewrite EVENTS,ORDER;repeat first[rewrite <-app_assoc|progress(cbn[app])];reflexivity.
      * split;[apply Forall_app;split;[apply admission_source_passive|exact PASSIVE]|split;assumption].
Qed.

Theorem admission_readback_requires_placement cell locals formatting_before before original child cgroup count events after :
  original!_child=Some(Vint child) ->1<=Int.signed child ->
  original!_cgfd=Some(Vint cgroup) ->original!_pidlength=Some(Vint count) ->
  entry_format_result cell formatting_before(admission_text locals)Ptrofs.zero count before ->
  number_output before(admission_encoded locals)Ptrofs.zero ->
  admission_text locals<>admission_encoded locals ->
  admission_text locals<>tls_block cell ->admission_encoded locals<>tls_block cell ->
  process_cgroup_whole_returns cgroup events ->
  process_steps admission_ge cell
    (live(State f_admit_child(admission_tail 5(fn_body f_admit_child))Kstop(admission_env locals)original before))events
    (live(Returnstate(Vint Int.zero)Kstop after)) ->
  exists bytes error before_write before_options suffix,
    Forall decimal_digit_ok bytes /\
    (exists first rest,bytes=first::rest /\first<>Byte.repr 48) /\
    decimal_number bytes=Some(Int.signed child) /\
    events=before_write++placement_lift(io_step(admission_write_request cell locals cgroup count)(transfer bytes error))::
      (before_options++process_traced(Int.repr 16896)child(Vlong Int64.zero)(Vlong(Int64.repr 1048592))Int64.zero::suffix) /\
    Forall admission_passive_event before_write /\Forall admission_quiet_event before_options.
Proof.
  intros CHILD POSITIVE CGROUP COUNT FORMATTED OUTPUT DISTINCT TEXT_TLS ENCODED_TLS WHOLE RUN.
  destruct(admission_readback_requires_placement_with_tail cell locals formatting_before before original
    child cgroup count events after CHILD POSITIVE CGROUP COUNT FORMATTED OUTPUT DISTINCT TEXT_TLS
    ENCODED_TLS WHOLE RUN)as[bytes[error[prefix[between[suffix FACTS]]]]].
  exists bytes,error,prefix,between,suffix;tauto.
Qed.
