(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.pid: The actual helper return establishes ordered owned-PID setup evidence. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import IO Machine StoreSteps WriteAll.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessAllocation ProcessStructure ProcessPaths
  ProcessWait ProcessStatus ProcessCallee ProcessPlacement ProcessAdmissionFormat ProcessAdmissionWait.
From EntryProcess Require Import ProcessAdmissionEvents.
From LeanCageMainNumber Require Import NumberMath NumberMemory.
Import ListNotations.
Open Scope Z_scope.

Theorem admission_actual_source_guarantee_with_tail cell before child cgroup status offset events after :
  1<=Int.signed child ->status<>tls_block cell ->Mem.valid_block before(tls_block cell) ->
  process_cgroup_whole_returns cgroup events ->
  process_steps admission_ge cell
    (live(Callstate(Internal f_admit_child)[Vint child;Vint cgroup;Vptr status offset]Kstop before))events
    (live(Returnstate(Vint Int.zero)Kstop after)) ->
  exists locals count bytes error word before_stop before_write before_options suffix,
    Forall decimal_digit_ok bytes /\
    (exists first rest,bytes=first::rest /\first<>Byte.repr 48) /\
    decimal_number bytes=Some(Int.signed child) /\
    admission_is_stopped word=true /\admission_is_sigstop word=true /\
    events=before_stop++process_waited child status offset Int.zero(wait_status child word)::
      (before_write++placement_lift(io_step(admission_write_request cell locals cgroup count)(transfer bytes error))::
        (before_options++process_traced(Int.repr 16896)child(Vlong Int64.zero)
          (Vlong(Int64.repr 1048592))Int64.zero::suffix)) /\
    Forall(admission_lease_event child status offset)before_stop /\
    Forall admission_passive_event before_write /\Forall admission_quiet_event before_options /\
    Forall admission_quiet_event suffix.
Proof.
  intros POSITIVE SEPARATE ERRNO WHOLE RUN.
  destruct(admission_allocate before)as[locals[allocated[ALLOC OBJECTS]]].
  destruct(admission_fresh_storage_from_live_tls _ _ _ _ ERRNO OBJECTS)as[DISTINCT[TEXT_TLS[ENCODED_TLS OUTPUT]]].
  destruct(process_source_frontier_reached _ _ _ _ _ _ _ _ _
    (admission_start_to_wait before locals allocated child cgroup status offset Kstop ALLOC)
    ltac:(intros;discriminate)RUN)as[waiting[EVENTS WAIT]].
  destruct(admission_parameter_bindings child cgroup(Vptr status offset))as[CHILD[CGROUP STATUS]].
  destruct(admission_wait_to_formatter cell locals allocated
    (admission_parameters child cgroup(Vptr status offset))child cgroup status offset waiting after
    POSITIVE SEPARATE CHILD CGROUP STATUS OUTPUT WAIT)
    as[prefix[tail[actual[memory[word FACTS]]]]].
  destruct FACTS as[ORDER[STOP_EVENT[STOP[SIGNAL[CHILD'[CGROUP'[OUTPUT'[CONTINUE EXTRA]]]]]]]].
  destruct EXTRA as[search[SEARCH SEARCH_CLASS]].
  assert(WHOLE_TAIL:process_cgroup_whole_returns cgroup tail).
  { intros request bytes error MEMBER DESCRIPTOR WRITING;eapply WHOLE;[|exact DESCRIPTOR|exact WRITING].
    rewrite EVENTS,ORDER;apply in_or_app;right;apply in_or_app;right;exact MEMBER. }
  destruct(admission_formatter_requires_placement_with_tail cell locals memory actual child cgroup tail after
    CHILD' POSITIVE CGROUP' OUTPUT' DISTINCT TEXT_TLS ENCODED_TLS WHOLE_TAIL CONTINUE)
    as[count[bytes[error[before_write[before_options[suffix[DIGITS[LEADING[VALUE
      [OPTIONS[PASSIVE[QUIET TAIL_QUIET]]]]]]]]]]]].
  exists locals,count,bytes,error,word,(repeat process_source_event 5++search),
    (repeat process_source_event 26++before_write),before_options,suffix.
  split;[exact DIGITS|]. split;[exact LEADING|]. split;[exact VALUE|].
  split;[exact STOP|]. split;[exact SIGNAL|]. split.
  - rewrite EVENTS,ORDER,SEARCH,OPTIONS;repeat first[rewrite <-app_assoc|progress(cbn[app])];reflexivity.
  - split.
    + apply Forall_app;split;[apply admission_passive_leases,admission_source_passive|exact SEARCH_CLASS].
    + split;[apply Forall_app;split;[apply admission_source_passive|exact PASSIVE]|split;assumption].
Qed.

Theorem admission_actual_source_guarantee cell before child cgroup status offset events after :
  1<=Int.signed child ->status<>tls_block cell ->entry_errno_ready cell before ->
  process_cgroup_whole_returns cgroup events ->
  process_steps admission_ge cell
    (live(Callstate(Internal f_admit_child)[Vint child;Vint cgroup;Vptr status offset]Kstop before))events
    (live(Returnstate(Vint Int.zero)Kstop after)) ->
  exists locals count bytes error word before_stop before_write before_options suffix,
    Forall decimal_digit_ok bytes /\
    (exists first rest,bytes=first::rest /\first<>Byte.repr 48) /\
    decimal_number bytes=Some(Int.signed child) /\
    admission_is_stopped word=true /\admission_is_sigstop word=true /\
    events=before_stop++process_waited child status offset Int.zero(wait_status child word)::
      (before_write++placement_lift(io_step(admission_write_request cell locals cgroup count)(transfer bytes error))::
        (before_options++process_traced(Int.repr 16896)child(Vlong Int64.zero)
          (Vlong(Int64.repr 1048592))Int64.zero::suffix)) /\
    Forall(admission_lease_event child status offset)before_stop /\
    Forall admission_passive_event before_write /\Forall admission_quiet_event before_options.
Proof.
  intros POSITIVE SEPARATE ERRNO WHOLE RUN.
  destruct(admission_actual_source_guarantee_with_tail cell before child cgroup status offset events after
    POSITIVE SEPARATE(admission_ready_valid _ _ ERRNO)WHOLE RUN)
    as[locals[count[bytes[error[word[before_stop[before_write[before_options[suffix FACTS]]]]]]]]].
  exists locals,count,bytes,error,word,before_stop,before_write,before_options,suffix;tauto.
Qed.
