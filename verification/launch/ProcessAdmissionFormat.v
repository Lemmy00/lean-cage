(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.pid: The real child argument and formatter return feed checked placement. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import IO Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffEffects
  NativeHandoffArguments NativeHandoffFormat.
From EntryProcess Require Import ProcessMachine ProcessAllocation ProcessStructure ProcessReturns
  ProcessPaths ProcessCallee ProcessNumeric ProcessPlacement ProcessAdmissionNumeric ProcessAdmissionEvents.
From LeanCageMainNumber Require Import NumberMath NumberMemory.
Import ListNotations.
Open Scope Z_scope.

Theorem admission_format_call_source locals le memory child :le!_child=Some(Vint child) ->
  store_path admission_ge(fun _=>True)
    (State f_admit_child(admission_tail 4(fn_body f_admit_child))Kstop(admission_env locals)le memory)3
    (Callstate entry_decimal_definition
      [Vptr(admission_text locals)Ptrofs.zero;Vlong(Int64.repr(Int.signed child))]
      (admission_format_cont locals le Kstop)memory).
Proof.
  intro CHILD.
  change(admission_tail 4(fn_body f_admit_child))with(Ssequence admission_format(admission_tail 5(fn_body f_admit_child))).
  change admission_format with(Ssequence
    (Scall(Some _t'4)(Evar _entry_decimal(Tfunction[tptr tschar;tulong]tint cc_default))
      [Evar _pidtext(tarray tschar 32);Ecast(Etempvar _child tint)tulong])
    (Sset _pidlength(Etempvar _t'4 tint))).
  admission_route;admission_route;eapply store_next;
    [exact I|eapply certified_call_edge|apply store_done;exact I].
  - reflexivity.
  - apply old_expression_value;eapply value_function;
      [apply admission_nonlocal_binding;discriminate|exact(proj1 handoff_decimal_binding)|reflexivity].
  - eapply cons_argument_values.
    + apply handoff_array_value;apply(proj1(admission_local_bindings locals)).
    + reflexivity.
    + eapply cons_argument_values.
      * eapply cast_expression_value;[apply old_expression_value,value_temp;exact CHILD|reflexivity].
      * reflexivity.
      * apply no_argument_values.
  - exact(proj2 handoff_decimal_binding).
  - reflexivity.
Qed.

Lemma admission_format_process_exact ge cell before output offset value k event target :
  process_step ge cell
    (live(Callstate entry_decimal_definition[Vptr output offset;Vlong value]k before))event target ->
  exists native,event=process_entry native /\
    entry_handoff_step ge cell
      (live(Callstate entry_decimal_definition[Vptr output offset;Vlong value]k before))native target.
Proof. intro STEP;inversion STEP;subst;try discriminate;eauto. Qed.

Theorem admission_format_return_decomposition ge cell before output offset value k events result after :
  process_steps ge cell
    (live(Callstate entry_decimal_definition[Vptr output offset;Vlong value]k before))events
    (live(Returnstate result Kstop after)) ->
  exists waiting count formatted rest,
    events=repeat(process_entry entry_primitive_wait)waiting++
      process_entry(entry_formatted output offset value count)::rest /\
    entry_format_result cell before output offset count formatted /\
    process_steps ge cell(live(Returnstate(Vint count)k formatted))rest(live(Returnstate result Kstop after)).
Proof.
  remember(live(Callstate entry_decimal_definition[Vptr output offset;Vlong value]k before))as initial eqn:INITIAL.
  remember(live(Returnstate result Kstop after))as final eqn:FINAL.
  intro RUN;revert before INITIAL FINAL.
  induction RUN as[state|first event middle rest last STEP RUN IH];intros before INITIAL FINAL;[congruence|].
  subst first last.
  destruct(admission_format_process_exact _ _ _ _ _ _ _ _ _ STEP)as[native[EVENT REAL]];subst event.
  destruct(handoff_format_cases _ _ _ _ _ _ _ _ _ REAL)
    as[[count[formatted[OWN[RESULT[EVENT TARGET]]]]]|[[EVENT TARGET]|
      [[formatted[PARTIAL[EVENT TARGET]]]|[EVENT TARGET]]]];subst.
  - exists 0%nat,count,formatted,rest;cbn;auto.
  - destruct(IH before eq_refl eq_refl)as[waiting[count[formatted[tail[EVENTS[RESULT CONTINUE]]]]]].
    exists(S waiting),count,formatted,tail;cbn;split;[congruence|auto].
  - destruct(process_dead_steps _ _ _ _ _ RUN)as[_ IMPOSSIBLE];discriminate.
  - destruct(process_dead_steps _ _ _ _ _ RUN)as[_ IMPOSSIBLE];discriminate.
Qed.

Lemma admission_format_preserves_output cell before text count after encoded :
  number_output before encoded Ptrofs.zero ->
  entry_format_result cell before text Ptrofs.zero count after ->
  number_output after encoded Ptrofs.zero.
Proof.
  intros[BOUND[RANGE ALIGN]]RESULT;split;[exact BOUND|]. split;[|exact ALIGN].
  intros position INTERVAL;apply(entry_format_permissions _ _ _ _ _ _ RESULT);
    apply RANGE;exact INTERVAL.
Qed.

Theorem admission_formatter_requires_placement_with_tail cell locals before original child cgroup events after :
  original!_child=Some(Vint child) ->1<=Int.signed child ->original!_cgfd=Some(Vint cgroup) ->
  number_output before(admission_encoded locals)Ptrofs.zero ->
  admission_text locals<>admission_encoded locals ->
  admission_text locals<>tls_block cell ->admission_encoded locals<>tls_block cell ->
  process_cgroup_whole_returns cgroup events ->
  process_steps admission_ge cell
    (live(State f_admit_child(admission_tail 4(fn_body f_admit_child))Kstop(admission_env locals)original before))events
    (live(Returnstate(Vint Int.zero)Kstop after)) ->
  exists count bytes error before_write before_options suffix,
    Forall decimal_digit_ok bytes /\(exists first rest,bytes=first::rest /\first<>Byte.repr 48) /\
    decimal_number bytes=Some(Int.signed child) /\
    events=before_write++placement_lift(io_step(admission_write_request cell locals cgroup count)(transfer bytes error))::
      (before_options++process_traced(Int.repr 16896)child(Vlong Int64.zero)(Vlong(Int64.repr 1048592))Int64.zero::suffix) /\
    Forall admission_passive_event before_write /\Forall admission_quiet_event before_options /\
    Forall admission_quiet_event suffix.
Proof.
  intros CHILD POSITIVE CGROUP OUTPUT DISTINCT TEXT_TLS ENCODED_TLS WHOLE RUN.
  destruct(process_source_frontier_reached _ _ _ _ _ _ _ _ _
    (admission_format_call_source locals original before child CHILD)ltac:(intros;discriminate)RUN)
    as[tail[EVENTS CONTINUE]].
  destruct(admission_format_return_decomposition _ _ _ _ _ _ _ _ _ _ CONTINUE)
    as[waiting[count[formatted[rest[FORMATTED[RESULT REST]]]]]].
  destruct(process_source_frontier_reached _ _ _ _ _ _ _ _ _
    (admission_format_return_source locals original formatted count Kstop)ltac:(intros;discriminate)REST)
    as[numeric[NUMERIC RUN_NUMERIC]].
  assert(CHILD':(admission_format_returned original count)!_child=Some(Vint child)).
  { unfold admission_format_returned;repeat rewrite PTree.gso by discriminate;exact CHILD. }
  assert(CGROUP':(admission_format_returned original count)!_cgfd=Some(Vint cgroup)).
  { unfold admission_format_returned;repeat rewrite PTree.gso by discriminate;exact CGROUP. }
  assert(COUNT':(admission_format_returned original count)!_pidlength=Some(Vint count)).
  { unfold admission_format_returned;apply PTree.gss. }
  assert(OUTPUT':number_output formatted(admission_encoded locals)Ptrofs.zero).
  { eapply admission_format_preserves_output;eassumption. }
  assert(WHOLE_NUMERIC:process_cgroup_whole_returns cgroup numeric).
  { intros actual bytes error MEMBER DESCRIPTOR WRITING;eapply WHOLE;[|exact DESCRIPTOR|exact WRITING].
    rewrite EVENTS,FORMATTED,NUMERIC;apply in_or_app;right;apply in_or_app;right;right;
      apply in_or_app;right;exact MEMBER. }
  destruct(admission_readback_requires_placement_with_tail cell locals before formatted
    (admission_format_returned original count)child cgroup count numeric after
    CHILD' POSITIVE CGROUP' COUNT' RESULT OUTPUT' DISTINCT TEXT_TLS ENCODED_TLS WHOLE_NUMERIC RUN_NUMERIC)
    as[bytes[error[before_write[before_options[suffix[DIGITS[LEADING[VALUE[ORDER[PASSIVE[QUIET TAIL]]]]]]]]]]].
  exists count,bytes,error,(repeat process_source_event 3++
    (repeat(process_entry entry_primitive_wait)waiting++
      process_entry(entry_formatted(admission_text locals)Ptrofs.zero(Int64.repr(Int.signed child))count)::
        (repeat process_source_event 4++before_write))),before_options,suffix.
  split;[exact DIGITS|]. split;[exact LEADING|]. split;[exact VALUE|]. split.
  - rewrite EVENTS,FORMATTED,NUMERIC,ORDER;
      repeat first[rewrite <-app_assoc|progress(cbn[app])];reflexivity.
  - split;[|split;assumption]. repeat rewrite Forall_app;split;[apply admission_source_passive|].
    split;[apply admission_repeat_forall;exact I|]. constructor;[exact I|].
    apply Forall_app;split;[apply admission_source_passive|exact PASSIVE].
Qed.

Theorem admission_formatter_requires_placement cell locals before original child cgroup events after :
  original!_child=Some(Vint child) ->1<=Int.signed child ->original!_cgfd=Some(Vint cgroup) ->
  number_output before(admission_encoded locals)Ptrofs.zero ->
  admission_text locals<>admission_encoded locals ->
  admission_text locals<>tls_block cell ->admission_encoded locals<>tls_block cell ->
  process_cgroup_whole_returns cgroup events ->
  process_steps admission_ge cell
    (live(State f_admit_child(admission_tail 4(fn_body f_admit_child))Kstop(admission_env locals)original before))events
    (live(Returnstate(Vint Int.zero)Kstop after)) ->
  exists count bytes error before_write before_options suffix,
    Forall decimal_digit_ok bytes /\(exists first rest,bytes=first::rest /\first<>Byte.repr 48) /\
    decimal_number bytes=Some(Int.signed child) /\
    events=before_write++placement_lift(io_step(admission_write_request cell locals cgroup count)(transfer bytes error))::
      (before_options++process_traced(Int.repr 16896)child(Vlong Int64.zero)(Vlong(Int64.repr 1048592))Int64.zero::suffix) /\
    Forall admission_passive_event before_write /\Forall admission_quiet_event before_options.
Proof.
  intros CHILD POSITIVE CGROUP OUTPUT DISTINCT TEXT_TLS ENCODED_TLS WHOLE RUN.
  destruct(admission_formatter_requires_placement_with_tail cell locals before original child cgroup events after
    CHILD POSITIVE CGROUP OUTPUT DISTINCT TEXT_TLS ENCODED_TLS WHOLE RUN)
    as[count[bytes[error[prefix[between[suffix FACTS]]]]]].
  exists count,bytes,error,prefix,between,suffix;tauto.
Qed.
