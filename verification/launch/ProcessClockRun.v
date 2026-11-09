(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.clock: Actual observations determine the clock return and frame. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import IO Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll LibraryMachine.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessAllocation ProcessPaths ProcessClock ProcessClockMemory.
From EntryProcess Require Import ProcessCallee.
From LeanCageMainNumber Require Import NumberInitial.
Import ListNotations.
Open Scope Z_scope.

Theorem clock_block_list output:blocks_of_env admission_ge(clock_env output)=[(output,0,16)].
Proof.
  change([(output,0,sizeof admission_ge clock_type)]=[(output,0,16)]).
  rewrite(proj1 clock_actual_layout);reflexivity.
Qed.

Theorem clock_free_list memory output after:Mem.free memory output 0 16=Some after ->
  Mem.free_list memory(blocks_of_env admission_ge(clock_env output))=Some after.
Proof. intro FREE;rewrite clock_block_list;cbn;rewrite FREE;reflexivity. Qed.

Definition clock_observed_word observation:=
  match observation with
  |clock_failed _=>Int64.zero
  |clock_value seconds nanos=>if Int64.signed seconds<?0 then Int64.zero else
      if 18446744073709550<?Int64.signed seconds then Int64.zero else clock_millis seconds nanos
  end.

Lemma clock_zero_return_source output le memory k after:
  Mem.free memory output 0 16=Some after ->
  store_path admission_ge(fun _=>True)
    (State f_now_ms(Sreturn(Some(Econst_int Int.zero tint)))k(clock_env output)le memory)1
    (Returnstate(Vlong Int64.zero)(call_cont k)after).
Proof.
  intro FREE;eapply store_next;[exact I|eapply certified_local_return_edge|apply store_done;exact I].
  - apply old_expression_value,value_int.
  - reflexivity.
  - apply clock_free_list;exact FREE.
Qed.

Lemma clock_millis_return_source output le memory k after seconds nanos:
  Mem.free memory output 0 16=Some after ->
  store_path admission_ge(fun _=>True)
    (State f_now_ms(Sreturn(Some clock_result_expression))k(clock_env output)
      (clock_success_env le seconds nanos)memory)1
    (Returnstate(Vlong(clock_millis seconds nanos))(call_cont k)after).
Proof.
  intro FREE;eapply store_next;[exact I|eapply certified_local_return_edge|apply store_done;exact I].
  - apply clock_computed_result.
  - reflexivity.
  - apply clock_free_list;exact FREE.
Qed.

Theorem clock_observation_source cell output before observation memory le k:
  output<>tls_block cell ->process_clock_effect cell output Ptrofs.zero before observation memory ->
  Mem.range_perm memory output 0 16 Cur Freeable ->
  exists count after,(count<=23)%nat /\Mem.free memory output 0 16=Some after /\
    store_path admission_ge(fun _=>True)
      (Returnstate(Vint(clock_return observation))(clock_cont output le k)memory)count
      (Returnstate(Vlong(clock_observed_word observation))(call_cont k)after).
Proof.
  intros SEPARATE EFFECT OWN;destruct(Mem.range_perm_free _ _ _ _ OWN)as[after FREE].
  destruct observation as[error|seconds nanos].
  - exists 10%nat,after;split;[lia|]. split;[exact FREE|].
    eapply store_path_trans with(n:=9%nat).
    + eapply number_path_implication with(P:=fun current=>current=memory);[intros;exact I|apply clock_failed_source].
    + apply clock_zero_return_source with(k:=Kseq clock_result k);exact FREE.
  - destruct(clock_value_loads _ _ _ _ _ _ SEPARATE EFFECT)as[SECONDS NANOS].
    unfold clock_observed_word;destruct(Int64.signed seconds<?0)eqn:NEGATIVE.
    + apply Z.ltb_lt in NEGATIVE;exists 13%nat,after;split;[lia|]. split;[exact FREE|].
      eapply store_path_trans with(n:=12%nat).
      * eapply number_path_implication with(P:=fun current=>current=memory);[intros;exact I|].
        exact(clock_negative_source output le memory k seconds NEGATIVE SECONDS).
      * apply clock_zero_return_source with(k:=Kseq clock_result k);exact FREE.
    + apply Z.ltb_ge in NEGATIVE;destruct(18446744073709550<?Int64.signed seconds)eqn:OVERFLOW.
      * apply Z.ltb_lt in OVERFLOW;exists 16%nat,after;split;[lia|]. split;[exact FREE|].
        eapply store_path_trans with(n:=15%nat).
        -- eapply number_path_implication with(P:=fun current=>current=memory);[intros;exact I|].
           exact(clock_overflow_source output le memory k seconds OVERFLOW SECONDS).
        -- apply clock_zero_return_source with(k:=Kseq clock_result k);exact FREE.
      * apply Z.ltb_ge in OVERFLOW;exists 23%nat,after;split;[lia|]. split;[exact FREE|].
        eapply store_path_trans with(n:=22%nat).
        -- eapply number_path_implication with(P:=fun current=>current=memory);[intros;exact I|].
           exact(clock_success_source output le memory k seconds nanos ltac:(lia)SECONDS NANOS).
        -- apply clock_millis_return_source;exact FREE.
Qed.

Lemma clock_entry_only_loss ge cell before clock output offset k event target:
  entry_handoff_step ge cell(live(Callstate process_clock_definition[Vint clock;Vptr output offset]k before))event target ->
  event=entry_library(original_event loss_step) /\target=dead before.
Proof.
  intro STEP;inversion STEP;subst;try discriminate.
  match goal with LIB:library_step _ _ _ _ _|-_=>inversion LIB;subst;try discriminate end.
  - match goal with ORIGINAL:Machine.step _ _ _ _ _|-_=>
      inversion ORIGINAL;subst;cbn in *;try contradiction;
        try match goal with BOUND:boundary _ _ _|-_=>inversion BOUND;subst;destruct(operation q);discriminate end
    end;auto.
  - match goal with READY:library_ready _ _|-_=>inversion READY end.
Qed.

Theorem clock_process_cases ge cell before clock output offset k event target:
  process_step ge cell(live(Callstate process_clock_definition[Vint clock;Vptr output offset]k before))event target ->
  (exists observation after,process_clock_owned before output offset /\
    process_clock_effect cell output offset before observation after /\entry_errno_ready cell after /\
    event=process_clocked clock output offset observation /\
    target=live(Returnstate(Vint(clock_return observation))k after)) \/
  (event=process_waiting /\target=live(Callstate process_clock_definition[Vint clock;Vptr output offset]k before)) \/
  (exists after,process_clock_partial cell output offset before after /\
    event=process_clock_lost clock output offset /\target=dead after) \/
  (event=process_entry(entry_library(original_event loss_step)) /\target=dead before).
Proof.
  intro STEP;inversion STEP;subst;try discriminate;eauto 15.
  destruct(clock_entry_only_loss _ _ _ _ _ _ _ _ _ H)as[EVENT TARGET];subst;auto.
Qed.

Theorem clock_return_decomposition ge cell before clock output offset k events value after:
  process_steps ge cell(live(Callstate process_clock_definition[Vint clock;Vptr output offset]k before))events
    (live(Returnstate value Kstop after)) ->
  exists waiting observation memory rest,
    events=repeat process_waiting waiting++process_clocked clock output offset observation::rest /\
    process_clock_effect cell output offset before observation memory /\entry_errno_ready cell memory /\
    process_steps ge cell(live(Returnstate(Vint(clock_return observation))k memory))rest
      (live(Returnstate value Kstop after)).
Proof.
  remember(live(Callstate process_clock_definition[Vint clock;Vptr output offset]k before))as initial eqn:INITIAL.
  remember(live(Returnstate value Kstop after))as final eqn:FINAL.
  intro RUN;revert before INITIAL FINAL.
  induction RUN as[state|first event middle rest last STEP RUN IH];intros before INITIAL FINAL;[congruence|].
  subst first last.
  destruct(clock_process_cases _ _ _ _ _ _ _ _ _ STEP)
    as[[observation[memory[OWN[EFFECT[READY[EVENT TARGET]]]]]]|[[EVENT TARGET]|
      [[memory[PARTIAL[EVENT TARGET]]]|[EVENT TARGET]]]];subst.
  - exists 0%nat,observation,memory,rest;cbn;auto.
  - destruct(IH before eq_refl eq_refl)as[waiting[observation[memory[tail[EVENTS[EFFECT[READY CONTINUE]]]]]]].
    exists(S waiting),observation,memory,tail;cbn;split;[congruence|auto].
  - destruct(process_dead_steps _ _ _ _ _ RUN)as[_ IMPOSSIBLE];discriminate.
  - destruct(process_dead_steps _ _ _ _ _ RUN)as[_ IMPOSSIBLE];discriminate.
Qed.

Theorem clock_all_source_returns cell before events value after:
  entry_errno_ready cell before ->
  process_steps admission_ge cell(live(Callstate(Internal f_now_ms)[]Kstop before))events
    (live(Returnstate value Kstop after)) ->
  exists output observation,
    value=Vlong(clock_observed_word observation) /\clock_old_frame cell before after /\
    In(process_clocked Int.one output Ptrofs.zero observation)events.
Proof.
  intros[error[LOW[HIGH[ACCESS LOAD]]]]RUN.
  destruct(Mem.alloc before 0 16)as[allocated output]eqn:ALLOC.
  assert(VALID:Mem.valid_block before(tls_block cell)).
  { eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[exact ACCESS|constructor]. }
  assert(FRESH:~Mem.valid_block before output)by(eapply Mem.fresh_block_alloc;exact ALLOC).
  assert(SEPARATE:output<>tls_block cell)by congruence.
  destruct(process_source_frontier_reached _ _ _ _ _ _ _ _ _
    (clock_start_to_call before allocated output Kstop ALLOC)ltac:(intros;discriminate)RUN)
    as[tail[EVENTS CONTINUE]].
  destruct(clock_return_decomposition _ _ _ _ _ _ _ _ _ _ CONTINUE)
    as[waiting[observation[memory[rest[RETURN[EFFECT[READY REST]]]]]]].
  assert(OWN:Mem.range_perm memory output 0 16 Cur Freeable).
  { intros position RANGE;apply(clock_effect_permissions _ _ _ _ _ _ EFFECT).
    eapply Mem.perm_alloc_2;[exact ALLOC|exact RANGE]. }
  destruct(clock_observation_source cell output allocated observation memory clock_temps Kstop SEPARATE EFFECT OWN)
    as[count[freed[BOUND[FREE PATH]]]].
  destruct(process_source_return_exact _ _ _ _ _ _ _ _ _ _ PATH REST)as[VALUE AFTER];subst after.
  exists output,observation;split;[exact VALUE|]. split.
  - eapply clock_fresh_old_free;[exact FRESH| |exact FREE].
    eapply clock_fresh_old_effect;[exact FRESH| |exact EFFECT].
    eapply clock_fresh_old_alloc;exact ALLOC.
  - rewrite EVENTS,RETURN;apply in_or_app;right;apply in_or_app;right;left;reflexivity.
Qed.

(* The TLS allocation fact is weaker than initialized errno: no stored value,
   access permission or errno frame is needed to establish the C return type. *)
Theorem clock_actual_return_type cell before events value after :
  Mem.valid_block before (tls_block cell) ->
  process_steps admission_ge cell (live (Callstate (Internal f_now_ms) [] Kstop before)) events
    (live (Returnstate value Kstop after)) ->
  exists millis,value=Vlong millis.
Proof.
  intros VALID RUN.
  destruct (Mem.alloc before 0 16) as [allocated output] eqn:ALLOC.
  assert (FRESH : ~Mem.valid_block before output) by (eapply Mem.fresh_block_alloc;exact ALLOC).
  assert (SEPARATE : output<>tls_block cell) by congruence.
  destruct (process_source_frontier_reached _ _ _ _ _ _ _ _ _
    (clock_start_to_call before allocated output Kstop ALLOC) ltac:(intros;discriminate) RUN)
    as [tail [EVENTS CONTINUE]].
  destruct (clock_return_decomposition _ _ _ _ _ _ _ _ _ _ CONTINUE)
    as [waiting [observation [memory [rest [RETURN [EFFECT [READY REST]]]]]]].
  assert (OWN : Mem.range_perm memory output 0 16 Cur Freeable).
  { intros position RANGE;apply (clock_effect_permissions _ _ _ _ _ _ EFFECT).
    eapply Mem.perm_alloc_2;[exact ALLOC|exact RANGE]. }
  destruct (clock_observation_source cell output allocated observation memory clock_temps Kstop
    SEPARATE EFFECT OWN) as [count [freed [BOUND [FREE PATH]]]].
  destruct (process_source_return_exact _ _ _ _ _ _ _ _ _ _ PATH REST) as [VALUE AFTER].
  exists (clock_observed_word observation);exact VALUE.
Qed.

Theorem clock_useful_source_execution cell before:
  entry_errno_ready cell before ->
  exists events after,process_steps admission_ge cell
    (live(Callstate(Internal f_now_ms)[]Kstop before))events(live(Returnstate(Vlong(Int64.repr 1000))Kstop after)) /\
    clock_old_frame cell before after /\
    exists output,In(process_clocked Int.one output Ptrofs.zero(clock_value Int64.one Int64.zero))events.
Proof.
  intro READY;pose proof READY as[error[LOW[HIGH[ACCESS LOAD]]]].
  destruct(Mem.alloc before 0 16)as[allocated output]eqn:ALLOC.
  assert(VALID:Mem.valid_block before(tls_block cell)).
  { eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[exact ACCESS|constructor]. }
  assert(FRESH:~Mem.valid_block before output)by(eapply Mem.fresh_block_alloc;exact ALLOC).
  assert(SEPARATE:output<>tls_block cell)by congruence.
  assert(ALLOCATED_ERRNO:entry_errno_ready cell allocated).
  { exists error;split;[exact LOW|]. split;[exact HIGH|]. split.
    - eapply Mem.valid_access_alloc_other;eassumption.
    - eapply Mem.load_alloc_other;eassumption. }
  set(bytes:=encode_val Mint64(Vlong Int64.one)++encode_val Mint64(Vlong Int64.zero)).
  assert(RANGE:Mem.range_perm allocated output 0(0+Z.of_nat(length bytes))Cur Writable).
  { unfold bytes;rewrite app_length,!encode_val_length;cbn.
    intros position INTERVAL;eapply Mem.perm_implies;[eapply Mem.perm_alloc_2;[exact ALLOC|exact INTERVAL]|constructor]. }
  destruct(Mem.range_perm_storebytes _ _ _ _ RANGE)as[memory COPY].
  assert(EFFECT:process_clock_effect cell output Ptrofs.zero allocated(clock_value Int64.one Int64.zero)memory).
  { eapply process_clock_value_effect with(copied:=memory)(error:=None);[exact COPY|constructor]. }
  assert(MEMORY_ERRNO:entry_errno_ready cell memory).
  { eapply clock_copy_errno_ready;[exact SEPARATE|exact ALLOCATED_ERRNO|exact COPY]. }
  assert(OWN:process_clock_owned allocated output Ptrofs.zero).
  { split;[change(0+16<=18446744073709551616);lia|].
    intros position INTERVAL;eapply Mem.perm_implies;[eapply Mem.perm_alloc_2;[exact ALLOC|exact INTERVAL]|constructor]. }
  assert(FREEABLE:Mem.range_perm memory output 0 16 Cur Freeable).
  { intros position INTERVAL;apply(clock_effect_permissions _ _ _ _ _ _ EFFECT).
    eapply Mem.perm_alloc_2;[exact ALLOC|exact INTERVAL]. }
  destruct(clock_observation_source cell output allocated(clock_value Int64.one Int64.zero)memory clock_temps Kstop
    SEPARATE EFFECT FREEABLE)as[count[after[BOUND[FREE PATH]]]].
  change(clock_observed_word(clock_value Int64.one Int64.zero))with(Int64.repr 1000)in PATH.
  set(events:=repeat process_source_event 6++
    process_clocked Int.one output Ptrofs.zero(clock_value Int64.one Int64.zero)::repeat process_source_event count).
  assert(RUN:process_steps admission_ge cell(live(Callstate(Internal f_now_ms)[]Kstop before))events
    (live(Returnstate(Vlong(Int64.repr 1000))Kstop after))).
  { unfold events;eapply process_steps_append.
    - eapply process_store_path_actual;apply clock_start_to_call;exact ALLOC.
    - econstructor;[apply process_clock_step;[exact OWN|exact EFFECT|exact MEMORY_ERRNO]|].
      eapply process_store_path_actual;exact PATH. }
  exists events,after;split;[exact RUN|]. split.
  - destruct(clock_all_source_returns _ _ _ _ _ READY RUN)as[object[observation[VALUE[FRAME OBSERVED]]]];exact FRAME.
  - exists output;unfold events;apply in_or_app;right;left;reflexivity.
Qed.
