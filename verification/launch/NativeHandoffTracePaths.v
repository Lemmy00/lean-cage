(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Split the same actual image-containing run, retaining descriptor flag events. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine StoreSteps LibraryMachine Library.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffPaths NativeHandoffEffects
  NativeHandoffInitial HandoffRegion.
From EntryNative Require Export NativeHandoffTraceEvents.
Import ListNotations.
Open Scope Z_scope.

Lemma handoff_flags_projection_source count : handoff_flags_projection(repeat handoff_source_event count)=[].
Proof. induction count;cbn[handoff_flags_projection handoff_source_event handoff_event_flags];assumption||reflexivity. Qed.
Lemma handoff_source_has_no_image count path arguments environment :
  ~In(entry_image path arguments environment)(repeat handoff_source_event count).
Proof. induction count;cbn;[tauto|intros[HEAD|TAIL];discriminate||contradiction]. Qed.

Theorem handoff_trace_source_split ge cell P first count last events target path arguments environment :
  store_path ge P first count last -> entry_handoff_steps ge cell(live first)events target ->
  In(entry_image path arguments environment)events ->
  exists prefix rest,
    events=prefix++rest /\ handoff_flags_projection prefix=[] /\
    entry_handoff_steps ge cell(live first)prefix(live last) /\
    entry_handoff_steps ge cell(live last)rest target /\ In(entry_image path arguments environment)rest.
Proof.
  intros SCRIPT RUN IMAGE.
  destruct(handoff_entry_path_decomposition _ _ _ _ _ _ SCRIPT _ _ RUN)
    as[[rest EVENTS]|[[used[current[remaining[COUNT[EVENTS[END TAIL]]]]]]|[used[m[COUNT[EVENTS[END MEMORY]]]]]]].
  - destruct EVENTS as[EVENTS REST]. exists(repeat handoff_source_event count),rest;split;[exact EVENTS|].
    split;[apply handoff_flags_projection_source|]. split.
    + pose proof(entry_original_steps_preserved ge cell _ _ _ (store_path_actual ge cell _ _ _ _ SCRIPT))as PREFIX.
      rewrite map_repeat in PREFIX;exact PREFIX.
    + split;[exact REST|]. rewrite EVENTS,in_app_iff in IMAGE;destruct IMAGE as[IMPOSSIBLE|IMAGE];[exfalso;apply(handoff_source_has_no_image _ _ _ _ IMPOSSIBLE)|exact IMAGE].
  - subst events;exfalso;exact(handoff_source_has_no_image _ _ _ _ IMAGE).
  - subst events;rewrite in_app_iff in IMAGE;destruct IMAGE as[IMPOSSIBLE|[IMPOSSIBLE|IMPOSSIBLE]];
      [exact(False_rect _ (handoff_source_has_no_image _ _ _ _ IMPOSSIBLE))|discriminate|contradiction].
Qed.

Theorem handoff_trace_format_returns ge cell output offset value k before events target path arguments environment :
  entry_handoff_steps ge cell(live(Callstate entry_decimal_definition[Vptr output offset;Vlong value]k before))events target ->
  In(entry_image path arguments environment)events ->
  exists returned after prefix rest,
    events=prefix++rest /\ handoff_flags_projection prefix=[] /\
    entry_handoff_steps ge cell(live(Callstate entry_decimal_definition[Vptr output offset;Vlong value]k before))prefix
      (live(Returnstate(Vint returned)k after)) /\
    entry_format_result cell before output offset returned after /\
    entry_handoff_steps ge cell(live(Returnstate(Vint returned)k after))rest target /\
    In(entry_image path arguments environment)rest.
Proof.
  intros RUN;remember(live(Callstate entry_decimal_definition[Vptr output offset;Vlong value]k before))as initial eqn:INITIAL.
  revert before k INITIAL;induction RUN as[initial|initial event middle events target STEP RUN IH];
    intros before k INITIAL IMAGE;subst initial;[contradiction|].
  destruct(handoff_format_cases _ _ _ _ _ _ _ _ _ STEP)
    as[[returned[after[OWN[RESULT[EVENT TARGET]]]]]|[[EVENT TARGET]|[[after[PARTIAL[EVENT TARGET]]]|[EVENT TARGET]]]];subst event middle.
  - cbn in IMAGE;destruct IMAGE as[IMPOSSIBLE|IMAGE];[discriminate|].
    exists returned,after,[entry_formatted output offset value returned],events;split;[reflexivity|]. split;[reflexivity|].
    split;[econstructor;[exact STEP|constructor]|]. split;[exact RESULT|]. split;assumption.
  - cbn in IMAGE;destruct IMAGE as[IMPOSSIBLE|IMAGE];[discriminate|].
    destruct(IH before k eq_refl IMAGE)as[returned[after[prefix[rest[EVENTS[FLAGS[PREFIX[RESULT[REST IMAGE']]]]]]]]].
    exists returned,after,(entry_primitive_wait::prefix),rest;split;[cbn;rewrite EVENTS;reflexivity|].
    split;[exact FLAGS|]. split;[econstructor;eassumption|]. split;[exact RESULT|]. split;assumption.
  - destruct(entry_handoff_dead_steps _ _ _ _ _ RUN)as[EVENTS END];subst events;cbn in IMAGE;intuition discriminate.
  - destruct(entry_handoff_dead_steps _ _ _ _ _ RUN)as[EVENTS END];subst events;cbn in IMAGE;intuition discriminate.
Qed.

Theorem handoff_trace_flags_returns ge cell descriptor flags k before events target path arguments environment :
  entry_handoff_steps ge cell(live(Callstate entry_flags_definition[Vint descriptor;Vint flags]k before))events target ->
  In(entry_image path arguments environment)events ->
  exists returned after prefix rest,
    events=prefix++rest /\ handoff_flags_projection prefix=[handoff_flag_event descriptor flags returned] /\
    entry_handoff_steps ge cell(live(Callstate entry_flags_definition[Vint descriptor;Vint flags]k before))prefix
      (live(Returnstate(Vint returned)k after)) /\
    entry_errno_frame cell before after /\ entry_errno_ready cell after /\
    entry_handoff_steps ge cell(live(Returnstate(Vint returned)k after))rest target /\
    In(entry_image path arguments environment)rest.
Proof.
  intros RUN;remember(live(Callstate entry_flags_definition[Vint descriptor;Vint flags]k before))as initial eqn:INITIAL.
  revert before k INITIAL;induction RUN as[initial|initial event middle events target STEP RUN IH];
    intros before k INITIAL IMAGE;subst initial;[contradiction|].
  destruct(handoff_flags_cases _ _ _ _ _ _ _ _ STEP)
    as[[returned[after[FRAME[READY[EVENT TARGET]]]]]|[[EVENT TARGET]|[[after[PARTIAL[EVENT TARGET]]]|[EVENT TARGET]]]];subst event middle.
  - cbn in IMAGE;destruct IMAGE as[IMPOSSIBLE|IMAGE];[discriminate|].
    exists returned,after,[entry_flags_returned descriptor flags returned],events;split;[reflexivity|]. split;[reflexivity|].
    split;[econstructor;[exact STEP|constructor]|]. split;[exact FRAME|]. split;[exact READY|]. split;assumption.
  - cbn in IMAGE;destruct IMAGE as[IMPOSSIBLE|IMAGE];[discriminate|].
    destruct(IH before k eq_refl IMAGE)as[returned[after[prefix[rest[EVENTS[FLAGS[PREFIX[FRAME[READY[REST IMAGE']]]]]]]]]].
    exists returned,after,(entry_primitive_wait::prefix),rest;split;[cbn;rewrite EVENTS;reflexivity|].
    split;[exact FLAGS|]. split;[econstructor;eassumption|]. split;[exact FRAME|]. split;[exact READY|]. split;assumption.
  - destruct(entry_handoff_dead_steps _ _ _ _ _ RUN)as[EVENTS END];subst events;cbn in IMAGE;intuition discriminate.
  - destruct(entry_handoff_dead_steps _ _ _ _ _ RUN)as[EVENTS END];subst events;cbn in IMAGE;intuition discriminate.
Qed.

Theorem handoff_trace_strcmp_returns ge cell left right bytes k before events target path arguments environment :
  c_string before left bytes -> c_string before right bytes ->
  entry_handoff_steps ge cell(live(Callstate strcmp_definition[address_value left;address_value right]k before))events target ->
  In(entry_image path arguments environment)events ->
  exists prefix rest,
    events=prefix++rest /\ handoff_flags_projection prefix=[] /\
    entry_handoff_steps ge cell(live(Callstate strcmp_definition[address_value left;address_value right]k before))prefix
      (live(Returnstate(Vint Int.zero)k before)) /\
    entry_handoff_steps ge cell(live(Returnstate(Vint Int.zero)k before))rest target /\
    In(entry_image path arguments environment)rest.
Proof.
  intros LEFT RIGHT RUN;remember(live(Callstate strcmp_definition[address_value left;address_value right]k before))as initial eqn:INITIAL.
  revert k INITIAL;induction RUN as[initial|initial event middle events target STEP RUN IH];
    intros k INITIAL IMAGE;subst initial;[contradiction|].
  destruct(handoff_strcmp_cases _ _ _ _ _ _ _ _ _ _ LEFT RIGHT STEP)
    as[[value[RESULT[EVENT TARGET]]]|[[EVENT TARGET]|[EVENT TARGET]]];subst event middle.
  - assert(ZERO:Int.eq value Int.zero=true).
    { apply(proj2(strcmp_zero_iff _ _ _ _ _ _ LEFT RIGHT RESULT));reflexivity. }
    apply Int.same_if_eq in ZERO;subst value.
    cbn in IMAGE;destruct IMAGE as[IMPOSSIBLE|IMAGE];[discriminate|].
    exists[entry_library(strcmp_returned left right Int.zero)],events;split;[reflexivity|]. split;[reflexivity|].
    split;[econstructor;[exact STEP|constructor]|]. split;assumption.
  - cbn in IMAGE;destruct IMAGE as[IMPOSSIBLE|IMAGE];[discriminate|].
    destruct(IH k eq_refl IMAGE)as[prefix[rest[EVENTS[FLAGS[PREFIX[REST IMAGE']]]]]].
    exists(entry_library library_wait::prefix),rest;split;[cbn;rewrite EVENTS;reflexivity|].
    split;[exact FLAGS|]. split;[econstructor;eassumption|]. split;assumption.
  - destruct(entry_handoff_dead_steps _ _ _ _ _ RUN)as[EVENTS END];subst events;cbn in IMAGE;intuition discriminate.
Qed.

Definition handoff_trace_cut ge cell (R:Clight.state->Prop) wanted first events target path arguments environment :=
  exists prefix last rest,
    events=prefix++rest /\ handoff_flags_projection prefix=wanted /\
    entry_handoff_steps ge cell(live first)prefix(live last) /\ R last /\
    entry_handoff_steps ge cell(live last)rest target /\ In(entry_image path arguments environment)rest.

Lemma handoff_trace_steps_trans ge cell first events middle rest last :
  entry_handoff_steps ge cell first events middle -> entry_handoff_steps ge cell middle rest last ->
  entry_handoff_steps ge cell first(events++rest)last.
Proof. intros FIRST SECOND;induction FIRST;cbn;[exact SECOND|econstructor;eauto]. Qed.

Lemma handoff_trace_cut_join ge cell R before_flags after_flags first middle prefix rest events target path arguments environment :
  events=prefix++rest -> handoff_flags_projection prefix=before_flags ->
  entry_handoff_steps ge cell(live first)prefix(live middle) ->
  handoff_trace_cut ge cell R after_flags middle rest target path arguments environment ->
  handoff_trace_cut ge cell R(before_flags++after_flags)first events target path arguments environment.
Proof.
  intros EVENTS FLAGS PREFIX[prefix2[last[rest2[EVENTS2[FLAGS2[PREFIX2[RESULT[REST IMAGE]]]]]]]].
  exists(prefix++prefix2),last,rest2;split;[rewrite EVENTS,EVENTS2,app_assoc;reflexivity|].
  split;[rewrite handoff_flags_projection_app,FLAGS,FLAGS2;reflexivity|].
  split;[eapply handoff_trace_steps_trans;eassumption|]. split;[exact RESULT|]. split;assumption.
Qed.

Lemma handoff_trace_cut_here ge cell R first events target path arguments environment :
  R first -> entry_handoff_steps ge cell(live first)events target -> In(entry_image path arguments environment)events ->
  handoff_trace_cut ge cell R [] first events target path arguments environment.
Proof. intros RESULT RUN IMAGE;exists [],first,events;split;[reflexivity|]. split;[reflexivity|]. split;[constructor|]. split;[exact RESULT|]. split;assumption. Qed.

Theorem handoff_trace_cut_source ge cell P R wanted first count middle events target path arguments environment :
  store_path ge P first count middle -> entry_handoff_steps ge cell(live first)events target ->
  In(entry_image path arguments environment)events ->
  (forall rest,entry_handoff_steps ge cell(live middle)rest target -> In(entry_image path arguments environment)rest ->
    handoff_trace_cut ge cell R wanted middle rest target path arguments environment) ->
  handoff_trace_cut ge cell R wanted first events target path arguments environment.
Proof.
  intros SCRIPT RUN IMAGE NEXT.
  destruct(handoff_trace_source_split _ _ _ _ _ _ _ _ _ _ _ SCRIPT RUN IMAGE)
    as[prefix[rest[EVENTS[FLAGS[PREFIX[REST AFTER]]]]]].
  change(handoff_trace_cut ge cell R([]++wanted)first events target path arguments environment).
  eapply handoff_trace_cut_join;[exact EVENTS|exact FLAGS|exact PREFIX|apply NEXT;assumption].
Qed.

Theorem handoff_trace_cut_format ge cell R wanted output offset value k before events target path arguments environment :
  entry_handoff_steps ge cell(live(Callstate entry_decimal_definition[Vptr output offset;Vlong value]k before))events target ->
  In(entry_image path arguments environment)events ->
  (forall returned after rest,entry_format_result cell before output offset returned after ->
    entry_handoff_steps ge cell(live(Returnstate(Vint returned)k after))rest target ->
    In(entry_image path arguments environment)rest ->
    handoff_trace_cut ge cell R wanted(Returnstate(Vint returned)k after)rest target path arguments environment) ->
  handoff_trace_cut ge cell R wanted(Callstate entry_decimal_definition[Vptr output offset;Vlong value]k before)
    events target path arguments environment.
Proof.
  intros RUN IMAGE NEXT.
  destruct(handoff_trace_format_returns _ _ _ _ _ _ _ _ _ _ _ _ RUN IMAGE)
    as[returned[after[prefix[rest[EVENTS[FLAGS[PREFIX[RESULT[REST AFTER]]]]]]]]].
  change(handoff_trace_cut ge cell R([]++wanted)(Callstate entry_decimal_definition[Vptr output offset;Vlong value]k before)
    events target path arguments environment).
  eapply handoff_trace_cut_join;[exact EVENTS|exact FLAGS|exact PREFIX|apply NEXT;assumption].
Qed.

Theorem handoff_trace_cut_flags ge cell R tail descriptor flags k before events target path arguments environment :
  entry_handoff_steps ge cell(live(Callstate entry_flags_definition[Vint descriptor;Vint flags]k before))events target ->
  In(entry_image path arguments environment)events ->
  (forall returned after rest,entry_errno_frame cell before after ->entry_errno_ready cell after ->
    entry_handoff_steps ge cell(live(Returnstate(Vint returned)k after))rest target ->
    In(entry_image path arguments environment)rest ->
    returned=Int.zero /\ handoff_trace_cut ge cell R tail(Returnstate(Vint returned)k after)rest target path arguments environment) ->
  handoff_trace_cut ge cell R(handoff_flag_event descriptor flags Int.zero::tail)
    (Callstate entry_flags_definition[Vint descriptor;Vint flags]k before)events target path arguments environment.
Proof.
  intros RUN IMAGE NEXT.
  destruct(handoff_trace_flags_returns _ _ _ _ _ _ _ _ _ _ _ RUN IMAGE)
    as[returned[after[prefix[rest[EVENTS[FLAGS[PREFIX[FRAME[READY[REST AFTER]]]]]]]]]].
  destruct(NEXT returned after rest FRAME READY REST AFTER)as[ZERO TAIL];subst returned.
  change(handoff_trace_cut ge cell R([handoff_flag_event descriptor flags Int.zero]++tail)
    (Callstate entry_flags_definition[Vint descriptor;Vint flags]k before)events target path arguments environment).
  eapply handoff_trace_cut_join;eassumption.
Qed.

Theorem handoff_trace_cut_strcmp ge cell R wanted left right bytes k before events target path arguments environment :
  c_string before left bytes ->c_string before right bytes ->
  entry_handoff_steps ge cell(live(Callstate strcmp_definition[address_value left;address_value right]k before))events target ->
  In(entry_image path arguments environment)events ->
  (forall rest,entry_handoff_steps ge cell(live(Returnstate(Vint Int.zero)k before))rest target ->
    In(entry_image path arguments environment)rest ->
    handoff_trace_cut ge cell R wanted(Returnstate(Vint Int.zero)k before)rest target path arguments environment) ->
  handoff_trace_cut ge cell R wanted(Callstate strcmp_definition[address_value left;address_value right]k before)
    events target path arguments environment.
Proof.
  intros LEFT RIGHT RUN IMAGE NEXT.
  destruct(handoff_trace_strcmp_returns _ _ _ _ _ _ _ _ _ _ _ _ LEFT RIGHT RUN IMAGE)
    as[prefix[rest[EVENTS[FLAGS[PREFIX[REST AFTER]]]]]].
  change(handoff_trace_cut ge cell R([]++wanted)(Callstate strcmp_definition[address_value left;address_value right]k before)
    events target path arguments environment).
  eapply handoff_trace_cut_join;[exact EVENTS|exact FLAGS|exact PREFIX|apply NEXT;assumption].
Qed.

Definition handoff_trace_spec ge cell R wanted first := forall events target path arguments environment,
  entry_handoff_steps ge cell(live first)events target -> In(entry_image path arguments environment)events ->
  handoff_trace_cut ge cell R wanted first events target path arguments environment.
Lemma handoff_trace_spec_source ge cell P R wanted first count middle :
  store_path ge P first count middle -> handoff_trace_spec ge cell R wanted middle ->
  handoff_trace_spec ge cell R wanted first.
Proof. intros SCRIPT NEXT events target path arguments environment RUN IMAGE;eapply handoff_trace_cut_source;eauto. Qed.
Lemma handoff_trace_spec_edge ge cell R wanted first middle :
  store_edge ge first middle -> handoff_trace_spec ge cell R wanted middle ->
  handoff_trace_spec ge cell R wanted first.
Proof.
  intros EDGE NEXT;eapply handoff_trace_spec_source with(P:=fun _=>True);[|exact NEXT].
  econstructor;[exact I|exact EDGE|constructor;exact I].
Qed.
Lemma handoff_trace_spec_here ge cell R first : R first -> handoff_trace_spec ge cell R [] first.
Proof. intros RESULT events target path arguments environment RUN IMAGE;apply handoff_trace_cut_here;assumption. Qed.
Lemma handoff_trace_spec_format ge cell R wanted output offset value k before :
  (forall returned after,entry_format_result cell before output offset returned after ->
    handoff_trace_spec ge cell R wanted(Returnstate(Vint returned)k after)) ->
  handoff_trace_spec ge cell R wanted(Callstate entry_decimal_definition[Vptr output offset;Vlong value]k before).
Proof.
  intros NEXT events target path arguments environment RUN IMAGE.
  eapply handoff_trace_cut_format;[exact RUN|exact IMAGE|].
  intros returned after rest RESULT REST LATER;apply NEXT;assumption.
Qed.
Lemma handoff_trace_spec_strcmp ge cell R wanted left right bytes k before :
  c_string before left bytes -> c_string before right bytes ->
  handoff_trace_spec ge cell R wanted(Returnstate(Vint Int.zero)k before) ->
  handoff_trace_spec ge cell R wanted(Callstate strcmp_definition[address_value left;address_value right]k before).
Proof.
  intros LEFT RIGHT NEXT events target path arguments environment RUN IMAGE.
  eapply handoff_trace_cut_strcmp;[exact LEFT|exact RIGHT|exact RUN|exact IMAGE|].
  intros rest REST LATER;apply NEXT;assumption.
Qed.
