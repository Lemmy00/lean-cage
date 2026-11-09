(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Successful outer returns must traverse actual callee and source frontiers. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps CallContexts LibraryMachine.
From EntryNative Require Import NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessContexts ProcessPaths ProcessPrimitiveCases.
Import ListNotations.
Open Scope Z_scope.

Lemma process_plug_cont_nonstop k suffix : suffix<>Kstop ->plug_cont k suffix<>Kstop.
Proof. destruct k;cbn;congruence. Qed.

Lemma process_plug_not_closed_return state suffix value memory : suffix<>Kstop ->
  plug_machine state suffix<>live(Returnstate value Kstop memory).
Proof.
  intro NONSTOP;destruct state as[state|m];[destruct state;cbn|discriminate];try discriminate.
  intro SAME;inversion SAME.
  eapply process_plug_cont_nonstop;[exact NONSTOP|eassumption].
Qed.

Theorem process_callee_return_decomposition ge cell definition arguments suffix before events value after :
  process_steps ge cell(live(Callstate definition arguments suffix before))events
    (live(Returnstate value Kstop after)) ->
  is_call_cont suffix ->suffix<>Kstop ->
  exists prefix rest returned memory,events=prefix++rest /\
    process_steps ge cell(live(Callstate definition arguments Kstop before))prefix
      (live(Returnstate returned Kstop memory)) /\
    process_steps ge cell(live(Returnstate returned suffix memory))rest
      (live(Returnstate value Kstop after)).
Proof.
  intros RUN CALL NONSTOP.
  destruct(process_caller_run_decomposition ge cell suffix(Callstate definition arguments Kstop before)
    events(live(Returnstate value Kstop after))CALL RUN)
    as[[local[LOCAL SAME]]|[prefix[rest[returned[memory[EVENTS[LOCAL CONTINUE]]]]]]].
  - exfalso;eapply process_plug_not_closed_return;[exact NONSTOP|symmetry;exact SAME].
  - exists prefix,rest,returned,memory;auto.
Qed.

Lemma process_store_path_closed_return ge(P:mem->Prop)value memory count last :
  store_path ge P(Returnstate value Kstop memory)count last ->
  count=0%nat /\last=Returnstate value Kstop memory.
Proof.
  intro PATH;inversion PATH;subst;[auto|].
  match goal with EDGE:store_edge _ _ _|-_=>destruct EDGE as[_[SOURCE _]];inversion SOURCE end.
Qed.

Theorem process_source_frontier_reached ge cell(P:mem->Prop)start count last events value after :
  store_path ge P start count last ->
  (forall returned memory,last<>Returnstate returned Kstop memory) ->
  process_steps ge cell(live start)events(live(Returnstate value Kstop after)) ->
  exists rest,events=repeat process_source_event count++rest /\
    process_steps ge cell(live last)rest(live(Returnstate value Kstop after)).
Proof.
  intros PATH NOTRETURN RUN.
  destruct(process_store_path_decomposition _ _ _ _ _ _ PATH _ _ RUN)
    as[REACHED|[[used[current[remaining[COUNT[EVENTS[TARGET TAIL]]]]]]|
      [used[memory[COUNT[EVENTS[TARGET PRESERVED]]]]]]];[exact REACHED| |discriminate].
  inversion TARGET;subst current.
  destruct(process_store_path_closed_return _ _ _ _ _ _ TAIL)as[ZERO SAME].
  exfalso;eapply NOTRETURN;exact SAME.
Qed.

Theorem process_terminal_run_constant ge cell before_value before events after_value after :
  process_steps ge cell(live(Returnstate before_value Kstop before))events
    (live(Returnstate after_value Kstop after)) ->
  events=[] /\after_value=before_value /\after=before.
Proof.
  intro RUN;inversion RUN;subst;[auto|].
  match goal with STEP:process_step _ _ _ _ _|-_=>
    destruct(process_stopped_return_only_loss _ _ _ _ _ _ STEP)as[EVENT TARGET]end.
  subst middle.
  match goal with TAIL:process_steps _ _ (dead _) _ _|-_=>
    destruct(process_dead_steps _ _ _ _ _ TAIL)as[EVENTS IMPOSSIBLE];discriminate end.
Qed.

Theorem process_source_return_exact ge cell(P:mem->Prop)start count value memory events actual after:
  store_path ge P start count(Returnstate value Kstop memory) ->
  process_steps ge cell(live start)events(live(Returnstate actual Kstop after)) ->
  actual=value /\after=memory.
Proof.
  intros PATH RUN.
  destruct(process_store_path_decomposition _ _ _ _ _ _ PATH _ _ RUN)
    as[[rest[EVENTS TAIL]]|[[used[current[remaining[COUNT[EVENTS[TARGET TAIL]]]]]]|
      [used[dead_memory[COUNT[EVENTS[TARGET PRESERVED]]]]]]];[| |discriminate].
  - destruct(process_terminal_run_constant _ _ _ _ _ _ _ TAIL)as[_ FACTS];exact FACTS.
  - inversion TARGET;subst current.
    destruct(process_store_path_closed_return _ _ _ _ _ _ TAIL)as[ZERO SAME];inversion SAME;auto.
Qed.

Theorem process_ptrace_return_decomposition ge cell before request child address data k events value after :
  process_steps ge cell
    (live(Callstate process_ptrace_definition[Vint request;Vint child;address;data]k before))events
    (live(Returnstate value Kstop after)) ->
  exists waiting returned memory rest,
    events=repeat process_waiting waiting++process_traced request child address data returned::rest /\
    process_ptrace_frame cell request data before memory /\entry_errno_ready cell memory /\
    process_steps ge cell(live(Returnstate(Vlong returned)k memory))rest
      (live(Returnstate value Kstop after)).
Proof.
  remember(live(Callstate process_ptrace_definition[Vint request;Vint child;address;data]k before))as initial eqn:INITIAL.
  remember(live(Returnstate value Kstop after))as final eqn:FINAL.
  intro RUN;revert before INITIAL FINAL.
  induction RUN as[state|first event middle rest last STEP RUN IH];intros before INITIAL FINAL;[congruence|].
  subst first last.
  destruct(process_ptrace_cases _ _ _ _ _ _ _ _ _ _ STEP)
    as[[returned[memory[FRAME[READY[EVENT TARGET]]]]]|[[EVENT TARGET]|
      [[EVENT TARGET]|[memory[EVENT[PARTIAL TARGET]]]]]];subst.
  - exists 0%nat,returned,memory,rest;cbn;auto.
  - destruct(IH before eq_refl eq_refl)as[waiting[returned[memory[tail[EVENTS[FRAME[READY CONTINUE]]]]]]].
    exists(S waiting),returned,memory,tail;cbn;split;[congruence|auto].
  - destruct(process_dead_steps _ _ _ _ _ RUN)as[EVENTS IMPOSSIBLE];discriminate.
  - destruct(process_dead_steps _ _ _ _ _ RUN)as[EVENTS IMPOSSIBLE];discriminate.
Qed.

Theorem process_negative_return_step ge cell fn k e le before event target :
  fn_return fn=tint ->call_cont k=Kstop ->
  process_step ge cell(live(State fn
    (Sreturn(Some(Eunop Oneg(Econst_int Int.one tint)tint)))k e le before))event target ->
  (event=process_source_event /\exists after,target=live(Returnstate(Vint Int.mone)Kstop after)) \/
  (event=process_entry(entry_library(original_event loss_step)) /\target=dead before).
Proof.
  intros RETURN CLOSED STEP.
  assert(INTERNAL:internal_state(State fn
    (Sreturn(Some(Eunop Oneg(Econst_int Int.one tint)tint)))k e le before))by exact I.
  destruct(process_internal_step_exact _ _ _ _ _ INTERNAL STEP)as[original[EVENT REAL]].
  subst event;inversion REAL;subst;try contradiction;
    try match goal with BOUND:boundary _ _ _|-_=>inversion BOUND end;auto.
  match goal with SOURCE:step2 _ _ _ _|-_=>inversion SOURCE;subst end.
  all:try solve[match goal with IMPOSSIBLE:_=_\/_=_|-_=>destruct IMPOSSIBLE;discriminate end].
  assert(EVALUATED:evaluated ge e le before(Eunop Oneg(Econst_int Int.one tint)tint)(Vint Int.mone)).
  { eapply value_unary;[apply value_int|reflexivity]. }
  match goal with VALUE:eval_expr _ _ _ _ _ _|-_=>
    pose proof(evaluated_unique _ _ _ _ _ _ EVALUATED _ VALUE)as SAME;subst end.
  match goal with CAST:sem_cast _ _ _ _=_|-_=>rewrite RETURN in CAST;cbn in CAST;inversion CAST;subst end.
  left;split;[reflexivity|]. rewrite CLOSED;eauto.
Qed.

Theorem process_negative_return_cannot_zero ge cell fn k e le before events after :
  fn_return fn=tint ->call_cont k=Kstop ->
  ~process_steps ge cell(live(State fn
    (Sreturn(Some(Eunop Oneg(Econst_int Int.one tint)tint)))k e le before))events
    (live(Returnstate(Vint Int.zero)Kstop after)).
Proof.
  intros RETURN CLOSED RUN;inversion RUN;subst;try discriminate.
  match goal with STEP:process_step _ _ _ _ _|-_=>
    destruct(process_negative_return_step _ _ _ _ _ _ _ _ _ RETURN CLOSED STEP)
      as[[EVENT[memory TARGET]]|[EVENT TARGET]]end;subst middle.
  - match goal with TAIL:process_steps _ _ _ _ _|-_=>
      destruct(process_terminal_run_constant _ _ _ _ _ _ _ TAIL)as[_[VALUE _]]end;discriminate.
  - match goal with TAIL:process_steps _ _ (dead _) _ _|-_=>
      destruct(process_dead_steps _ _ _ _ _ TAIL)as[_ IMPOSSIBLE]end;discriminate.
Qed.
