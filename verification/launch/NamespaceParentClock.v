(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.acceptance: A useful clock return retains its actual writable errno cell. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Clight.
Require Import IO Machine ErrorNumber LibraryMachine.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessAllocation ProcessPaths ProcessClock ProcessClockMemory
  ProcessClockRun ProcessCallee.
Import ListNotations.
Open Scope Z_scope.

Lemma namespace_clock_free_ready cell output memory after:
  output<>tls_block cell ->entry_errno_ready cell memory ->Mem.free memory output 0 16=Some after ->
  entry_errno_ready cell after.
Proof.
  intros SEPARATE[error[LOW[HIGH[[RANGE ALIGN]LOAD]]]]FREE.
  assert(FRAME:Mem.unchanged_on(fun object _=>object=tls_block cell)memory after).
  { eapply Mem.free_unchanged_on;[exact FREE|]. intros position BOUND SAME;congruence. }
  exists error;split;[exact LOW|]. split;[exact HIGH|]. split.
  - split;[intros position BOUND;eapply Mem.perm_unchanged_on;
      [exact FRAME|reflexivity|apply RANGE;exact BOUND]|exact ALIGN].
  - eapply Mem.load_unchanged_on;[exact FRAME|intros;reflexivity|exact LOAD].
Qed.

Theorem namespace_clock_actual_ready cell before events value after:
  Mem.valid_block before(tls_block cell) ->
  process_steps admission_ge cell(live(Callstate(Internal f_now_ms)[]Kstop before))events
    (live(Returnstate value Kstop after)) ->entry_errno_ready cell after.
Proof.
  intros VALID RUN;destruct(Mem.alloc before 0 16)as[allocated output]eqn:ALLOC.
  assert(FRESH:~Mem.valid_block before output)by(eapply Mem.fresh_block_alloc;exact ALLOC).
  assert(SEPARATE:output<>tls_block cell)by congruence.
  destruct(process_source_frontier_reached _ _ _ _ _ _ _ _ _
    (clock_start_to_call before allocated output Kstop ALLOC)ltac:(intros;discriminate)RUN)
    as[tail[EVENTS CONTINUE]].
  destruct(clock_return_decomposition _ _ _ _ _ _ _ _ _ _ CONTINUE)
    as[waiting[observation[memory[rest[ORDER[EFFECT[READY REST]]]]]]].
  assert(OWN:Mem.range_perm memory output 0 16 Cur Freeable).
  { intros position BOUND;apply(clock_effect_permissions _ _ _ _ _ _ EFFECT).
    eapply Mem.perm_alloc_2;[exact ALLOC|exact BOUND]. }
  destruct(clock_observation_source cell output allocated observation memory clock_temps Kstop
    SEPARATE EFFECT OWN)as[count[freed[BOUND[FREE PATH]]]].
  destruct(process_source_return_exact _ _ _ _ _ _ _ _ _ _ PATH REST)as[VALUE AFTER];subst after.
  eapply namespace_clock_free_ready;eassumption.
Qed.
