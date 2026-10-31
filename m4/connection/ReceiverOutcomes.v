(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-receiver.reads: Whole-receiver classification uses the actual read trace, bounded by nine bytes. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Clight.
Require Import Slice Machine StoreSteps CallPaths LibraryMachine ResultLayout ReceiverSource
  ReceiverReadMemory ReceiverRouting ReceiverReadStep ReceiverInput ReceiverEntry
  ReceiverChoice ReceiverConstruction ReceiverTrace ReceiverLoopTrace.
Import ListNotations.
Open Scope Z_scope.
Theorem receiver_return_trace_exact : forall cell base output ofs fd bad entered done status run uid events value after,
  receiver_input cell base output ofs run uid ->
  library_steps result_ge cell(live(receiver_initial output ofs fd bad entered done status Kstop base))events
    (live(Returnstate value Kstop after)) ->
  exists b allocated reason,receiver_allocations base b allocated /\
    receiver_stop_valid reason(receiver_read_trace events) /\
    receiver_choice_result output ofs
      (receiver_select(receiver_read_trace events)(receiver_bad bad reason)entered done status)uid run b value after.
Proof.
  intros cell base output ofs fd bad entered done status run uid events value after INPUT RUN.
  destruct(receiver_entry_prepared cell base output ofs fd bad entered done status run uid INPUT)
    as[b[allocated[initialized[count[ALLOC[PATH[LIVE[BUFFER REGS]]]]]]]].
  destruct(source_path_caller_prefix _ _ _ _ _ _ PATH _ _ RUN)
    as[[n[s[remaining[COUNT[ES[TARGET TAIL]]]]]]|[[n[m[BOUND[ES[TARGET GOOD]]]]]|[rest[ES AFTER]]]].
  - inversion TARGET;subst s;destruct(store_return_path _ _ _ _ _ _ TAIL)as[N EQ];discriminate EQ.
  - discriminate TARGET.
  - assert(ROUTED : receiver_routed cell b fd(receiver_temps output ofs fd bad entered done status)bad Kstop
      (receiver_live_memory cell base b output ofs fd)[]
      (receiver_loop_state b(receiver_first_temps output ofs fd bad entered done status)Kstop initialized)).
    { eapply receiver_loop_routed;[exact LIVE|exact(proj2(proj2(proj2 LIVE)))|exact BUFFER|exact REGS]. }
    destruct(receiver_loop_exact_trace cell base b output ofs fd bad entered done status run uid _ _ _ _ INPUT ROUTED AFTER)
      as[reason[STOP POST]].
    exists b,allocated,reason;split;[exact ALLOC|].
    rewrite ES,receiver_read_trace_app,receiver_read_trace_source;exact(conj STOP POST).
Qed.
Theorem receiver_read_nine_byte_bound : forall cell base output ofs fd bad entered done status run uid events target,
  receiver_input cell base output ofs run uid ->
  library_steps result_ge cell(live(receiver_initial output ofs fd bad entered done status Kstop base))events target ->
  (length(receiver_read_trace events)<=9)%nat.
Proof.
  intros cell base output ofs fd bad entered done status run uid events target INPUT RUN.
  destruct(receiver_entry_prepared cell base output ofs fd bad entered done status run uid INPUT)
    as[b[allocated[initialized[count[ALLOC[PATH[LIVE[BUFFER REGS]]]]]]]].
  destruct(source_path_caller_prefix _ _ _ _ _ _ PATH _ _ RUN)
    as[[n[s[remaining[COUNT[ES[TARGET TAIL]]]]]]|[[n[m[BOUND[ES[TARGET GOOD]]]]]|[rest[ES AFTER]]]];subst events.
  - rewrite receiver_read_trace_source;cbn;lia.
  - rewrite receiver_read_trace_app,receiver_read_trace_source;cbn;lia.
  - rewrite receiver_read_trace_app,receiver_read_trace_source.
    eapply receiver_loop_read_bound;[exact INPUT| |exact AFTER].
    eapply receiver_loop_routed;[exact LIVE|exact(proj2(proj2(proj2 LIVE)))|exact BUFFER|exact REGS].
Qed.
