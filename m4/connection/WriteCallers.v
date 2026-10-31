(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-callers.continuation: Every caller run includes the actual write_all body. *)
From Coq Require Import List.
From compcert Require Import Coqlib Integers AST Values Memory Events Clight.
Require Import Slice IO Machine WriteMemory WriteAll WriteWitnesses LibraryMachine LibraryPreservation CallContexts.
Import ListNotations.

Definition write_call_initial q k m := plug_state (WriteAll.initial_state q m) k.
Definition write_return_post q input events value after :=
  write_owned q input after /\
  ((value = Vint Int.zero /\ emitted_trace events = input) \/
   (value = Vint Int.mone /\ failed_reply (fold_left last_update events None) /\
    emitted_trace events <> input)).

Theorem write_caller_decomposition : forall q input m k events target,
  write_owned q input m -> is_call_cont k ->
  library_steps (Clight.globalenv Slice.prog) (cell_of q)
    (live (write_call_initial q k m)) events target ->
  (exists original local_target,
    events = map original_event original /\ target = plug_machine local_target k /\
    Machine.steps (Clight.globalenv Slice.prog) (cell_of q)
      (live (WriteAll.initial_state q m)) original local_target /\
    write_owned q input (machine_memory local_target) /\
    exists rest, input = emitted_trace original ++ rest) \/
  (exists before after value final,
    events = map original_event before ++ after /\
    write_return_post q input before value final /\
    Machine.steps (Clight.globalenv Slice.prog) (cell_of q)
      (live (WriteAll.initial_state q m)) before (live (Returnstate value Kstop final)) /\
    library_steps (Clight.globalenv Slice.prog) (cell_of q)
      (live (Returnstate value k final)) after target).
Proof.
  intros q input m k events target OWN CALL RUN.
  destruct (caller_run_decomposition _ _ _ _ _ _ CALL RUN)
    as [[local [LOCAL SAME]]|[before [after [value [final [ES [LOCAL TAIL]]]]]]].
  - destruct (write_all_library_projection _ _ _ _ _ OWN LOCAL) as [original [ES ORIGINAL]].
    pose proof (write_all_prefix_safety _ _ _ _ _ OWN ORIGINAL) as SAFE.
    left; exists original, local. split; [exact ES|]. split; [exact SAME|].
    split; [exact ORIGINAL|exact SAFE].
  - destruct (write_all_library_projection _ _ _ _ _ OWN LOCAL) as [original [BEFORE ORIGINAL]].
    pose proof (write_all_prefix_safety _ _ _ _ _ OWN ORIGINAL) as [PRESERVED _].
    pose proof (write_all_return_exact _ _ _ _ _ _ OWN ORIGINAL) as RETURN.
    right; exists original, after, value, final. subst before.
    split; [exact ES|]. split; [split; assumption|auto].
Qed.

Theorem write_caller_success : forall q input m k,
  write_owned q input m -> is_call_cont k ->
  exists original,
    library_steps (Clight.globalenv Slice.prog) (cell_of q)
      (live (write_call_initial q k m)) (map original_event original)
      (live (Returnstate (Vint Int.zero) k m)) /\ emitted_trace original = input.
Proof.
  intros q input m k OWN CALL.
  destruct (write_all_success_exists _ _ _ OWN) as [original [RUN BYTES]].
  exists original; split; [|exact BYTES].
  exact (plug_library_steps _ _ _ _ _ k CALL (original_runs_preserved _ _ _ _ _ RUN)).
Qed.

Theorem write_caller_error : forall q input m k error,
  write_owned q input m -> input <> [] -> is_call_cont k -> error <> Int.repr 4 ->
  exists original after,
    library_steps (Clight.globalenv Slice.prog) (cell_of q)
      (live (write_call_initial q k m)) (map original_event original)
      (live (Returnstate (Vint Int.mone) k after)) /\ replies original = [failure error].
Proof.
  intros q input m k error OWN NE CALL ERROR.
  destruct (source_error_return _ _ _ _ OWN NE ERROR) as [original [after [RUN REPLIES]]].
  exists original, after; split; [|exact REPLIES].
  exact (plug_library_steps _ _ _ _ _ k CALL (original_runs_preserved _ _ _ _ _ RUN)).
Qed.

Theorem write_caller_partial_loss : forall n q first rest m k,
  write_owned q (first ++ rest) m -> first <> [] -> is_call_cont k ->
  exists original,
    library_steps (Clight.globalenv Slice.prog) (cell_of q)
      (live (write_call_initial q k m)) (map original_event original) (dead m) /\
    emitted_trace original = first /\ replies original = [] /\
    exists before, original = repeat (source_step E0) before ++
      (repeat wait_step n ++ [partial_loss (suffix q 0) first None]).
Proof.
  intros n q first rest m k OWN FIRST CALL.
  destruct (source_wait_then_partial_loss n q first rest m OWN FIRST) as [original [RUN FACTS]].
  exists original; split; [|exact FACTS].
  exact (plug_library_steps _ _ _ _ _ k CALL (original_runs_preserved _ _ _ _ _ RUN)).
Qed.
