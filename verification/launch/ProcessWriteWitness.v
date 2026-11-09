(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.acceptance: A full bounded write has a useful actual source execution. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Clight.
Require Import IO Machine ClightSteps WriteMemory WriteAll LibraryMachine.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffBindings.
From EntryProcess Require Import ProcessMachine ProcessPaths ProcessCalls ProcessPlacement.
Import ListNotations.
Open Scope Z_scope.

Lemma process_clight_path_actual ge cell start finish : path ge start finish ->
  exists count,process_steps ge cell(live start)(repeat process_source_event count)(live finish).
Proof.
  intro PATH;induction PATH as[state|state next finish EDGE PATH[count RUN]].
  - exists 0%nat;constructor.
  - exists(S count);cbn; econstructor;[|exact RUN].
    apply process_entry_step,entry_library_step,original_step.
    destruct EDGE as[INTERNAL[STEP REST]];apply internal;assumption.
Qed.

Theorem current_write_useful_full_execution q input before :
  write_owned q input before -> input<>[] ->
  exists first last,
    process_steps(Clight.globalenv EntrySource.prog)(cell_of q)
      (live(Callstate(Internal EntrySource.f_write_all)
        [Vint(descriptor q);Vptr(buffer_block q)(Ptrofs.repr(buffer_offset q));
         Vlong(Int64.repr(requested q))]Kstop before))
      (repeat process_source_event first++placement_lift(io_step q(transfer input None))::
        repeat process_source_event last)
      (live(Returnstate(Vint Int.zero)Kstop before)).
Proof.
  intros OWN NONEMPTY;pose proof OWN as[OP[BUFFER[LENGTH LOAD]]].
  destruct BUFFER as[SIZE[OFFSET[WRAP[EO[EW[ACCESS[SEPARATE BYTES]]]]]]].
  assert(POSITIVE:0<Z.of_nat(length input)<=requested q).
  { destruct input;[contradiction|cbn in *;lia]. }
  destruct(initial_to_loop(Clight.globalenv EntrySource.prog)q before)as[le[REGISTERS INITIAL]].
  pose proof(loop_to_write(Clight.globalenv EntrySource.prog)q 0 le before
    current_write_symbols REGISTERS ltac:(lia))as CALL.
  assert(EFFECT:io_return q before(transfer input None)before).
  { apply write_returns;[exact(proj1(proj2 OWN))|exact OP|exact POSITIVE|rewrite LENGTH;exact LOAD|constructor]. }
  destruct(write_positive_to_loop(Clight.globalenv EntrySource.prog)q 0 le before input None REGISTERS
    ltac:(lia)ltac:(lia)ltac:(lia))as[next[REGISTERS' RETURN]].
  pose proof(loop_to_return(Clight.globalenv EntrySource.prog)q
    (0+Z.of_nat(length input))next before REGISTERS' ltac:(lia))as DONE.
  destruct(process_clight_path_actual _ (cell_of q)_ _(path_trans _ _ _ _ INITIAL CALL))as[first PREFIX].
  destruct(process_clight_path_actual _ (cell_of q)_ _(path_trans _ _ _ _ RETURN DONE))as[last SUFFIX].
  unfold write_state in PREFIX;rewrite placement_suffix_zero in PREFIX by exact OP.
  exists first,last;rewrite current_entry_write_all_exact.
  eapply process_steps_append;[exact PREFIX|].
  econstructor;[|exact SUFFIX].
  apply process_entry_step,entry_library_step,original_step.
  rewrite <-OP at 1;eapply effect with(q:=q)(r:=transfer input None);
    [constructor;reflexivity|exact EFFECT].
Qed.
