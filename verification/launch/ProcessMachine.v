(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.effects: Extend the actual source machine with one waitpid or ptrace operation. *)
From Stdlib Require Import ZArith List String.
From compcert Require Import Coqlib Integers AST Values Memory Memdata Events Ctypes Ctypesdefs Clight.
Require Import IO Machine ClightSteps StoreSteps ErrorNumber LibraryMachine.
From EntryNative Require Import NativeHandoffMachine.
Import ListNotations.
Open Scope Z_scope.

Definition process_wait_definition : Clight.fundef := External
  (EF_external "waitpid" (mksignature [Xint; Xptr; Xint] Xint cc_default))
  [tint; tptr tint; tint] tint cc_default.

Definition process_ptrace_definition : Clight.fundef := External
  (EF_external "entry_ptrace4" (mksignature [Xint; Xint; Xptr; Xptr] Xlong cc_default))
  [tint; tint; tptr tvoid; tptr tvoid] tlong cc_default.

(* §AR-entry.effects: The tail uses individual libc/kernel calls after release. *)
Definition process_kill_definition : Clight.fundef := External
  (EF_external "kill" (mksignature [Xint;Xint] Xint cc_default))
  [tint;tint] tint cc_default.
Definition process_sleep_definition : Clight.fundef := External
  (EF_external "usleep" (mksignature [Xint] Xint cc_default)) [tuint] tint cc_default.

Inductive process_aux_kind := auxiliary_kill | auxiliary_sleep.
Inductive process_aux_event :=
| auxiliary_returned (kind:process_aux_kind) (first second returned:int)
| auxiliary_lost (kind:process_aux_kind) (first second:int).

(* §AR-entry.caller.clock: One bounded runtime operation, with source-owned timespec storage. *)
Definition process_clock_definition : Clight.fundef := External
  (EF_external "clock_gettime"(mksignature[Xint;Xptr]Xint cc_default))
  [tint;tptr(Tstruct EntrySource._timespec noattr)]tint cc_default.

Inductive clock_observation := clock_failed(error:int) | clock_value(seconds nanos:int64).
Definition clock_return observation :=
  match observation with clock_failed _=>Int.mone|clock_value _ _=>Int.zero end.
Definition process_clock_partial cell output offset before after :=
  Mem.unchanged_on(entry_outside cell output(Ptrofs.unsigned offset)16)before after /\
  forall object position kind permission,
    Mem.perm after object position kind permission<->Mem.perm before object position kind permission.
Definition process_clock_owned before output offset :=
  Ptrofs.unsigned offset+16<=Ptrofs.modulus /\
  Mem.range_perm before output(Ptrofs.unsigned offset)(Ptrofs.unsigned offset+16)Cur Writable.
Inductive process_clock_effect cell output offset : mem->clock_observation->mem->Prop :=
| process_clock_failed_effect:forall before error after,
    1<=Int.signed error<=4095 ->process_clock_partial cell output offset before after ->
    initialized_errno cell after error ->process_clock_effect cell output offset before(clock_failed error)after
| process_clock_value_effect:forall before seconds nanos copied error after,
    Mem.storebytes before output(Ptrofs.unsigned offset)
      (encode_val Mint64(Vlong seconds)++encode_val Mint64(Vlong nanos))=Some copied ->
    errno_change
      {|operation:=reading;descriptor:=Int.zero;buffer_block:=output;buffer_offset:=Ptrofs.unsigned offset;
        requested:=16;errno_block:=tls_block cell;errno_offset:=tls_offset cell|}copied error after ->
    process_clock_effect cell output offset before(clock_value seconds nanos)after.

Inductive wait_observation :=
| wait_failed (error : int)
| wait_status (child status : int).

Definition wait_return (observation : wait_observation) : int :=
  match observation with wait_failed _ => Int.mone | wait_status child _ => child end.

(* The Linux process contract additionally identifies the returned task and
   whether its status is a stop or a reap. These source effects describe the
   exact bytes and errno memory, without treating a status label as ownership. *)
Inductive process_wait_effect (cell : tls) (status : block) (offset : Ptrofs.int)
    : mem -> wait_observation -> mem -> Prop :=
| process_wait_failed : forall before error after,
    1 <= Int.signed error <= 4095 ->
    Mem.store Mint32 before (tls_block cell) (tls_offset cell) (Vint error) = Some after ->
    process_wait_effect cell status offset before (wait_failed error) after
| process_wait_status : forall before child word written error after,
    1 <= Int.signed child <= Int.max_signed ->
    Mem.storev Mint32 before (Vptr status offset) (Vint word) = Some written ->
    errno_change
      {| operation := reading; descriptor := Int.zero; buffer_block := status;
         buffer_offset := Ptrofs.unsigned offset; requested := 4;
         errno_block := tls_block cell; errno_offset := tls_offset cell |}
      written error after ->
    process_wait_effect cell status offset before (wait_status child word) after.

Inductive process_event :=
| process_entry (event : entry_handoff_event)
| process_waited (requested : int) (status : block) (offset : Ptrofs.int)
    (options : int) (observation : wait_observation)
| process_traced (request child : int) (address data : val) (returned : int64)
| process_wait_lost (requested : int) (status : block) (offset : Ptrofs.int) (options : int)
| process_trace_lost (request child : int) (address data : val)
| process_waiting
| process_clocked(clock:int)(output:block)(offset:Ptrofs.int)(observation:clock_observation)
| process_clock_lost(clock:int)(output:block)(offset:Ptrofs.int)
| process_auxiliary(event:process_aux_event).

Definition process_ptrace_frame cell request data before after :=
  if Int.eq request (Int.repr 16898) then
    match data with
    | Vptr output offset => Mem.unchanged_on
        (entry_outside cell output (Ptrofs.unsigned offset) 128) before after
    | _ => entry_errno_frame cell before after
    end
  else entry_errno_frame cell before after.

Definition process_wait_partial cell status offset before after :=
  Mem.unchanged_on (entry_outside cell status (Ptrofs.unsigned offset) 4) before after /\
  forall object position kind permission,
    Mem.perm after object position kind permission <-> Mem.perm before object position kind permission.

Definition process_ptrace_partial cell request data before after :=
  process_ptrace_frame cell request data before after /\
  forall object position kind permission,
    Mem.perm after object position kind permission <-> Mem.perm before object position kind permission.

Inductive process_step ge cell : machine -> process_event -> machine -> Prop :=
| process_entry_step : forall before event after,
    entry_handoff_step ge cell before event after ->
    process_step ge cell before (process_entry event) after
| process_wait_step : forall before requested status offset options k observation after,
    process_wait_effect cell status offset before observation after ->
    entry_errno_ready cell after ->
    process_step ge cell
      (live (Callstate process_wait_definition
        [Vint requested; Vptr status offset; Vint options] k before))
      (process_waited requested status offset options observation)
      (live (Returnstate (Vint (wait_return observation)) k after))
| process_ptrace_step : forall before request child address data k returned after,
    process_ptrace_frame cell request data before after ->
    entry_errno_ready cell after ->
    process_step ge cell
      (live (Callstate process_ptrace_definition
        [Vint request; Vint child; address; data] k before))
      (process_traced request child address data returned)
      (live (Returnstate (Vlong returned) k after))
| process_wait_loss : forall before requested status offset options k after,
    process_wait_partial cell status offset before after ->
    process_step ge cell
      (live (Callstate process_wait_definition
        [Vint requested; Vptr status offset; Vint options] k before))
      (process_wait_lost requested status offset options) (dead after)
| process_ptrace_loss : forall before request child address data k after,
    process_ptrace_partial cell request data before after ->
    process_step ge cell
      (live (Callstate process_ptrace_definition
        [Vint request; Vint child; address; data] k before))
      (process_trace_lost request child address data) (dead after)
| process_wait_waiting : forall before requested status offset options k,
    process_step ge cell
      (live (Callstate process_wait_definition
        [Vint requested; Vptr status offset; Vint options] k before)) process_waiting
      (live (Callstate process_wait_definition
        [Vint requested; Vptr status offset; Vint options] k before))
| process_ptrace_waiting : forall before request child address data k,
    process_step ge cell
      (live (Callstate process_ptrace_definition
        [Vint request; Vint child; address; data] k before)) process_waiting
      (live (Callstate process_ptrace_definition
        [Vint request; Vint child; address; data] k before))
| process_clock_step:forall before clock output offset k observation after,
    process_clock_owned before output offset ->
    process_clock_effect cell output offset before observation after ->entry_errno_ready cell after ->
    process_step ge cell(live(Callstate process_clock_definition[Vint clock;Vptr output offset]k before))
      (process_clocked clock output offset observation)(live(Returnstate(Vint(clock_return observation))k after))
| process_clock_loss:forall before clock output offset k after,
    process_clock_owned before output offset ->process_clock_partial cell output offset before after ->
    process_step ge cell(live(Callstate process_clock_definition[Vint clock;Vptr output offset]k before))
      (process_clock_lost clock output offset)(dead after)
| process_clock_waiting:forall before clock output offset k,
    process_clock_owned before output offset ->
    process_step ge cell(live(Callstate process_clock_definition[Vint clock;Vptr output offset]k before))
      process_waiting(live(Callstate process_clock_definition[Vint clock;Vptr output offset]k before))
| process_kill_step:forall before pid signal k returned after,
    entry_errno_frame cell before after ->entry_errno_ready cell after ->
    process_step ge cell(live(Callstate process_kill_definition[Vint pid;Vint signal]k before))
      (process_auxiliary(auxiliary_returned auxiliary_kill pid signal returned))
      (live(Returnstate(Vint returned)k after))
| process_sleep_step:forall before micros k returned after,
    entry_errno_frame cell before after ->entry_errno_ready cell after ->
    process_step ge cell(live(Callstate process_sleep_definition[Vint micros]k before))
      (process_auxiliary(auxiliary_returned auxiliary_sleep micros Int.zero returned))
      (live(Returnstate(Vint returned)k after))
| process_kill_loss:forall before pid signal k after,
    entry_errno_partial cell before after ->
    process_step ge cell(live(Callstate process_kill_definition[Vint pid;Vint signal]k before))
      (process_auxiliary(auxiliary_lost auxiliary_kill pid signal))(dead after)
| process_sleep_loss:forall before micros k after,
    entry_errno_partial cell before after ->
    process_step ge cell(live(Callstate process_sleep_definition[Vint micros]k before))
      (process_auxiliary(auxiliary_lost auxiliary_sleep micros Int.zero))(dead after)
| process_kill_waiting:forall before pid signal k,
    process_step ge cell(live(Callstate process_kill_definition[Vint pid;Vint signal]k before))
      process_waiting(live(Callstate process_kill_definition[Vint pid;Vint signal]k before))
| process_sleep_waiting:forall before micros k,
    process_step ge cell(live(Callstate process_sleep_definition[Vint micros]k before))
      process_waiting(live(Callstate process_sleep_definition[Vint micros]k before)).

Inductive process_steps ge cell : machine -> list process_event -> machine -> Prop :=
| process_steps_nil : forall state, process_steps ge cell state [] state
| process_steps_cons : forall before event middle rest after,
    process_step ge cell before event middle -> process_steps ge cell middle rest after ->
    process_steps ge cell before (event :: rest) after.

Theorem process_loss_everywhere ge cell state :
  process_step ge cell (live state)
    (process_entry (entry_library (original_event loss_step))) (dead (memory_of state)).
Proof. constructor; apply entry_handoff_loss_everywhere. Qed.

Theorem process_dead_cannot_resume ge cell memory event after :
  ~ process_step ge cell (dead memory) event after.
Proof.
  intro STEP; inversion STEP; subst; eapply entry_handoff_dead_cannot_resume; eassumption.
Qed.

Theorem process_dead_steps ge cell memory events after :
  process_steps ge cell (dead memory) events after -> events = [] /\ after = dead memory.
Proof.
  intro RUN; inversion RUN; subst; auto.
  exfalso; eapply process_dead_cannot_resume; eassumption.
Qed.

Theorem process_entry_steps_preserved ge cell before events after :
  entry_handoff_steps ge cell before events after ->
  process_steps ge cell before (map process_entry events) after.
Proof.
  intro RUN; induction RUN; cbn; [constructor|].
  econstructor; [constructor; exact H|exact IHRUN].
Qed.

Theorem process_internal_step_exact ge cell state event after :
  internal_state state -> process_step ge cell (live state) event after ->
  exists original, event = process_entry (entry_library (original_event original)) /\
    Machine.step ge cell (live state) original after.
Proof.
  intros INTERNAL STEP; inversion STEP; subst; cbn in INTERNAL; try contradiction.
  destruct (entry_internal_step_exact _ _ _ _ _ INTERNAL H) as [original [EVENT REAL]].
  subst; eauto.
Qed.

Theorem process_store_edge_cases ge cell state next event after :
  store_edge ge state next -> process_step ge cell (live state) event after ->
  (event = process_entry (entry_library (original_event (source_step E0))) /\ after = live next) \/
  (event = process_entry (entry_library (original_event loss_step)) /\ after = dead (memory_of state)).
Proof.
  intros EDGE STEP.
  destruct (process_internal_step_exact _ _ _ _ _ (proj1 EDGE) STEP)
    as [original [EVENT REAL]]; subst.
  destruct (store_edge_cases _ _ _ _ _ _ EDGE REAL) as [[EVENT AFTER]|[EVENT AFTER]];
    subst; auto.
Qed.
