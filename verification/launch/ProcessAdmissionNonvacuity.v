(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.acceptance: The real loader and fresh TLS/status objects inhabit useful admission. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import IO Machine ErrorNumber WriteAll.
From EntryNative Require Import EntrySource NativeHandoffInputWitness.
From EntryProcess Require Import ProcessMachine ProcessAdmissionWitness.
Import ListNotations.
Open Scope Z_scope.

Theorem admission_actual_useful_input : exists initial cell before status,
  Genv.init_mem EntrySource.prog=Some initial /\
  initialized_errno cell before(Int.repr 5) /\
  Mem.valid_access before Mint32 status 0 Writable /\status<>tls_block cell.
Proof.
  destruct handoff_actual_initial_memory_exists as[initial INITIAL].
  destruct(Mem.alloc initial 0 4)as[allocated tls]eqn:TLS.
  assert(TLS_ACCESS:Mem.valid_access allocated Mint32 tls 0 Writable).
  { eapply Mem.valid_access_implies with(p1:=Freeable);[|constructor].
    eapply Mem.valid_access_alloc_same;[exact TLS|lia|cbn;lia|exists 0;reflexivity]. }
  destruct(Mem.valid_access_store _ _ _ _(Vint(Int.repr 5))TLS_ACCESS)as[written STORE].
  destruct(Mem.alloc written 0 4)as[before status]eqn:STATUS.
  set(cell:={|tls_block:=tls;tls_offset:=0|}).
  assert(SEPARATE:status<>tls).
  { intro SAME;subst status;eapply Mem.fresh_block_alloc;[exact STATUS|].
    eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;
      [eapply Mem.store_valid_access_1;[exact STORE|exact TLS_ACCESS]|constructor]. }
  exists initial,cell,before,status;split;[exact INITIAL|]. split.
  - unfold initialized_errno,cell;cbn[tls_block tls_offset].
    split;[lia|]. split;[change(4<=18446744073709551616);lia|]. split.
    + eapply Mem.valid_access_alloc_other;[exact STATUS|].
      eapply Mem.store_valid_access_1;eassumption.
    + eapply Mem.load_alloc_other;[exact STATUS|].
      erewrite Mem.load_store_same by exact STORE;reflexivity.
  - split.
    + eapply Mem.valid_access_implies with(p1:=Freeable);[|constructor].
      eapply Mem.valid_access_alloc_same;[exact STATUS|lia|cbn;lia|exists 0;reflexivity].
    + exact SEPARATE.
Qed.

Theorem admission_actual_source_useful cgroup : exists initial cell before status locals first second after,
  Genv.init_mem EntrySource.prog=Some initial /\
  initialized_errno cell before(Int.repr 5) /\
  Mem.valid_access before Mint32 status 0 Writable /\status<>tls_block cell /\
  process_steps(Clight.globalenv EntrySource.prog)cell
    (live(Callstate(Internal f_admit_child)[Vint(Int.repr 2);Vint cgroup;Vptr status Ptrofs.zero]Kstop before))
    (repeat ProcessPaths.process_source_event 5++
      process_waited(Int.repr 2)status Ptrofs.zero Int.zero(wait_status(Int.repr 2)(Int.repr 4991))::
      (repeat ProcessPaths.process_source_event 29++
        process_entry(NativeHandoffMachine.entry_formatted(ProcessAllocation.admission_text locals)
          Ptrofs.zero(Int64.repr 2)Int.one)::
        (repeat ProcessPaths.process_source_event first++
          ProcessPlacement.placement_lift(io_step(ProcessPlacement.admission_write_request cell locals cgroup Int.one)
            (transfer[Byte.repr 50]None))::
          (repeat ProcessPaths.process_source_event second++
            process_traced(Int.repr 16896)(Int.repr 2)(Vlong Int64.zero)
              (Vlong(Int64.repr 1048592))Int64.zero::repeat ProcessPaths.process_source_event 5))))
    (live(Returnstate(Vint Int.zero)Kstop after)).
Proof.
  destruct admission_actual_useful_input as[initial[cell[before[status[INITIAL[ERRNO[ACCESS SEPARATE]]]]]]].
  destruct(admission_useful_source_execution cell before cgroup status(Int.repr 5)ERRNO ACCESS SEPARATE)
    as[locals[first[second[after RUN]]]].
  exists initial,cell,before,status,locals,first,second,after;auto 8.
Qed.
