(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-entry.release: The actual sender's owned byte determines normal and partial-loss output. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events
  Ctypes Ctypesdefs Clight.
Require Import IO Machine ClightSteps StoreSteps ErrorNumber WriteMemory WriteAll.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessAllocation ProcessPaths ProcessRelease
  ProcessPrimitiveCases.
Import ListNotations.
Open Scope Z_scope.

Definition release_request cell peer grant : request :=
  {|operation:=writing;descriptor:=peer;buffer_block:=grant;buffer_offset:=0;requested:=1;
    errno_block:=tls_block cell;errno_offset:=tls_offset cell|}.
Definition release_byte memory grant :=
  Mem.loadbytes memory grant 0 1 = Some [Byte (Byte.repr 165)].

Theorem release_store_byte before after grant :
  Mem.store Mint8unsigned before grant 0 (Vint(Int.repr 165))=Some after -> release_byte after grant.
Proof. intro STORE;exact(Mem.loadbytes_store_same _ _ _ _ _ _ STORE). Qed.

Theorem release_errno_preserves_byte cell before after grant :
  grant<>tls_block cell -> entry_errno_frame cell before after ->
  release_byte before grant ->release_byte after grant.
Proof.
  intros SEPARATE FRAME BYTE;eapply Mem.loadbytes_unchanged_on;[exact FRAME| |exact BYTE].
  intros position RANGE;left;exact SEPARATE.
Qed.

Theorem release_request_owned cell peer grant memory :
  entry_errno_ready cell memory ->grant<>tls_block cell ->release_byte memory grant ->
  owned(release_request cell peer grant)memory.
Proof.
  intros [error [LOW[HIGH[ACCESS LOAD]]]] SEPARATE BYTE.
  unfold owned,release_request;cbn.
  split;[lia|]. split;[change(0<=0<18446744073709551616);lia|].
  split;[change(0+1<=18446744073709551616);lia|].
  split;[exact LOW|]. split;[exact HIGH|]. split;[exact ACCESS|].
  split;[left;exact SEPARATE|]. exists[Byte.repr 165];split;[reflexivity|exact BYTE].
Qed.

Theorem release_transfer_exact cell peer grant memory bytes error after :
  release_byte memory grant ->
  io_return(release_request cell peer grant)memory(transfer bytes error)after ->
  bytes=[Byte.repr 165].
Proof.
  intros BYTE EFFECT;inversion EFFECT;subst;try discriminate.
  assert(LENGTH:Z.of_nat(length bytes)=1)by(cbn in *;lia).
  cbn [release_request] in H4;rewrite LENGTH in H4;unfold release_byte in BYTE.
  change(Mem.loadbytes memory grant 0 1=Some(map Byte bytes))in H4.
  rewrite BYTE in H4;apply map_byte_injective;cbn;injection H4 as SAME;symmetry;exact SAME.
Qed.

Definition release_wire_event peer event : Prop :=
  match event with
  | process_entry(NativeHandoffMachine.entry_library(LibraryMachine.original_event(io_step q reply))) =>
      operation q=writing /\descriptor q=peer /\requested q=1 /\
        forall bytes error,reply=transfer bytes error ->bytes=[Byte.repr 165]
  | process_entry(NativeHandoffMachine.entry_library(LibraryMachine.original_event(partial_loss q bytes _))) =>
      operation q=writing /\descriptor q=peer /\requested q=1 /\bytes=[Byte.repr 165]
  | _=>True
  end.

Inductive release_bytes_invariant cell (child peer:int) : machine ->Prop :=
| release_bytes_resume : forall state count grant le memory,
    le!_peer=Some(Vint peer) ->grant<>tls_block cell ->release_byte memory grant ->
    store_path admission_ge(fun _=>True)state count
      (Callstate process_ptrace_definition
        [Vint(Int.repr 7);Vint child;Vlong Int64.zero;Vlong Int64.zero]
        (release_resume_cont grant le Kstop)memory) ->
    release_bytes_invariant cell child peer(live state)
| release_bytes_write : forall state count grant le memory,
    owned(release_request cell peer grant)memory ->release_byte memory grant ->
    store_path admission_ge(fun _=>True)state count
      (Callstate(External(io_function writing)[tint;tptr tvoid;tulong]tlong cc_default)
        (request_args(release_request cell peer grant))
        (release_write_cont grant le Kstop)memory) ->
    release_bytes_invariant cell child peer(live state)
| release_bytes_finishing : forall state count grant le memory k expression,
    call_cont k=Kstop ->store_path admission_ge(fun _=>True)state count
      (State f_release_child(Sreturn(Some expression))k(release_env grant)le memory) ->
    release_bytes_invariant cell child peer(live state)
| release_bytes_return : forall value memory,
    release_bytes_invariant cell child peer(live(Returnstate value Kstop memory))
| release_bytes_dead : forall memory,release_bytes_invariant cell child peer(dead memory).

Theorem release_bytes_step cell child peer state event target :
  release_bytes_invariant cell child peer state ->process_step admission_ge cell state event target ->
  release_wire_event peer event /\release_bytes_invariant cell child peer target.
Proof.
  intros INVARIANT STEP;destruct INVARIANT as
    [state count grant le memory PEER SEPARATE BYTE PATH|
     state count grant le memory OWN BYTE PATH|
     state count grant le memory k expression CLOSED PATH|value memory|memory].
  - inversion PATH as[current GOOD|current next rest last GOOD EDGE TAIL];subst.
    + destruct(process_ptrace_cases _ _ _ _ _ _ _ _ _ _ STEP)
        as[[returned[after[FRAME[ERRNO[EVENT TARGET]]]]]|[[EVENT TARGET]|
          [[EVENT TARGET]|[after[EVENT[PARTIAL TARGET]]]]]];subst;split;[exact I| |exact I| |exact I|constructor|exact I|constructor].
      * destruct(release_resumed returned)eqn:RESUMED.
        -- assert(BYTE':release_byte after grant).
           { eapply release_errno_preserves_byte;[exact SEPARATE|exact FRAME|exact BYTE]. }
           eapply release_bytes_write with(grant:=grant)(le:=release_after_resume_env le returned)(memory:=after).
           ++ apply release_request_owned;assumption.
           ++ exact BYTE'.
           ++ eapply store_path_trans.
              ** pose proof(release_resume_return_source grant le after Kstop returned)as RESUME.
                 rewrite RESUMED in RESUME;exact RESUME.
              ** apply release_write_call_source.
                 unfold release_after_resume_env;rewrite PTree.gso by discriminate;exact PEER.
        -- eapply release_bytes_finishing with(k:=Kseq(release_tail 2)Kstop);[reflexivity|].
           pose proof(release_resume_return_source grant le after Kstop returned)as RESUME.
           rewrite RESUMED in RESUME;exact RESUME.
      * eapply release_bytes_resume;[exact PEER|exact SEPARATE|exact BYTE|constructor;exact I].
    + destruct(process_store_edge_cases _ _ _ _ _ _ EDGE STEP)as[[EVENT TARGET]|[EVENT TARGET]];
        subst;split;[exact I| |exact I|constructor].
      eapply release_bytes_resume;eassumption.
  - inversion PATH as[current GOOD|current next rest last GOOD EDGE TAIL];subst.
    + destruct(process_write_cases _ _ _ _ _ _ _ OWN eq_refl eq_refl eq_refl STEP)
        as[[reply[after[EFFECT[EVENT TARGET]]]]|[[EVENT TARGET]|
          [[EVENT TARGET]|[bytes[error[after[EFFECT[EVENT TARGET]]]]]]]];subst.
      * split.
        -- cbn;repeat split;try reflexivity;intros bytes error SAME;subst reply.
           eapply release_transfer_exact;eassumption.
        -- pose proof(release_write_return_source grant le after Kstop(returned reply))as FINISH.
           destruct(release_written(returned reply)).
           ++ eapply release_bytes_finishing with(k:=Kstop)
                (expression:=Econst_int Int.zero tint);[reflexivity|exact FINISH].
           ++ eapply release_bytes_finishing with(k:=Kseq(release_tail 3)Kstop)
                (expression:=Eunop Cop.Oneg(Econst_int Int.one tint)tint);[reflexivity|exact FINISH].
      * split;[exact I|]. eapply release_bytes_write;[exact OWN|exact BYTE|constructor;exact I].
      * split;[exact I|constructor].
      * split.
        -- cbn;repeat split;try reflexivity;eapply release_transfer_exact;eassumption.
        -- constructor.
    + destruct(process_store_edge_cases _ _ _ _ _ _ EDGE STEP)as[[EVENT TARGET]|[EVENT TARGET]];
        subst;split;[exact I| |exact I|constructor].
      eapply release_bytes_write;eassumption.
  - inversion PATH as[current GOOD|current next rest last GOOD EDGE TAIL];subst.
    + destruct(process_return_statement_terminates _ _ _ _ _ _ _ _ _ _ CLOSED STEP)
        as[[EVENT[value[after TARGET]]]|[EVENT TARGET]];subst;split;[exact I|constructor|exact I|constructor].
    + destruct(process_store_edge_cases _ _ _ _ _ _ EDGE STEP)as[[EVENT TARGET]|[EVENT TARGET]];
        subst;split;[exact I| |exact I|constructor].
      eapply release_bytes_finishing;eassumption.
  - destruct(process_stopped_return_only_loss _ _ _ _ _ _ STEP)as[EVENT TARGET];subst;split;[exact I|constructor].
  - exfalso;eapply process_dead_cannot_resume;exact STEP.
Qed.

Theorem release_initial_bytes_from_live_tls cell before child peer :
  Mem.valid_block before(tls_block cell) ->
  release_bytes_invariant cell child peer
    (live(Callstate(Internal f_release_child)[Vint child;Vint peer]Kstop before)).
Proof.
  intro VALID.
  destruct(Mem.alloc before 0 1)as[allocated grant]eqn:ALLOC.
  assert(SEPARATE:grant<>tls_block cell).
  { intro SAME;subst grant;eapply Mem.fresh_block_alloc;[exact ALLOC|exact VALID]. }
  assert(GRANT:Mem.valid_access allocated Mint8unsigned grant 0 Freeable).
  { eapply Mem.valid_access_alloc_same;[exact ALLOC|lia|cbn;lia|exists 0;reflexivity]. }
  assert(WRITE:Mem.valid_access allocated Mint8unsigned grant 0 Writable).
  { eapply Mem.valid_access_implies;[exact GRANT|constructor]. }
  destruct(Mem.valid_access_store _ _ _ _(Vint(Int.repr 165))WRITE)as[after STORE].
  eapply release_bytes_resume with(grant:=grant)(le:=release_parameters child peer)
    (memory:=after)(count:=7%nat).
  - unfold release_parameters;WriteAll.lookup.
  - exact SEPARATE.
  - eapply release_store_byte;exact STORE.
  - eapply release_start_to_resume;eassumption.
Qed.

Theorem release_initial_bytes cell before child peer :
  entry_errno_ready cell before ->
  release_bytes_invariant cell child peer
    (live(Callstate(Internal f_release_child)[Vint child;Vint peer]Kstop before)).
Proof.
  intros[error[LOW[HIGH[ACCESS LOAD]]]].
  apply release_initial_bytes_from_live_tls.
  eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[exact ACCESS|constructor].
Qed.

Theorem release_actual_wire_bytes_from_live_tls cell before child peer events target :
  Mem.valid_block before(tls_block cell) ->
  process_steps admission_ge cell
    (live(Callstate(Internal f_release_child)[Vint child;Vint peer]Kstop before))events target ->
  Forall(release_wire_event peer)events.
Proof.
  intros READY RUN.
  pose proof(release_initial_bytes_from_live_tls cell before child peer READY)as INITIAL.
  revert INITIAL;induction RUN;intros INVARIANT;[constructor|].
  destruct(release_bytes_step _ _ _ _ _ _ INVARIANT H)as[EVENT NEXT].
  constructor;[exact EVENT|apply IHRUN;exact NEXT].
Qed.

Theorem release_actual_wire_bytes cell before child peer events target :
  entry_errno_ready cell before ->
  process_steps admission_ge cell
    (live(Callstate(Internal f_release_child)[Vint child;Vint peer]Kstop before))events target ->
  Forall(release_wire_event peer)events.
Proof.
  intros[error[LOW[HIGH[ACCESS LOAD]]]] RUN.
  eapply release_actual_wire_bytes_from_live_tls;[|exact RUN].
  eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[exact ACCESS|constructor].
Qed.
