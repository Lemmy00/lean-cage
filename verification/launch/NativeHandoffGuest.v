(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: The complete actual guest reaches either checked image arguments or the real failure callee. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine StoreSteps WriteAll.
From EntryNative Require Import EntrySource NativeHandoffMachine HandoffRegion NativeHandoffStructure
  NativeHandoffArguments NativeHandoffAllocation NativeHandoffInput NativeHandoffInitial NativeHandoffMemory
  NativeHandoffEncoding NativeHandoffDescriptors NativeHandoffLoop NativeHandoffStdout NativeHandoffComposition NativeHandoffExec
  NativeHandoffSuffix NativeHandoffTables.
From LeanCageMainNumber Require Import NumberMemory NumberMath NumberInitial.
Import ListNotations.
Open Scope Z_scope.
Local Opaque handoff_ge handoff_symbol.

Definition handoff_image_snapshot cell input input_fd output_fd errors_fd failure state :=
  exists b after caller uidbytes fdtexts k,
    state=Callstate entry_exec_definition
      [Vptr(handoff_symbol EntrySource.___stringlit_111)Ptrofs.zero;
       Vptr(handoff_arguments b)Ptrofs.zero;Vptr(handoff_environment b)Ptrofs.zero]
      (handoff_exec_cont(handoff_locals_env b)caller(Kseq(guest_tail 24(fn_body EntrySource.f_guest))k))after /\
    caller!EntrySource._failure=Some(Vint failure) /\
    handoff_live_data cell input b(handoff_original_words input_fd output_fd errors_fd failure)after /\
    handoff_borrowed_mode_bytes input=handoff_normal_bytes /\
    100000<=Int.unsigned(handoff_borrowed_uid input)<=100999 /\
    number_input after(handoff_uid b)Ptrofs.zero uidbytes /\ (1<=length uidbytes<32)%nat /\
    decimal_number uidbytes=Some(Int.unsigned(handoff_borrowed_uid input)) /\
    handoff_fd_history b(handoff_original_words input_fd output_fd errors_fd failure)after 0 fdtexts /\
    length fdtexts=4%nat /\ handoff_descriptors_checked(handoff_original_words input_fd output_fd errors_fd failure)4 /\
    handoff_pointer_table after(handoff_arguments b)(handoff_public_arguments b input) /\
    handoff_pointer_table after(handoff_environment b)handoff_environment_values.

Lemma handoff_descriptors_tail_actual : guest_tail 9(fn_body EntrySource.f_guest)=
  Ssequence handoff_descriptor_loop(guest_tail 10(fn_body EntrySource.f_guest)).
Proof. reflexivity. Qed.

Theorem handoff_guest_region cell input before input_fd output_fd errors_fd failure k :
  handoff_borrowed_input cell before input ->
  handoff_region handoff_ge cell(fun _=>True)
    (fun state=>handoff_failure_result cell failure state \/
      handoff_image_snapshot cell input input_fd output_fd errors_fd failure state)30000
    (Callstate(Internal EntrySource.f_guest)[Vint input_fd;Vint output_fd;Vint errors_fd;Vint failure]k before).
Proof.
  intros INPUT;set(R:=fun state=>handoff_failure_result cell failure state \/
    handoff_image_snapshot cell input input_fd output_fd errors_fd failure state).
  assert(ACCEPT:forall state,handoff_failure_result cell failure state->R state)by(intros;left;assumption).
  eapply handoff_region_weaken with(n:=(128+(4000+(1+20008+(1+(514+2048)))))%nat);[|vm_compute;lia].
  refine(handoff_guest_initial_region cell input before input_fd output_fd errors_fd failure k R
    (4000+(1+20008+(1+(514+2048))))%nat INPUT ACCEPT _).
  intros b initialized initialle LAYOUT LIVE FAILURE MODE UIDBOUND.
  refine(handoff_uid_encoding_region cell input b(handoff_original_words input_fd output_fd errors_fd failure)
    initialized initialle k failure R(1+20008+(1+(514+2048)))%nat LAYOUT LIVE UIDBOUND FAILURE ACCEPT _).
  intros uid_after uidle uidbytes UIDLIVE UIDFAILURE UIDTEXT UIDLENGTH UIDPARSED.
  rewrite handoff_descriptors_tail_actual at 1.
  eapply handoff_region_source_prepend;[exact I|apply unchanged_store_edge;WriteAll.structural|].
  refine(handoff_descriptors_region cell input b(handoff_original_words input_fd output_fd errors_fd failure)
    uid_after uidle(Kseq(guest_tail 10(fn_body EntrySource.f_guest))k)failure uidbytes R
    (1+(514+2048))%nat LAYOUT UIDLIVE UIDFAILURE UIDTEXT ACCEPT _).
  intros fd_after fdle fdtexts FDLIVE FDFAILURE FDUINT FDHISTORY FDLENGTH FDCHECKED.
  eapply handoff_region_source_prepend;[exact I|apply unchanged_store_edge;WriteAll.structural|].
  refine(handoff_stdout_tail_region cell input b(handoff_original_words input_fd output_fd errors_fd failure)
    fd_after fdle k failure R 2048%nat LAYOUT FDLIVE FDFAILURE ACCEPT _).
  intros stdout_after stdoutle STDOUTLIVE STDOUTFAILURE ERRNOFRAME.
  assert(UIDTLS:handoff_uid b<>tls_block cell).
  { exact(proj1(handoff_private_object cell input b(handoff_uid b)32 LAYOUT
      ltac:(unfold handoff_objects;cbn;auto 8))). }
  assert(STDOUTUID:number_input stdout_after(handoff_uid b)Ptrofs.zero uidbytes)
    by(eapply handoff_errno_preserves_input;[exact ERRNOFRAME|exact UIDTLS|exact FDUINT]).
  assert(STDOUTHISTORY:handoff_fd_history b(handoff_original_words input_fd output_fd errors_fd failure)stdout_after 0 fdtexts)
    by(eapply handoff_fd_history_errno;[exact LAYOUT|exact ERRNOFRAME|exact FDHISTORY]).
  destruct(handoff_argument_tables_source cell input b(handoff_original_words input_fd output_fd errors_fd failure)
    stdout_after stdoutle k failure LAYOUT STDOUTLIVE STDOUTFAILURE)
    as[after[count[copied[COUNTBOUND[AFTER[TABLEFRAME[ARGSTABLE[ENVTABLE[FINALFAILURE PATH]]]]]]]]].
  eapply handoff_region_weaken with(n:=count);[|exact COUNTBOUND].
  replace count with(count+0)%nat at 1 by lia.
  eapply handoff_region_store_path with(count:=count)(remaining:=0%nat).
  - eapply number_path_implication;[intros;exact I|exact PATH].
  - apply handoff_region_stop;[exact I|]. right.
    exists b,after,(handoff_checked_argument_env copied(handoff_borrowed_source input)(handoff_borrowed_source_offset input)),
      uidbytes,fdtexts,k.
    split;[reflexivity|]. split.
    + unfold handoff_checked_argument_env;rewrite !PTree.gso by discriminate;exact FINALFAILURE.
    + split;[exact AFTER|]. split;[exact MODE|]. split;[exact UIDBOUND|]. split.
      * destruct(handoff_tables_numbers_separate b(proj1 LAYOUT))as[UIDARGS[UIDENV REST]].
        eapply handoff_tables_preserves_input;[exact TABLEFRAME|exact UIDARGS|exact UIDENV|exact STDOUTUID].
      * split;[exact UIDLENGTH|]. split;[exact UIDPARSED|]. split.
        -- eapply handoff_fd_history_tables;[exact(proj1 LAYOUT)|exact TABLEFRAME|exact STDOUTHISTORY].
        -- split;[exact FDLENGTH|]. split;[exact FDCHECKED|]. split;assumption.
Qed.
