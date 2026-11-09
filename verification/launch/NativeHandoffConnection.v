(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.values: Compose the actual image snapshot with the shared worker byte interface. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Ctypesdefs Clight.
From LeanImport Require Import Lean.
Require Import ArgumentsImport Machine.
From EntryNative Require Import EntrySource NativeValues NativeHandoffMachine NativeHandoffStructure
  NativeHandoffArguments NativeHandoffAllocation NativeHandoffInput NativeHandoffInitial NativeHandoffExec
  NativeHandoffGuest NativeHandoffWire NativeHandoffValues NativeHandoffImage HandoffRegion.
From LeanCageMainNumber Require Import NumberMath.
Import ListNotations.
Local Close Scope lean_scope.
Local Open Scope Z_scope.

Inductive handoff_checked_lean (claim:SProp) : Prop :=
| handoff_checked_lean_intro : claim ->handoff_checked_lean claim.

(* These are marshalling laws of one fresh exec/runtime startup. The relation
   copies the actual terminated table, drops argv[0], and exposes String.toUTF8
   bytes. Invalid UTF-8 is not assumed to survive the runtime's lossy decoder. *)
Record WorkerArgvContract (valid_utf8:list Byte.int->Prop)
    (copied:mem->block->List_inst1(List_inst1 UInt8)->Prop) : Prop := {
  worker_ascii_utf8 : forall bytes,
    Forall(fun byte=>Byte.unsigned byte<128)bytes ->valid_utf8 bytes;
  worker_argv_copy : forall m output first rest args,
    handoff_argv_bytes m output(first::rest) ->Forall valid_utf8 rest ->
    copied m output args ->Lean.eq args(argument_byte_lists rest)
}.

Lemma handoff_decimal_utf8 valid_utf8 copied (runtime:WorkerArgvContract valid_utf8 copied) bytes value :
  decimal_number bytes=Some value ->valid_utf8 bytes.
Proof.
  intros PARSED;apply(worker_ascii_utf8 _ _ runtime).
  destruct(proj1(decimal_number_exact bytes value)PARSED)as[_[DIGITS _]].
  eapply Forall_impl;[|exact DIGITS]. intros byte DIGIT;unfold decimal_digit_ok in DIGIT;lia.
Qed.

Lemma handoff_mode_utf8 valid_utf8 copied (runtime:WorkerArgvContract valid_utf8 copied) preflight :
  valid_utf8(handoff_worker_mode_bytes preflight).
Proof.
  apply(worker_ascii_utf8 _ _ runtime);unfold handoff_worker_mode_bytes;
    destruct(Int.eq preflight Int.zero);vm_compute;repeat constructor;lia.
Qed.

Lemma handoff_normal_utf8 valid_utf8 copied (runtime:WorkerArgvContract valid_utf8 copied) :
  valid_utf8 handoff_normal_bytes.
Proof. apply(worker_ascii_utf8 _ _ runtime);vm_compute;repeat constructor;lia. Qed.

Theorem handoff_snapshot_worker_connection cell input input_fd output_fd errors_fd failure state
    valid_utf8 copied (runtime:WorkerArgvContract valid_utf8 copied) :
  handoff_image_snapshot cell input input_fd output_fd errors_fd failure state ->
  valid_utf8(handoff_borrowed_root_bytes input) ->
  Forall valid_utf8(handoff_borrowed_argument_bytes input) ->
  exists b after caller suffix,
    state=Callstate entry_exec_definition
      [Vptr(handoff_symbol EntrySource.___stringlit_111)Ptrofs.zero;
       Vptr(handoff_arguments b)Ptrofs.zero;Vptr(handoff_environment b)Ptrofs.zero]
      (handoff_exec_cont(handoff_locals_env b)caller(Kseq(guest_tail 24(fn_body f_guest))suffix))after /\
    caller!EntrySource._failure=Some(Vint failure) /\
    handoff_checked_lean(forall args,
      copied after(handoff_arguments b)args ->
      LeanCage_Entry_ArgumentMeaning_nativeValues
        (Nat_of_nat(Z.to_nat(Int.unsigned(handoff_borrowed_uid input))))
        (Nat_of_nat(Z.to_nat(Int.signed input_fd)))(Nat_of_nat(Z.to_nat(Int.signed output_fd)))
        (Nat_of_nat(Z.to_nat(Int.signed errors_fd)))(Nat_of_nat(Z.to_nat(Int.signed failure)))
        (argument_bytes(handoff_worker_mode_bytes(handoff_borrowed_preflight input)))
        (argument_bytes(handoff_borrowed_root_bytes input))(argument_bytes handoff_normal_bytes)
        (argument_byte_lists(handoff_borrowed_argument_bytes input))args).
Proof.
  intros SNAPSHOT ROOTUTF8 ARGVUTF8.
  destruct(handoff_snapshot_wire _ _ _ _ _ _ _ SNAPSHOT)
    as[b[after[caller[suffix[uidbytes[inputbytes[outputbytes[errorsbytes[failurebytes
      [STATE[CALLERFAILURE[WIRE[ENVIRONMENT[UID[INPUT[OUTPUT[ERRORS FAILURE]]]]]]]]]]]]]]]]].
  exists b,after,caller,suffix;split;[exact STATE|]. split;[exact CALLERFAILURE|]. constructor.
  intros args COPY.
  assert(UTF8:Forall valid_utf8
    (handoff_worker_mode_bytes(handoff_borrowed_preflight input)::uidbytes::
      handoff_borrowed_root_bytes input::inputbytes::outputbytes::errorsbytes::failurebytes::
      handoff_normal_bytes::handoff_borrowed_argument_bytes input)).
  { apply Forall_cons;[eapply handoff_mode_utf8;exact runtime|].
    apply Forall_cons;[eapply handoff_decimal_utf8;[exact runtime|exact UID]|].
    apply Forall_cons;[exact ROOTUTF8|].
    apply Forall_cons;[eapply handoff_decimal_utf8;[exact runtime|exact INPUT]|].
    apply Forall_cons;[eapply handoff_decimal_utf8;[exact runtime|exact OUTPUT]|].
    apply Forall_cons;[eapply handoff_decimal_utf8;[exact runtime|exact ERRORS]|].
    apply Forall_cons;[eapply handoff_decimal_utf8;[exact runtime|exact FAILURE]|].
    apply Forall_cons;[eapply handoff_normal_utf8;exact runtime|exact ARGVUTF8]. }
  pose proof(worker_argv_copy _ _ runtime _ _ _ _ _ WIRE UTF8 COPY)as ORIGINAL.
  assert(SAME:args=argument_byte_lists
    (handoff_worker_mode_bytes(handoff_borrowed_preflight input)::uidbytes::
      handoff_borrowed_root_bytes input::inputbytes::outputbytes::errorsbytes::failurebytes::
      handoff_normal_bytes::handoff_borrowed_argument_bytes input)).
  { destruct ORIGINAL;reflexivity. }
  rewrite SAME.
  eapply handoff_imported_native_values;
    [exact UID|exact INPUT|exact OUTPUT|exact ERRORS|exact FAILURE].
Qed.

(* This interface starts at the maintained guest call. Its memory, image and
   copied values come from the same execution, including all failing and lost
   alternatives of that source machine. Preparation supplies only UTF-8 input
   strings; successful formatting, fd checks and the worker table are derived. *)
Theorem handoff_guest_worker_values cell input before
    input_fd output_fd errors_fd failure k events target path arguments environment
    valid_utf8 copied (runtime:WorkerArgvContract valid_utf8 copied) :
  handoff_borrowed_input cell before input ->
  entry_handoff_steps handoff_ge cell
    (live(Callstate(Internal f_guest)
      [Vint input_fd;Vint output_fd;Vint errors_fd;Vint failure]k before))events target ->
  In(entry_image path arguments environment)events ->
  valid_utf8(handoff_borrowed_root_bytes input) ->
  Forall valid_utf8(handoff_borrowed_argument_bytes input) ->
  exists prefix endpoint rest b after caller suffix,
    events=prefix++rest /\ handoff_no_images prefix /\
    entry_handoff_steps handoff_ge cell
      (live(Callstate(Internal f_guest)
        [Vint input_fd;Vint output_fd;Vint errors_fd;Vint failure]k before))prefix(live endpoint) /\
    endpoint=Callstate entry_exec_definition
      [Vptr(handoff_symbol EntrySource.___stringlit_111)Ptrofs.zero;
       Vptr(handoff_arguments b)Ptrofs.zero;Vptr(handoff_environment b)Ptrofs.zero]
      (handoff_exec_cont(handoff_locals_env b)caller(Kseq(guest_tail 24(fn_body f_guest))suffix))after /\
    handoff_image_snapshot cell input input_fd output_fd errors_fd failure endpoint /\
    entry_handoff_steps handoff_ge cell(live endpoint)rest target /\
    In(entry_image path arguments environment)rest /\
    caller!EntrySource._failure=Some(Vint failure) /\
    handoff_checked_lean(forall args,
      copied after(handoff_arguments b)args ->
      LeanCage_Entry_ArgumentMeaning_nativeValues
        (Nat_of_nat(Z.to_nat(Int.unsigned(handoff_borrowed_uid input))))
        (Nat_of_nat(Z.to_nat(Int.signed input_fd)))(Nat_of_nat(Z.to_nat(Int.signed output_fd)))
        (Nat_of_nat(Z.to_nat(Int.signed errors_fd)))(Nat_of_nat(Z.to_nat(Int.signed failure)))
        (argument_bytes(handoff_worker_mode_bytes(handoff_borrowed_preflight input)))
        (argument_bytes(handoff_borrowed_root_bytes input))(argument_bytes handoff_normal_bytes)
        (argument_byte_lists(handoff_borrowed_argument_bytes input))args) /\
    path=Vptr(handoff_symbol EntrySource.___stringlit_111)Ptrofs.zero /\
    arguments=Vptr(handoff_arguments b)Ptrofs.zero /\
    environment=Vptr(handoff_environment b)Ptrofs.zero /\target=dead after.
Proof.
  intros INPUT RUN IMAGE ROOTUTF8 ARGVUTF8.
  destruct(handoff_guest_image_has_checked_snapshot _ _ _ _ _ _ _ _ _ _ _ _ _ INPUT RUN IMAGE)
    as[prefix[endpoint[rest[EVENTS[NOIMAGES[PREFIX[SNAPSHOT[TAIL LATER]]]]]]]].
  destruct(handoff_snapshot_worker_connection _ _ _ _ _ _ _ _ _ runtime
    SNAPSHOT ROOTUTF8 ARGVUTF8)as[b[after[caller[suffix[STATE[CALLERFAILURE VALUES]]]]]].
  assert(EXACT:path=Vptr(handoff_symbol EntrySource.___stringlit_111)Ptrofs.zero /\
    arguments=Vptr(handoff_arguments b)Ptrofs.zero /\
    environment=Vptr(handoff_environment b)Ptrofs.zero /\target=dead after).
  { pose proof TAIL as EXEC;rewrite STATE in EXEC.
    destruct(handoff_exec_image_is_current cell b caller after failure suffix
      (Vptr(handoff_symbol EntrySource.___stringlit_111)Ptrofs.zero)
      (Vptr(handoff_arguments b)Ptrofs.zero)(Vptr(handoff_environment b)Ptrofs.zero)
      rest target path arguments environment CALLERFAILURE EXEC LATER)
      as[PATH[ARGS[ENV[waits[EVENTS' TARGET]]]]];auto. }
  exists prefix,endpoint,rest,b,after,caller,suffix;intuition.
Qed.
