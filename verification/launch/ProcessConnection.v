(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Connect actual Clight tracer requests to the ordinary Lean origin predicate. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Smallstep
  Ctypes Ctypesdefs Clight.
From LeanImport Require Import Lean.
From EntryNative Require Import EntrySource.
Require Import Machine.
From EntryProcess Require Import ProcessControl ProcessTrace ProcessImport ProcessMachine.
Import ListNotations.
Local Close Scope lean_scope.
Local Open Scope Z_scope.

Theorem release_byte_ordinary_Lean count byte : count = 1 -> byte = Byte.repr 165 ->
  LeanCage_Entry_ReleaseAccepted (Nat_of_nat (Z.to_nat count))
    (Nat_of_nat (Z.to_nat (Byte.unsigned byte))).
Proof.
  intros COUNT BYTE; subst. unfold LeanCage_Entry_ReleaseAccepted.
  constructor; constructor.
Qed.

Theorem checked_tracer_request_word request :
  tracer_request_allowed request = true ->
  LeanCage_Entry_NonSubstitutingRequest (Nat_of_nat (Z.to_nat (Int.unsigned request))).
Proof.
  intro ALLOWED. destruct (tracer_request_exact request ALLOWED) as [SAME|[SAME|SAME]];
    subst request; unfold LeanCage_Entry_NonSubstitutingRequest.
  - apply Lean.Or_inl; constructor.
  - apply Lean.Or_inr, Lean.Or_inl; constructor.
  - apply Lean.Or_inr, Lean.Or_inr; constructor.
Qed.

Theorem namespace_request_ordinary_Lean arguments before trace fn opt args k env temps memory
    ty child request address_value data_value calltrace fd next :
  star step2 (Clight.globalenv EntrySource.prog)
    (Callstate (Ctypes.Internal f_namespace_init) arguments Kstop before) trace
    (State fn (Scall opt (Evar _entry_ptrace4 ty) args) k env temps memory) ->
  step2 (Clight.globalenv EntrySource.prog)
    (State fn (Scall opt (Evar _entry_ptrace4 ty) args) k env temps memory) calltrace
    (Callstate fd [Vint request; Vint child; address_value; data_value] next memory) ->
  LeanCage_Entry_NonSubstitutingRequest (Nat_of_nat (Z.to_nat (Int.unsigned request))).
Proof.
  intros RUN CALL.
  destruct (namespace_tracer_invocation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RUN CALL)
    as [word [child_value [address [data [VALUES REQUEST]]]]].
  inversion VALUES; subst word.
  apply checked_tracer_request_word.
  destruct REQUEST as [SAME|[SAME|SAME]]; subst request; reflexivity.
Qed.

Theorem namespace_process_request_ordinary_Lean cell arguments before events fn opt args k env temps memory
    ty child request address_value data_value event fd next :
  process_steps (Clight.globalenv EntrySource.prog) cell
    (live (Callstate (Ctypes.Internal f_namespace_init) arguments Kstop before)) events
    (live (State fn (Scall opt (Evar _entry_ptrace4 ty) args) k env temps memory)) ->
  process_step (Clight.globalenv EntrySource.prog) cell
    (live (State fn (Scall opt (Evar _entry_ptrace4 ty) args) k env temps memory)) event
    (live (Callstate fd [Vint request; Vint child; address_value; data_value] next memory)) ->
  LeanCage_Entry_NonSubstitutingRequest (Nat_of_nat (Z.to_nat (Int.unsigned request))).
Proof.
  intros RUN CALL.
  destruct (namespace_process_tracer_invocation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RUN CALL)
    as [word [child_value [address [data [VALUES REQUEST]]]]].
  inversion VALUES; subst word. apply checked_tracer_request_word.
  destruct REQUEST as [SAME|[SAME|SAME]]; subst request; reflexivity.
Qed.
