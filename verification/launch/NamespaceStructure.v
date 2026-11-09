(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Functional source interfaces retain the exact channel/fork helper body. *)
From Stdlib Require Import ZArith List PArith.
From compcert Require Import Integers AST Ctypes Ctypesdefs Clight.
From EntryNative Require Import EntrySource.
From EntryNamespace Require Import NamespaceMachine.
Import ListNotations.
Open Scope Z_scope.

Definition namespace_ge := Clight.globalenv EntrySource.prog.

Fixpoint child_tail (index : nat) (body : statement) : statement :=
  match index,body with
  | O,_ => body
  | S rest,Ssequence _ body => child_tail rest body
  | _,_ => Sskip
  end.

Definition child_phase index :=
  match child_tail index (fn_body f_create_entry_child) with
  | Ssequence first _ => first
  | last => last
  end.

Definition child_socket := child_phase 0.
Definition child_duplicate := child_phase 1.
Definition child_close_original := child_phase 2.
Definition child_check_duplicate := child_phase 3.
Definition child_mask := child_phase 4.
Definition child_signals := child_phase 5.
Definition child_publish_peer := child_phase 6.
Definition child_fork := child_phase 7.
Definition child_publish_fork := child_phase 8.
Definition child_select_fork := child_phase 9.
Definition child_close_failure := child_phase 10.
Definition child_return := child_phase 11.

Theorem child_source_phases : fn_body f_create_entry_child =
  Ssequence child_socket (Ssequence child_duplicate
    (Ssequence child_close_original (Ssequence child_check_duplicate
      (Ssequence child_mask (Ssequence child_signals (Ssequence child_publish_peer
        (Ssequence child_fork (Ssequence child_publish_fork
          (Ssequence child_select_fork (Ssequence child_close_failure child_return)))))))))).
Proof. reflexivity. Qed.

Theorem child_source_signature :
  fn_params f_create_entry_child =
    [(_input,tint);(_output,tint);(_errors,tint);(_peer,tptr tint);(_child,tptr tint)] /\
  fn_vars f_create_entry_child = [(_pair,tarray tint 2)] /\
  child_return = Sreturn (Some (Econst_int Int.zero tint)) /\
  child_close_failure = Scall None (Evar _close (Tfunction [tint] tint cc_default))
    [Etempvar _failure tint].
Proof. repeat split; reflexivity. Qed.

Theorem child_selection_source : child_select_fork =
  Sifthenelse (Ebinop Cop.Oeq (Etempvar _forked tint) (Econst_int Int.zero tint) tint)
    (Scall None (Evar _guest (Tfunction [tint;tint;tint;tint] tvoid cc_default))
      [Etempvar _input tint;Etempvar _output tint;Etempvar _errors tint;Etempvar _failure tint])
    Sskip.
Proof. reflexivity. Qed.

Definition namespace_source_definition (id : ident) :=
  find (fun item => Pos.eqb (fst item) id) (prog_defs EntrySource.prog).

Theorem child_primitive_signatures :
  namespace_source_definition _socketpair = Some (_socketpair,Gfun namespace_pair_definition) /\
  namespace_source_definition _entry_duplicate_above =
    Some (_entry_duplicate_above,Gfun namespace_duplicate_definition) /\
  namespace_source_definition _entry_signal_mask =
    Some (_entry_signal_mask,Gfun namespace_mask_definition) /\
  namespace_source_definition _entry_signal_default =
    Some (_entry_signal_default,Gfun namespace_default_definition) /\
  namespace_source_definition _fork = Some (_fork,Gfun namespace_fork_definition).
Proof. repeat split; reflexivity. Qed.
