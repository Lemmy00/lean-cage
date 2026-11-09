(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Descriptor inheritance flags are changed at the real checked source call sites. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffStructure
  NativeHandoffArguments NativeHandoffNumeric NativeHandoffFormat NativeHandoffDescriptors.
Import ListNotations.
Open Scope Z_scope.

Definition handoff_flags_error code error :=
  Sifthenelse (Etempvar code tint)
    (Ssequence
      (Scall (Some error) (Evar EntrySource._error_number (Tfunction [] tint cc_default)) [])
      (Scall None (Evar EntrySource._fail_child (Tfunction [tint;tuint;tint] tvoid cc_default))
        [Etempvar EntrySource._failure tint;Econst_int (Int.repr 3) tint;Etempvar error tint])) Sskip.
Definition handoff_flags_call code descriptor flags :=
  Scall (Some code)
    (Evar EntrySource._entry_descriptor_flags (Tfunction [tint;tint] tint cc_default)) [descriptor;flags].

Definition handoff_fd_flags := match handoff_descriptor_after_format with
  | Ssequence _ (Ssequence _ rest) => rest | _ => Sskip end.
Definition handoff_flags_fd_cont e le k descriptor :=
  Kcall (Some EntrySource._t'16) EntrySource.f_guest e
    (PTree.set EntrySource._t'31 (Vint descriptor) le)
    (Kseq (handoff_flags_error EntrySource._t'16 EntrySource._t'15) k).

Lemma handoff_fd_flags_actual : handoff_fd_flags =
  Ssequence
    (Ssequence (Sset EntrySource._t'31 handoff_fd_getter)
      (handoff_flags_call EntrySource._t'16 (Etempvar EntrySource._t'31 tint) (Econst_int Int.zero tint)))
    (handoff_flags_error EntrySource._t'16 EntrySource._t'15).
Proof. reflexivity. Qed.

Lemma handoff_stdout_flags_actual : guest_phase 10 =
  Ssequence (handoff_flags_call EntrySource._t'18 (Econst_int Int.one tint) (Econst_int Int.one tint))
    (handoff_flags_error EntrySource._t'18 EntrySource._t'17).
Proof. reflexivity. Qed.

Lemma handoff_flags_binding :
  Genv.find_symbol handoff_ge EntrySource._entry_descriptor_flags = Some (handoff_symbol EntrySource._entry_descriptor_flags) /\
  Genv.find_funct handoff_ge (Vptr (handoff_symbol EntrySource._entry_descriptor_flags) Ptrofs.zero) = Some entry_flags_definition.
Proof. split; reflexivity. Qed.

Lemma handoff_flags_call_edge e le m k code descriptor_expression flags_expression descriptor flags :
  e ! EntrySource._entry_descriptor_flags = None ->
  expression_value handoff_ge e le m descriptor_expression (Vint descriptor) ->
  expression_value handoff_ge e le m flags_expression (Vint flags) ->
  typeof descriptor_expression = tint -> typeof flags_expression = tint ->
  store_edge handoff_ge
    (State EntrySource.f_guest (handoff_flags_call code descriptor_expression flags_expression) k e le m)
    (Callstate entry_flags_definition [Vint descriptor;Vint flags] (Kcall (Some code) EntrySource.f_guest e le k) m).
Proof.
  intros GLOBAL DESCRIPTOR FLAGS DESCRIPTORTYPE FLAGSTYPE; unfold handoff_flags_call.
  eapply certified_call_edge.
  - reflexivity.
  - apply old_expression_value; eapply value_function;
      [exact GLOBAL|exact (proj1 handoff_flags_binding)|reflexivity].
  - eapply cons_argument_values; [exact DESCRIPTOR|rewrite DESCRIPTORTYPE; reflexivity|].
    eapply cons_argument_values; [exact FLAGS|rewrite FLAGSTYPE; reflexivity|apply no_argument_values].
  - exact (proj2 handoff_flags_binding).
  - reflexivity.
Qed.

Theorem handoff_fd_flags_call_source e le m k handles index descriptor :
  e ! EntrySource._entry_descriptor_flags = None ->
  e ! EntrySource._handles = Some (handles,tarray tint 4) ->
  le ! EntrySource._i = Some (Vint (Int.repr index)) -> 0 <= index < 4 ->
  Mem.loadv Mint32 m (Vptr handles (Ptrofs.repr (4*index))) = Some (Vint descriptor) ->
  store_path handoff_ge (fun after=>after=m)
    (State EntrySource.f_guest handoff_fd_flags k e le m) 5
    (Callstate entry_flags_definition [Vint descriptor;Vint Int.zero]
      (handoff_flags_fd_cont e le k descriptor) m).
Proof.
  intros GLOBAL LOCAL INDEX BOUND LOAD; rewrite handoff_fd_flags_actual.
  handoff_route; handoff_route; handoff_set.
  - apply handoff_descriptor_at_value with (handles:=handles) (index:=index);
      [exact LOCAL|exact INDEX|exact BOUND|exact LOAD].
  - handoff_route; eapply store_next; [reflexivity|apply handoff_flags_call_edge|].
    + exact GLOBAL.
    + apply old_expression_value; apply value_temp; apply PTree.gss.
    + apply old_expression_value; apply value_int.
    + reflexivity.
    + reflexivity.
    + apply store_done; reflexivity.
Qed.

Theorem handoff_stdout_flags_call_source e le m k :
  e ! EntrySource._entry_descriptor_flags = None ->
  store_path handoff_ge (fun after=>after=m)
    (State EntrySource.f_guest (guest_phase 10) k e le m) 2
    (Callstate entry_flags_definition [Vint Int.one;Vint Int.one]
      (Kcall (Some EntrySource._t'18) EntrySource.f_guest e le
        (Kseq (handoff_flags_error EntrySource._t'18 EntrySource._t'17) k)) m).
Proof.
  intros GLOBAL; rewrite handoff_stdout_flags_actual.
  handoff_route; eapply store_next; [reflexivity|apply handoff_flags_call_edge|].
  - exact GLOBAL.
  - apply old_expression_value; apply value_int.
  - apply old_expression_value; apply value_int.
  - reflexivity.
  - reflexivity.
  - apply store_done; reflexivity.
Qed.

Theorem handoff_flags_return_source e le m k code error returned :
  store_path handoff_ge (fun after=>after=m)
    (Returnstate (Vint returned)
      (Kcall (Some code) EntrySource.f_guest e le (Kseq (handoff_flags_error code error) k)) m) 3
    (State EntrySource.f_guest
      (if Int.eq returned Int.zero then Sskip else
        match handoff_flags_error code error with Sifthenelse _ yes _ => yes | _ => Sskip end)
      k e (PTree.set code (Vint returned) le) m).
Proof.
  unfold handoff_flags_error; handoff_route; handoff_route.
  destruct (Int.eq returned Int.zero) eqn:ZERO.
  - eapply store_next; [reflexivity|apply certified_if_edge with (v:=Vint returned) (b:=false)|].
    + apply old_expression_value; apply value_temp; apply PTree.gss.
    + change (Some (negb (Int.eq returned Int.zero))=Some false); rewrite ZERO; reflexivity.
    + apply store_done; reflexivity.
  - eapply store_next; [reflexivity|apply certified_if_edge with (v:=Vint returned) (b:=true)|].
    + apply old_expression_value; apply value_temp; apply PTree.gss.
    + change (Some (negb (Int.eq returned Int.zero))=Some true); rewrite ZERO; reflexivity.
    + apply store_done; reflexivity.
Qed.
