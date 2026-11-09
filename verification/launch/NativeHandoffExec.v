(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Actual final NULL checks, environment stores and entry-image exec arguments. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffStructure NativeHandoffArguments.
Import ListNotations.
Open Scope Z_scope.

Definition handoff_checked_argument_env le source offset :=
  PTree.set EntrySource._t'24 (Vlong Int64.zero)
    (PTree.set EntrySource._t'23 (Vptr source offset) le).

Theorem handoff_final_argument_check_source e le m source offset index k :
  e ! EntrySource._policy__1 = None ->
  Mem.loadv Mptr m (Vptr (handoff_symbol EntrySource._policy__1) (Ptrofs.repr 88)) = Some (Vptr source offset) ->
  le ! EntrySource._i__2 = Some (Vlong (Int64.repr index)) -> 0 <= index <= 64 ->
  Mem.loadv Mptr m (Vptr source (Ptrofs.add offset (Ptrofs.repr (8 * index)))) = Some (Vlong Int64.zero) ->
  store_path handoff_ge (fun after => after = m)
    (State EntrySource.f_guest guest_check_arguments k e le m) 7
    (State EntrySource.f_guest Sskip k e (handoff_checked_argument_env le source offset) m).
Proof.
  intros GLOBAL POLICY INDEX BOUND LOAD.
  unfold guest_check_arguments, guest_phase, guest_tail; cbn [fn_body].
  handoff_route; handoff_set.
  - apply handoff_policy_arguments_value; [exact GLOBAL|exact POLICY].
  - handoff_route; handoff_route; handoff_set.
    + apply handoff_argument_slot_value with (source := source) (offset := offset) (index := index).
      * apply PTree.gss.
      * WriteAll.lookup.
      * exact BOUND.
      * exact LOAD.
    + handoff_route.
      eapply store_next; [reflexivity|apply certified_if_edge with (v := Vlong Int64.zero) (b := false)|].
      * apply old_expression_value; apply value_temp; apply PTree.gss.
      * reflexivity.
      * apply store_done; reflexivity.
Qed.

Theorem handoff_argument_terminator_source e le before after output index k :
  e ! EntrySource._args = Some (output,tarray (tptr tschar) 74) ->
  le ! EntrySource._i__2 = Some (Vlong (Int64.repr index)) -> 0 <= index <= 64 ->
  Mem.store Mptr before output (8 * (9 + index)) (Vlong Int64.zero) = Some after ->
  store_path handoff_ge (fun current => current = before \/ current = after)
    (State EntrySource.f_guest (guest_phase 20) k e le before) 1
    (State EntrySource.f_guest Sskip k e le after).
Proof.
  intros LOCAL INDEX BOUND STORE; unfold guest_phase, guest_tail; cbn [fn_body].
  eapply store_next; [left; reflexivity| |].
  - eapply assignment_source_edge with (v := Vlong Int64.zero) (w := Vlong Int64.zero).
    + apply pointer_location_value; eapply binary_expression_value.
      * apply handoff_array_value; exact LOCAL.
      * eapply binary_expression_value.
        -- apply old_expression_value; apply value_int.
        -- apply old_expression_value; apply value_temp; exact INDEX.
        -- apply handoff_index_destination; exact BOUND.
      * apply handoff_pointer_add_array; lia.
    + eapply cast_expression_value; [apply old_expression_value; apply value_int|reflexivity].
    + reflexivity.
    + eapply assign_loc_value; [reflexivity|].
      unfold Mem.storev; rewrite Ptrofs.unsigned_repr
        by (change Ptrofs.max_unsigned with 18446744073709551615; lia).
      destruct (zle _ _) as [LIMIT|OVER]; [exact STORE|].
      exfalso; change (8 * (9 + index) + 8 > 18446744073709551616) in OVER; lia.
  - apply store_done; right; reflexivity.
Qed.

Lemma handoff_pointer_add_signed_array ge m block count index : 0 <= index <= 74 ->
  sem_binary_operation ge Oadd (Vptr block Ptrofs.zero) (tarray (tptr tschar) count)
    (Vint (Int.repr index)) tint m = Some (Vptr block (Ptrofs.repr (8 * index))).
Proof.
  intros INDEX.
  change (Some (Vptr block (Ptrofs.add Ptrofs.zero
    (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_ints (Int.repr index))))) =
    Some (Vptr block (Ptrofs.repr (8 * index)))).
  unfold Ptrofs.of_ints; rewrite Int.signed_repr
    by (change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia).
  rewrite Ptrofs.add_zero_l, Ptrofs.mul_signed, !Ptrofs.signed_repr
    by (change Ptrofs.min_signed with (-9223372036854775808);
      change Ptrofs.max_signed with 9223372036854775807; lia).
  reflexivity.
Qed.

Lemma handoff_environment_literal_binding :
  Genv.find_symbol handoff_ge EntrySource.___stringlit_114 = Some (handoff_symbol EntrySource.___stringlit_114).
Proof. reflexivity. Qed.

Theorem handoff_environment_value_source e le before after environment k :
  e ! EntrySource._env = Some (environment,tarray (tptr tschar) 2) ->
  e ! EntrySource.___stringlit_114 = None ->
  Mem.store Mptr before environment 0 (Vptr (handoff_symbol EntrySource.___stringlit_114) Ptrofs.zero) = Some after ->
  store_path handoff_ge (fun current => current = before \/ current = after)
    (State EntrySource.f_guest (guest_phase 21) k e le before) 1
    (State EntrySource.f_guest Sskip k e le after).
Proof.
  intros LOCAL GLOBAL STORE; unfold guest_phase, guest_tail; cbn [fn_body].
  eapply store_next; [left; reflexivity| |].
  - eapply assignment_source_edge with
      (v := Vptr (handoff_symbol EntrySource.___stringlit_114) Ptrofs.zero)
      (w := Vptr (handoff_symbol EntrySource.___stringlit_114) Ptrofs.zero).
    + apply pointer_location_value; eapply binary_expression_value.
      * apply handoff_array_value; exact LOCAL.
      * apply old_expression_value; apply value_int.
      * apply handoff_pointer_add_signed_array; lia.
    + apply old_expression_value; eapply value_function;
        [exact GLOBAL|apply handoff_environment_literal_binding|reflexivity].
    + reflexivity.
    + eapply assign_loc_value; [reflexivity|exact STORE].
  - apply store_done; right; reflexivity.
Qed.

Theorem handoff_environment_terminator_source e le before after environment k :
  e ! EntrySource._env = Some (environment,tarray (tptr tschar) 2) ->
  Mem.store Mptr before environment 8 (Vlong Int64.zero) = Some after ->
  store_path handoff_ge (fun current => current = before \/ current = after)
    (State EntrySource.f_guest (guest_phase 22) k e le before) 1
    (State EntrySource.f_guest Sskip k e le after).
Proof.
  intros LOCAL STORE; unfold guest_phase, guest_tail; cbn [fn_body].
  eapply store_next; [left; reflexivity| |].
  - eapply assignment_source_edge with (v := Vlong Int64.zero) (w := Vlong Int64.zero).
    + apply pointer_location_value; eapply binary_expression_value.
      * apply handoff_array_value; exact LOCAL.
      * apply old_expression_value; apply value_int.
      * apply handoff_pointer_add_signed_array; lia.
    + eapply cast_expression_value; [apply old_expression_value; apply value_int|reflexivity].
    + reflexivity.
    + eapply assign_loc_value; [reflexivity|exact STORE].
  - apply store_done; right; reflexivity.
Qed.

Lemma handoff_exec_binding :
  Genv.find_symbol handoff_ge EntrySource._execve = Some (handoff_symbol EntrySource._execve) /\
  Genv.find_funct handoff_ge (Vptr (handoff_symbol EntrySource._execve) Ptrofs.zero) = Some entry_exec_definition.
Proof. split; reflexivity. Qed.

Definition handoff_exec_cont e le k := Kcall None EntrySource.f_guest e
  (PTree.set EntrySource._t'22 (Vptr (handoff_symbol EntrySource.___stringlit_111) Ptrofs.zero) le) k.

Theorem handoff_entry_exec_source e le m output environment k :
  e ! EntrySource._args = Some (output,tarray (tptr tschar) 74) ->
  e ! EntrySource._env = Some (environment,tarray (tptr tschar) 2) ->
  e ! EntrySource._execve = None ->
  Mem.loadv Mptr m (Vptr output Ptrofs.zero) =
    Some (Vptr (handoff_symbol EntrySource.___stringlit_111) Ptrofs.zero) ->
  store_path handoff_ge (fun after => after = m)
    (State EntrySource.f_guest (guest_phase 23) k e le m) 4
    (Callstate entry_exec_definition
      [Vptr (handoff_symbol EntrySource.___stringlit_111) Ptrofs.zero;
       Vptr output Ptrofs.zero; Vptr environment Ptrofs.zero]
      (handoff_exec_cont e le k) m).
Proof.
  intros ARGUMENTS ENVIRONMENT GLOBAL LOAD; unfold guest_phase, guest_tail; cbn [fn_body].
  handoff_route; handoff_set.
  - eapply location_read_value.
    + apply pointer_location_value; eapply binary_expression_value.
      * apply handoff_array_value; exact ARGUMENTS.
      * apply old_expression_value; apply value_int.
      * apply handoff_pointer_add_signed_array; lia.
    + eapply deref_loc_value; [reflexivity|exact LOAD].
  - handoff_route.
    eapply store_next; [reflexivity| |].
    + eapply certified_call_edge.
      * reflexivity.
      * apply old_expression_value; eapply value_function;
          [exact GLOBAL|exact (proj1 handoff_exec_binding)|reflexivity].
      * eapply cons_argument_values.
        -- apply old_expression_value; apply value_temp; apply PTree.gss.
        -- reflexivity.
        -- eapply cons_argument_values.
           ++ apply handoff_array_value; exact ARGUMENTS.
           ++ reflexivity.
           ++ eapply cons_argument_values.
              ** apply handoff_array_value; exact ENVIRONMENT.
              ** reflexivity.
              ** apply no_argument_values.
      * exact (proj2 handoff_exec_binding).
      * reflexivity.
    + apply store_done; reflexivity.
Qed.
