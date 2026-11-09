(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-entry.control: Actual local setup failures return an error before any fork. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll LibraryMachine.
From EntryNative Require Import EntrySource.
From EntryNamespace Require Import NamespaceStructure NamespaceAllocation NamespacePaths.
Import ListNotations.
Open Scope Z_scope.
Set Printing Depth 20.

Definition child_duplicate_error_return := Sreturn (Some (Etempvar _t'4 tint)).
Definition child_duplicate_error_call :=
  Scall (Some _t'4) (Evar _error_number (Tfunction [] tint cc_default)) [].
Definition child_duplicate_cleanup_env le first := PTree.set _t'13 (Vint first) le.
Definition child_duplicate_cleanup_cont pair le first k :=
  Kcall None f_create_entry_child (child_env pair) (child_duplicate_cleanup_env le first)
    (Kseq (Ssequence child_duplicate_error_call child_duplicate_error_return)
      (Kseq (child_tail 4 (fn_body f_create_entry_child)) k)).
Definition child_duplicate_error_cont pair le first k :=
  Kcall (Some _t'4) f_create_entry_child (child_env pair) (child_duplicate_cleanup_env le first)
    (Kseq child_duplicate_error_return (Kseq (child_tail 4 (fn_body f_create_entry_child)) k)).

Theorem child_duplicate_failure_source pair le m k failure first :
  le!_failure = Some (Vint failure) -> Int.signed failure < 0 ->
  Mem.load Mint32 m pair 0 = Some (Vint first) ->
  store_path namespace_ge (fun current=>current=m)
    (State f_create_entry_child (child_tail 3 (fn_body f_create_entry_child)) k (child_env pair) le m) 7
    (Callstate close_definition [Vint first] (child_duplicate_cleanup_cont pair le first k) m).
Proof.
  intros FAILURE NEGATIVE FIRST.
  unfold child_duplicate_cleanup_cont,child_duplicate_cleanup_env,child_duplicate_error_call,
    child_duplicate_error_return,child_tail; cbn [fn_body]; child_route.
  eapply store_next; [child_memory|apply certified_if_edge with (v:=Vint Int.one) (b:=true)|].
  - eapply binary_expression_value; [apply old_expression_value,value_temp; exact FAILURE|
      apply old_expression_value,value_int|].
    change (Some (Val.of_bool (Int.lt failure Int.zero)) = Some (Vint Int.one)).
    unfold Int.lt; rewrite Int.signed_zero; destruct (zlt (Int.signed failure) 0); [reflexivity|lia].
  - reflexivity.
  - child_route; child_route; child_set.
    + apply child_pair_slot_value; [lia|exact FIRST].
    + child_route; eapply store_next; [child_memory|child_call _close|apply store_done; child_memory].
      child_argument; apply no_argument_values.
Qed.

Theorem child_duplicate_cleanup_return_source pair le m k first returned :
  store_path namespace_ge (fun current=>current=m)
    (Returnstate returned (child_duplicate_cleanup_cont pair le first k) m) 4
    (Callstate (Internal f_error_number) [] (child_duplicate_error_cont pair le first k) m).
Proof.
  unfold child_duplicate_cleanup_cont,child_duplicate_error_cont,child_duplicate_error_call,
    child_duplicate_error_return; child_route; child_route; child_route.
  eapply store_next; [child_memory|child_call _error_number|apply store_done; child_memory].
  apply no_argument_values.
Qed.

Theorem child_duplicate_error_return_source pair le before after k first error :
  Mem.free_list before (blocks_of_env namespace_ge (child_env pair)) = Some after ->
  store_path namespace_ge (fun current=>current=before \/ current=after)
    (Returnstate (Vint error) (child_duplicate_error_cont pair le first k) before) 3
    (Returnstate (Vint error) (call_cont k) after).
Proof.
  intro FREE; unfold child_duplicate_error_cont,child_duplicate_error_return; child_route; child_route.
  eapply store_next; [child_memory|eapply certified_local_return_edge|apply store_done; child_memory].
  - apply old_expression_value,value_temp; apply PTree.gss.
  - reflexivity.
  - exact FREE.
Qed.

Definition child_mask_error_set := Sset _error (Etempvar _t'5 tint).
Definition child_mask_error_return := Sreturn (Some (Etempvar _error tint)).
Definition child_mask_close_peer :=
  Ssequence
    (Ssequence
      (Sset _t'12 (Ederef (Ebinop Oadd (Evar _pair (tarray tint 2))
        (Econst_int Int.zero tint) (tptr tint)) tint))
      (Scall None (Evar _close (Tfunction [tint] tint cc_default)) [Etempvar _t'12 tint]))
    child_mask_error_return.
Definition child_mask_cleanup :=
  Ssequence (Scall None (Evar _close (Tfunction [tint] tint cc_default)) [Etempvar _failure tint])
    child_mask_close_peer.
Definition child_mask_error_env le returned := PTree.set _t'6 (Vlong returned) le.
Definition child_mask_error_cont pair le returned k :=
  Kcall (Some _t'5) f_create_entry_child (child_env pair) (child_mask_error_env le returned)
    (Kseq child_mask_error_set (Kseq child_mask_cleanup
      (Kseq (child_tail 5 (fn_body f_create_entry_child)) k))).
Definition child_mask_captured_env le returned error :=
  PTree.set _error (Vint error) (PTree.set _t'5 (Vint error) (child_mask_error_env le returned)).
Definition child_mask_failure_close_cont pair le returned error k :=
  Kcall None f_create_entry_child (child_env pair) (child_mask_captured_env le returned error)
    (Kseq child_mask_close_peer (Kseq (child_tail 5 (fn_body f_create_entry_child)) k)).
Definition child_mask_peer_close_env le returned error first :=
  PTree.set _t'12 (Vint first) (child_mask_captured_env le returned error).
Definition child_mask_peer_close_cont pair le returned error first k :=
  Kcall None f_create_entry_child (child_env pair) (child_mask_peer_close_env le returned error first)
    (Kseq child_mask_error_return (Kseq (child_tail 5 (fn_body f_create_entry_child)) k)).

Theorem child_mask_failure_source pair le m k returned : returned <> Int64.zero ->
  store_path namespace_ge (fun current=>current=m)
    (Returnstate (Vlong returned) (child_mask_cont pair le k) m) 6
    (Callstate (Internal f_error_number) [] (child_mask_error_cont pair le returned k) m).
Proof.
  intro NONZERO; unfold child_mask_cont,child_mask_guard,child_mask_error_cont,child_mask_error_env,
    child_mask_error_set,child_mask_cleanup,child_mask_close_peer,child_mask_error_return,
    child_mask,child_phase,child_tail; cbn [fn_body].
  child_route; child_route.
  eapply store_next; [child_memory|apply certified_if_edge with (v:=Vlong returned) (b:=true)|].
  - apply old_expression_value,value_temp; apply PTree.gss.
  - change (Some (negb (Int64.eq returned Int64.zero)) = Some true).
    rewrite Int64.eq_false by exact NONZERO; reflexivity.
  - child_route; child_route; eapply store_next;
      [child_memory|child_call _error_number|apply store_done; child_memory].
    apply no_argument_values.
Qed.

Theorem child_mask_error_capture_source pair le m k returned error failure :
  le!_failure = Some (Vint failure) ->
  store_path namespace_ge (fun current=>current=m)
    (Returnstate (Vint error) (child_mask_error_cont pair le returned k) m) 6
    (Callstate close_definition [Vint failure] (child_mask_failure_close_cont pair le returned error k) m).
Proof.
  intro FAILURE; unfold child_mask_error_cont,child_mask_error_set,child_mask_captured_env,child_mask_error_env,
    child_mask_failure_close_cont,child_mask_cleanup; child_route; child_route; child_set.
  - apply old_expression_value,value_temp; apply PTree.gss.
  - child_route; child_route.
    eapply store_next; [child_memory|child_call _close|apply store_done; child_memory].
    child_argument; apply no_argument_values.
Qed.

Theorem child_mask_close_failure_return_source pair le m k returned error first close_return :
  Mem.load Mint32 m pair 0 = Some (Vint first) ->
  store_path namespace_ge (fun current=>current=m)
    (Returnstate close_return (child_mask_failure_close_cont pair le returned error k) m) 7
    (Callstate close_definition [Vint first] (child_mask_peer_close_cont pair le returned error first k) m).
Proof.
  intro FIRST; unfold child_mask_failure_close_cont,child_mask_close_peer,child_mask_peer_close_cont,
    child_mask_peer_close_env; child_route; child_route; child_route; child_route; child_set.
  - apply child_pair_slot_value; [lia|exact FIRST].
  - child_route; eapply store_next; [child_memory|child_call _close|apply store_done; child_memory].
    child_argument; apply no_argument_values.
Qed.

Theorem child_mask_error_return_source pair le before after k returned error first close_return :
  Mem.free_list before (blocks_of_env namespace_ge (child_env pair)) = Some after ->
  store_path namespace_ge (fun current=>current=before \/ current=after)
    (Returnstate close_return (child_mask_peer_close_cont pair le returned error first k) before) 3
    (Returnstate (Vint error) (call_cont k) after).
Proof.
  intro FREE; unfold child_mask_peer_close_cont,child_mask_peer_close_env,child_mask_captured_env,
    child_mask_error_return; child_route; child_route.
  eapply store_next; [child_memory|eapply certified_local_return_edge|apply store_done; child_memory].
  - apply old_expression_value,value_temp; WriteAll.lookup.
  - reflexivity.
  - exact FREE.
Qed.
