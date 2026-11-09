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

Definition child_default_error_set := Sset _error__1 (Etempvar _t'7 tint).
Definition child_default_error_return := Sreturn (Some (Etempvar _error__1 tint)).
Definition child_default_close_peer :=
  Ssequence
    (Ssequence
      (Sset _t'11 (Ederef (Ebinop Oadd (Evar _pair (tarray tint 2))
        (Econst_int Int.zero tint) (tptr tint)) tint))
      (Scall None (Evar _close (Tfunction [tint] tint cc_default)) [Etempvar _t'11 tint]))
    child_default_error_return.
Definition child_default_cleanup :=
  Ssequence (Scall None (Evar _close (Tfunction [tint] tint cc_default)) [Etempvar _failure tint])
    child_default_close_peer.
Definition child_default_error_env le returned := PTree.set _t'8 (Vlong returned) le.
Definition child_default_error_cont pair le returned k :=
  Kcall (Some _t'7) f_create_entry_child (child_env pair) (child_default_error_env le returned)
    (Kseq child_default_error_set (Kseq child_default_cleanup
      (Kseq (child_tail 6 (fn_body f_create_entry_child)) k))).
Definition child_default_captured_env le returned error :=
  PTree.set _error__1 (Vint error) (PTree.set _t'7 (Vint error) (child_default_error_env le returned)).
Definition child_default_failure_close_cont pair le returned error k :=
  Kcall None f_create_entry_child (child_env pair) (child_default_captured_env le returned error)
    (Kseq child_default_close_peer (Kseq (child_tail 6 (fn_body f_create_entry_child)) k)).
Definition child_default_peer_close_env le returned error first :=
  PTree.set _t'11 (Vint first) (child_default_captured_env le returned error).
Definition child_default_peer_close_cont pair le returned error first k :=
  Kcall None f_create_entry_child (child_env pair) (child_default_peer_close_env le returned error first)
    (Kseq child_default_error_return (Kseq (child_tail 6 (fn_body f_create_entry_child)) k)).

Theorem child_default_failure_source pair le m k returned : returned <> Int64.zero ->
  store_path namespace_ge (fun current=>current=m)
    (Returnstate (Vlong returned) (child_default_cont pair le k) m) 6
    (Callstate (Internal f_error_number) [] (child_default_error_cont pair le returned k) m).
Proof.
  intro NONZERO; unfold child_default_cont,child_default_guard,child_default_error_cont,child_default_error_env,
    child_default_error_set,child_default_cleanup,child_default_close_peer,child_default_error_return,
    child_signals,child_phase,child_tail; cbn [fn_body].
  child_route; child_route.
  eapply store_next; [child_memory|apply certified_if_edge with (v:=Vlong returned) (b:=true)|].
  - apply old_expression_value,value_temp; apply PTree.gss.
  - change (Some (negb (Int64.eq returned Int64.zero)) = Some true).
    rewrite Int64.eq_false by exact NONZERO; reflexivity.
  - child_route; child_route; eapply store_next;
      [child_memory|child_call _error_number|apply store_done; child_memory].
    apply no_argument_values.
Qed.

Theorem child_default_error_capture_source pair le m k returned error failure :
  le!_failure = Some (Vint failure) ->
  store_path namespace_ge (fun current=>current=m)
    (Returnstate (Vint error) (child_default_error_cont pair le returned k) m) 6
    (Callstate close_definition [Vint failure] (child_default_failure_close_cont pair le returned error k) m).
Proof.
  intro FAILURE; unfold child_default_error_cont,child_default_error_set,child_default_captured_env,child_default_error_env,
    child_default_failure_close_cont,child_default_cleanup; child_route; child_route; child_set.
  - apply old_expression_value,value_temp; apply PTree.gss.
  - child_route; child_route.
    eapply store_next; [child_memory|child_call _close|apply store_done; child_memory].
    child_argument; apply no_argument_values.
Qed.

Theorem child_default_close_failure_return_source pair le m k returned error first close_return :
  Mem.load Mint32 m pair 0 = Some (Vint first) ->
  store_path namespace_ge (fun current=>current=m)
    (Returnstate close_return (child_default_failure_close_cont pair le returned error k) m) 7
    (Callstate close_definition [Vint first] (child_default_peer_close_cont pair le returned error first k) m).
Proof.
  intro FIRST; unfold child_default_failure_close_cont,child_default_close_peer,child_default_peer_close_cont,
    child_default_peer_close_env; child_route; child_route; child_route; child_route; child_set.
  - apply child_pair_slot_value; [lia|exact FIRST].
  - child_route; eapply store_next; [child_memory|child_call _close|apply store_done; child_memory].
    child_argument; apply no_argument_values.
Qed.

Theorem child_default_error_return_source pair le before after k returned error first close_return :
  Mem.free_list before (blocks_of_env namespace_ge (child_env pair)) = Some after ->
  store_path namespace_ge (fun current=>current=before \/ current=after)
    (Returnstate close_return (child_default_peer_close_cont pair le returned error first k) before) 3
    (Returnstate (Vint error) (call_cont k) after).
Proof.
  intro FREE; unfold child_default_peer_close_cont,child_default_peer_close_env,child_default_captured_env,
    child_default_error_return; child_route; child_route.
  eapply store_next; [child_memory|eapply certified_local_return_edge|apply store_done; child_memory].
  - apply old_expression_value,value_temp; WriteAll.lookup.
  - reflexivity.
  - exact FREE.
Qed.
