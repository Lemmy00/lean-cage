(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Actual wait identity and SIGSTOP guards precede every placement operation. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From EntryNative Require Import EntrySource.
From EntryProcess Require Import ProcessAllocation ProcessStructure ProcessReturns ProcessWait.
Import ListNotations.
Open Scope Z_scope.

Definition admission_is_stopped word :=
  Int.eq (Int.and word (Int.repr 255)) (Int.repr 127).
Definition admission_is_sigstop word :=
  Int.eq (Int.shr (Int.and word (Int.repr 65280)) (Int.repr 8)) (Int.repr 19).
Definition admission_status_load := Ederef (Etempvar _status (tptr tint)) tint.

Theorem admission_status_guards_source :
  admission_identity = Sifthenelse (Ebinop One (Etempvar _got tint) (Etempvar _child tint) tint)
    admission_failure Sskip /\
  admission_stopped = Ssequence (Sset _t'11 admission_status_load)
    (Sifthenelse (Eunop Onotbool (Ebinop Oeq
      (Ebinop Oand (Etempvar _t'11 tint) (Econst_int (Int.repr 255) tint) tint)
      (Econst_int (Int.repr 127) tint) tint) tint) admission_failure Sskip) /\
  admission_stopsig = Ssequence (Sset _t'10 admission_status_load)
    (Sifthenelse (Ebinop One (Ebinop Oshr
      (Ebinop Oand (Etempvar _t'10 tint) (Econst_int (Int.repr 65280) tint) tint)
      (Econst_int (Int.repr 8) tint) tint) (Econst_int (Int.repr 19) tint) tint)
      admission_failure Sskip).
Proof. repeat split; reflexivity. Qed.

Theorem admission_identity_guard e le memory k got child :
  le!_got = Some (Vint got) -> le!_child = Some (Vint child) ->
  store_path admission_ge (fun _ => True)
    (State f_admit_child admission_after_wait k e le memory)
    (if Int.eq got child then 3 else 2)%nat
    (if Int.eq got child then
       State f_admit_child (admission_tail 2 (fn_body f_admit_child)) k e le memory
     else State f_admit_child admission_failure
       (Kseq (admission_tail 2 (fn_body f_admit_child)) k) e le memory).
Proof.
  intros GOT CHILD.
  change admission_after_wait with
    (Ssequence admission_identity (admission_tail 2 (fn_body f_admit_child))).
  rewrite (proj1 admission_status_guards_source).
  pose proof (admission_guard_source e le memory k
    (Ebinop One (Etempvar _got tint) (Etempvar _child tint) tint)
    (admission_tail 2 (fn_body f_admit_child)) (negb (Int.eq got child))) as PATH.
  specialize (PATH eq_refl).
  assert (TEST : expression_value admission_ge e le memory
    (Ebinop One (Etempvar _got tint) (Etempvar _child tint) tint)
    (Val.of_bool (negb (Int.eq got child)))).
  { apply old_expression_value; eapply value_binary;
      [apply value_temp;exact GOT|apply value_temp;exact CHILD|reflexivity]. }
  specialize (PATH TEST); destruct (Int.eq got child); exact PATH.
Qed.

Theorem admission_status_load_value e le memory status offset word :
  le!_status = Some (Vptr status offset) ->
  Mem.loadv Mint32 memory (Vptr status offset) = Some (Vint word) ->
  expression_value admission_ge e le memory admission_status_load (Vint word).
Proof.
  intros STATUS LOAD; apply old_expression_value; eapply value_load;
    [apply value_temp;exact STATUS|reflexivity|exact LOAD].
Qed.

Definition admission_stopped_env le word := PTree.set _t'11 (Vint word) le.
Definition admission_stopsig_env le word := PTree.set _t'10 (Vint word) le.

Theorem admission_stopped_guard e le memory k status offset word :
  le!_status = Some (Vptr status offset) ->
  Mem.loadv Mint32 memory (Vptr status offset) = Some (Vint word) ->
  store_path admission_ge (fun _ => True)
    (State f_admit_child (admission_tail 2 (fn_body f_admit_child)) k e le memory)
    (if admission_is_stopped word then 6 else 5)%nat
    (if admission_is_stopped word then
      State f_admit_child (admission_tail 3 (fn_body f_admit_child)) k e
        (admission_stopped_env le word) memory
     else State f_admit_child admission_failure
       (Kseq (admission_tail 3 (fn_body f_admit_child)) k) e
       (admission_stopped_env le word) memory).
Proof.
  intros STATUS LOAD.
  change (admission_tail 2 (fn_body f_admit_child)) with
    (Ssequence admission_stopped (admission_tail 3 (fn_body f_admit_child))).
  rewrite (proj1 (proj2 admission_status_guards_source)).
  replace (if admission_is_stopped word then 6 else 5)%nat with
    (S (S (S (S (S (if admission_is_stopped word then 1 else 0))))))
    by (destruct (admission_is_stopped word); reflexivity).
  admission_route; admission_route; admission_set.
  - eapply admission_status_load_value; eassumption.
  - unfold admission_stopped_env; admission_route.
    eapply store_next; [exact I|apply certified_if_edge with
      (v:=Val.of_bool (negb (admission_is_stopped word)))
      (b:=negb (admission_is_stopped word))|].
    + apply old_expression_value; eapply value_unary.
      * eapply value_binary.
        -- eapply value_binary; [apply value_temp;apply PTree.gss|apply value_int|reflexivity].
        -- apply value_int.
        -- reflexivity.
      * change (sem_unary_operation Onotbool (Val.of_bool (admission_is_stopped word)) tint memory =
          Some (Val.of_bool (negb (admission_is_stopped word)))).
        destruct (admission_is_stopped word); reflexivity.
    + destruct (admission_is_stopped word); reflexivity.
    + destruct (admission_is_stopped word); cbn.
      * admission_route; apply store_done; exact I.
      * apply store_done; exact I.
Qed.

Theorem admission_stopsig_guard e le memory k status offset word :
  le!_status = Some (Vptr status offset) ->
  Mem.loadv Mint32 memory (Vptr status offset) = Some (Vint word) ->
  store_path admission_ge (fun _ => True)
    (State f_admit_child (admission_tail 3 (fn_body f_admit_child)) k e le memory)
    (if admission_is_sigstop word then 6 else 5)%nat
    (if admission_is_sigstop word then
      State f_admit_child (admission_tail 4 (fn_body f_admit_child)) k e
        (admission_stopsig_env le word) memory
     else State f_admit_child admission_failure
       (Kseq (admission_tail 4 (fn_body f_admit_child)) k) e
       (admission_stopsig_env le word) memory).
Proof.
  intros STATUS LOAD.
  change (admission_tail 3 (fn_body f_admit_child)) with
    (Ssequence admission_stopsig (admission_tail 4 (fn_body f_admit_child))).
  rewrite (proj2 (proj2 admission_status_guards_source)).
  replace (if admission_is_sigstop word then 6 else 5)%nat with
    (S (S (S (S (S (if admission_is_sigstop word then 1 else 0))))))
    by (destruct (admission_is_sigstop word); reflexivity).
  admission_route; admission_route; admission_set.
  - eapply admission_status_load_value; eassumption.
  - unfold admission_stopsig_env; admission_route.
    eapply store_next; [exact I|apply certified_if_edge with
      (v:=Val.of_bool (negb (admission_is_sigstop word)))
      (b:=negb (admission_is_sigstop word))|].
    + apply old_expression_value; eapply value_binary.
      * eapply value_binary.
        -- eapply value_binary; [apply value_temp;apply PTree.gss|apply value_int|reflexivity].
        -- apply value_int.
        -- reflexivity.
      * apply value_int.
      * reflexivity.
    + destruct (admission_is_sigstop word); reflexivity.
    + destruct (admission_is_sigstop word); cbn.
      * admission_route; apply store_done; exact I.
      * apply store_done; exact I.
Qed.
