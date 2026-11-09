(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: The helper waits for its supplied child and owned status slot. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll ErrorNumber.
From EntryNative Require Import EntrySource.
From EntryProcess Require Import ProcessMachine ProcessAllocation ProcessStructure ProcessReturns.
Import ListNotations.
Open Scope Z_scope.

Definition admission_wait_body := match admission_wait with Sloop body _ => body | _ => Sskip end.
Definition admission_wait_condition := match admission_wait with Sloop _ condition => condition | _ => Sskip end.
Definition admission_after_wait := admission_tail 1 (fn_body f_admit_child).

Theorem admission_wait_source : admission_wait =
  Sloop
    (Ssequence
      (Scall (Some _t'3) (Evar _waitpid (Tfunction [tint;tptr tint;tint] tint cc_default))
        [Etempvar _child tint;Etempvar _status (tptr tint);Econst_int Int.zero tint])
      (Sset _got (Etempvar _t'3 tint))) admission_wait_condition.
Proof. reflexivity. Qed.

Definition admission_wait_cont k :=
  Kloop1 admission_wait_body admission_wait_condition (Kseq admission_after_wait k).

Definition admission_wait_call_cont e le k :=
  Kcall (Some _t'3) f_admit_child e le
    (Kseq (Sset _got (Etempvar _t'3 tint)) (admission_wait_cont k)).

Theorem admission_wait_global : exists pointer,
  Genv.find_symbol admission_ge _waitpid = Some pointer /\
  Genv.find_funct admission_ge (Vptr pointer Ptrofs.zero) = Some process_wait_definition.
Proof. eexists; split; vm_compute; reflexivity. Qed.

Lemma admission_wait_call_source e le memory child status offset k :
  e!_waitpid = None -> le!_child = Some (Vint child) ->
  le!_status = Some (Vptr status offset) ->
  store_path admission_ge (fun _ => True)
    (State f_admit_child admission_wait (Kseq admission_after_wait k) e le memory) 3
    (Callstate process_wait_definition [Vint child;Vptr status offset;Vint Int.zero]
      (admission_wait_call_cont e le k) memory).
Proof.
  intros UNSHADOWED CHILD STATUS.
  destruct admission_wait_global as [pointer [SYMBOL FUNCTION]].
  rewrite admission_wait_source.
  admission_route; admission_route.
  eapply store_next; [exact I|eapply certified_call_edge|apply store_done; exact I].
  - reflexivity.
  - apply old_expression_value; eapply value_function;
      [exact UNSHADOWED|exact SYMBOL|reflexivity].
  - eapply cons_argument_values with (v:=Vint child).
    + apply old_expression_value,value_temp; exact CHILD.
    + reflexivity.
    + eapply cons_argument_values with (v:=Vptr status offset).
      * apply old_expression_value,value_temp; exact STATUS.
      * reflexivity.
      * eapply cons_argument_values with (v:=Vint Int.zero).
        -- apply old_expression_value,value_int.
        -- reflexivity.
        -- apply no_argument_values.
  - exact FUNCTION.
  - reflexivity.
Qed.

Theorem admission_start_to_wait before locals after child cgroup status offset k :
  alloc_variables admission_ge empty_env before (fn_vars f_admit_child) (admission_env locals) after ->
  store_path admission_ge (fun _ => True)
    (Callstate (Internal f_admit_child) [Vint child;Vint cgroup;Vptr status offset] k before) 5
    (Callstate process_wait_definition [Vint child;Vptr status offset;Vint Int.zero]
      (admission_wait_call_cont (admission_env locals)
        (admission_parameters child cgroup (Vptr status offset)) k) after).
Proof.
  intro ALLOC.
  eapply store_next; [exact I|apply function_entry_source_edge,admission_function_entry; exact ALLOC|].
  rewrite admission_source_phases.
  admission_route.
  apply admission_wait_call_source.
  - apply admission_nonlocal_binding; discriminate.
  - unfold admission_parameters; WriteAll.lookup.
  - unfold admission_parameters; WriteAll.lookup.
Qed.

Definition admission_errno_call := Scall (Some _t'2)
  (Evar ___errno_location (Tfunction [] (tptr tint) cc_default)) [].
Definition admission_retry_test := Sifthenelse (Etempvar _t'1 tint) Sskip Sbreak.

Theorem admission_wait_condition_source : admission_wait_condition =
  Ssequence
    (Sifthenelse (Ebinop Olt (Etempvar _got tint) (Econst_int Int.zero tint) tint)
      (Ssequence admission_errno_call
        (Ssequence (Sset _t'12 (Ederef (Etempvar _t'2 (tptr tint)) tint))
          (Sset _t'1 (Ecast (Ebinop Oeq (Etempvar _t'12 tint)
            (Econst_int (Int.repr 4) tint) tint) tbool))))
      (Sset _t'1 (Econst_int Int.zero tint))) admission_retry_test.
Proof. reflexivity. Qed.

Lemma admission_nonnegative_test memory word : 0 <= Int.signed word ->
  sem_binary_operation admission_ge Olt (Vint word) tint (Vint Int.zero) tint memory =
    Some (Vint Int.zero).
Proof.
  intro NONNEGATIVE.
  change (Some (Val.of_bool (Int.lt word Int.zero)) = Some (Vint Int.zero)).
  unfold Int.lt. change
    (Some (Val.of_bool (if zlt (Int.signed word) 0 then true else false)) = Some (Vint Int.zero)).
  destruct (zlt (Int.signed word) 0); [lia|reflexivity].
Qed.

Lemma admission_break_loop2_edge ge fn first second k e le memory :
  edge ge (State fn Sbreak (Kloop2 first second k) e le memory)
    (State fn Sskip k e le memory).
Proof. intros; structural_edge. Qed.

Definition admission_wait_return_env le got :=
  PTree.set _t'1 (Vint Int.zero) (PTree.set _got (Vint got) (PTree.set _t'3 (Vint got) le)).

Theorem admission_wait_positive_source e le memory got k : 0 <= Int.signed got ->
  store_path admission_ge (fun _ => True)
    (Returnstate (Vint got) (admission_wait_call_cont e le k) memory) 11
    (State f_admit_child admission_after_wait k e (admission_wait_return_env le got) memory).
Proof.
  intro NONNEGATIVE; unfold admission_wait_call_cont,admission_wait_cont,admission_wait_return_env.
  admission_route; admission_route.
  admission_set; [apply old_expression_value,value_temp; apply PTree.gss|].
  admission_route. rewrite admission_wait_condition_source.
  admission_route.
  eapply store_next; [exact I|apply certified_if_edge with (v:=Vint Int.zero) (b:=false)|].
  - apply old_expression_value; eapply value_binary.
    + apply value_temp; apply PTree.gss.
    + apply value_int.
    + apply admission_nonnegative_test; exact NONNEGATIVE.
  - reflexivity.
  - admission_set; [apply old_expression_value,value_int|].
    admission_route. unfold admission_retry_test.
    eapply store_next; [exact I|apply certified_if_edge with (v:=Vint Int.zero) (b:=false)|].
    + apply old_expression_value,value_temp; apply PTree.gss.
    + reflexivity.
    + eapply store_next; [exact I|apply unchanged_store_edge,admission_break_loop2_edge|].
      admission_route. apply store_done; exact I.
Qed.

Definition admission_wait_saved le got :=
  PTree.set _got (Vint got) (PTree.set _t'3 (Vint got) le).
Definition admission_errno_tail := Ssequence
  (Sset _t'12 (Ederef (Etempvar _t'2 (tptr tint)) tint))
  (Sset _t'1 (Ecast (Ebinop Oeq (Etempvar _t'12 tint)
    (Econst_int (Int.repr 4) tint) tint) tbool)).
Definition admission_errno_cont e le k :=
  Kcall (Some _t'2) f_admit_child e (admission_wait_saved le Int.mone)
    (Kseq admission_errno_tail (Kseq admission_retry_test
      (Kloop2 admission_wait_body admission_wait_condition (Kseq admission_after_wait k)))).

Theorem admission_errno_global : exists pointer,
  Genv.find_symbol admission_ge ___errno_location = Some pointer /\
  Genv.find_funct admission_ge (Vptr pointer Ptrofs.zero) =
    Some (External errno_function [] (tptr tint) cc_default).
Proof. eexists; split; vm_compute; reflexivity. Qed.

Theorem admission_wait_failed_to_errno e le memory k : e!___errno_location = None ->
  store_path admission_ge (fun _ => True)
    (Returnstate (Vint Int.mone) (admission_wait_call_cont e le k) memory) 8
    (Callstate (External errno_function [] (tptr tint) cc_default) []
      (admission_errno_cont e le k) memory).
Proof.
  intro UNSHADOWED; destruct admission_errno_global as [pointer [SYMBOL FUNCTION]].
  unfold admission_wait_call_cont,admission_wait_cont,admission_errno_cont,admission_wait_saved.
  admission_route; admission_route.
  admission_set; [apply old_expression_value,value_temp; apply PTree.gss|].
  admission_route; rewrite admission_wait_condition_source.
  admission_route.
  eapply store_next; [exact I|apply certified_if_edge with (v:=Vint Int.one) (b:=true)|].
  - apply old_expression_value; WriteAll.expression.
  - reflexivity.
  - admission_route. unfold admission_errno_call.
    eapply store_next; [exact I|eapply certified_call_edge|apply store_done; exact I].
    + reflexivity.
    + apply old_expression_value; eapply value_function;
        [exact UNSHADOWED|exact SYMBOL|reflexivity].
    + apply no_argument_values.
    + exact FUNCTION.
    + reflexivity.
Qed.

Definition admission_errno_env cell le error :=
  PTree.set _t'1 (Val.of_bool (Int.eq error (Int.repr 4)))
    (PTree.set _t'12 (Vint error)
      (PTree.set _t'2 (Vptr (tls_block cell) (Ptrofs.repr (tls_offset cell)))
        (admission_wait_saved le Int.mone))).

Theorem admission_errno_retry_source cell e le memory k error :
  initialized_errno cell memory error ->
  store_path admission_ge (fun _ => True)
    (Returnstate (Vptr (tls_block cell) (Ptrofs.repr (tls_offset cell)))
      (admission_errno_cont e le k) memory) 9
    (State f_admit_child
      (if Int.eq error (Int.repr 4) then admission_wait else Sskip)
      (Kseq admission_after_wait k) e (admission_errno_env cell le error) memory).
Proof.
  intro ERRNO; unfold admission_errno_cont,admission_errno_tail,admission_errno_env.
  admission_route; admission_route; admission_route.
  admission_set.
  - apply old_expression_value; eapply value_load.
    + apply value_temp; apply PTree.gss.
    + reflexivity.
    + apply ErrorNumber.errno_load; exact ERRNO.
  - admission_route; admission_set.
    + apply old_expression_value; eapply value_cast with
        (v:=Val.of_bool (Int.eq error (Int.repr 4)))
        (w:=Val.of_bool (Int.eq error (Int.repr 4))).
      * eapply value_binary; [apply value_temp; apply PTree.gss|apply value_int|reflexivity].
      * change (sem_cast (Val.of_bool (Int.eq error (Int.repr 4))) tint tbool memory =
          Some (Val.of_bool (Int.eq error (Int.repr 4)))).
        destruct (Int.eq error (Int.repr 4)); reflexivity.
    + admission_route; unfold admission_retry_test.
      eapply store_next; [exact I|apply certified_if_edge with
        (v:=Val.of_bool (Int.eq error (Int.repr 4))) (b:=Int.eq error (Int.repr 4))|].
      * apply old_expression_value,value_temp; apply PTree.gss.
      * destruct (Int.eq error (Int.repr 4)); reflexivity.
      * destruct (Int.eq error (Int.repr 4)); cbn.
        -- admission_route; apply store_done; exact I.
        -- eapply store_next; [exact I|apply unchanged_store_edge,admission_break_loop2_edge|].
           apply store_done; exact I.
Qed.
