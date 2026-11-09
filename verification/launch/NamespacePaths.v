(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Actual channel/fork source paths retain the real caller continuation. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine.
From EntryNamespace Require Import NamespaceMachine NamespaceStructure NamespaceAllocation.
Import ListNotations.
Open Scope Z_scope.

Definition namespace_source_event :=
  namespace_process (process_entry (entry_library (LibraryMachine.original_event (source_step E0)))).
Definition namespace_symbol id :=
  match Genv.find_symbol namespace_ge id with Some object => object | None => 1%positive end.

Theorem namespace_steps_append ge cell before prefix middle suffix after :
  namespace_steps ge cell before prefix middle -> namespace_steps ge cell middle suffix after ->
  namespace_steps ge cell before (prefix++suffix) after.
Proof. intros PREFIX SUFFIX; induction PREFIX; cbn; eauto using namespace_steps_cons. Qed.

Ltac child_memory := first [exact I|reflexivity|left;reflexivity|right;reflexivity].
Ltac child_route := eapply store_next; [child_memory|apply unchanged_store_edge; WriteAll.structural|].
Ltac child_set := eapply store_next; [child_memory|apply certified_set_edge|].
Ltac child_function := apply old_expression_value; eapply value_function;
  [apply child_nonlocal_bindings; discriminate|reflexivity|reflexivity].
Ltac child_argument := eapply cons_argument_values;
  [apply old_expression_value; WriteAll.expression|reflexivity|].
Ltac child_call id := eapply certified_call_edge with (vf:=Vptr (namespace_symbol id) Ptrofs.zero);
  [reflexivity|child_function| |reflexivity|reflexivity].

Theorem namespace_store_path_actual ge cell (P : mem -> Prop) start count last :
  store_path ge P start count last ->
  namespace_steps ge cell (live start) (repeat namespace_source_event count) (live last).
Proof.
  intro PATH; induction PATH; cbn; [constructor|].
  econstructor; [|exact IHPATH].
  apply namespace_process_step,process_entry_step,entry_library_step,LibraryMachine.original_step.
  apply internal; destruct H0 as [IN [STEP REST]]; assumption.
Qed.

Theorem namespace_store_path_decomposition ge cell (P : mem -> Prop) start count last :
  store_path ge P start count last ->
  forall events target, namespace_steps ge cell (live start) events target ->
  (exists rest, events = repeat namespace_source_event count ++ rest /\
    namespace_steps ge cell (live last) rest target) \/
  (exists used current remaining, (count = used + remaining)%nat /\
    events = repeat namespace_source_event used /\ target = live current /\
    store_path ge P current remaining last) \/
  (exists used memory, (used < count)%nat /\
    events = repeat namespace_source_event used ++
      [namespace_process (process_entry (entry_library (LibraryMachine.original_event loss_step)))] /\
    target = dead memory /\ P memory).
Proof.
  intro SCRIPT; induction SCRIPT as [state GOOD|state next count last GOOD EDGE SCRIPT IH];
    intros events target RUN.
  - left; exists events; cbn; auto.
  - destruct events as [|event rest].
    + inversion RUN; subst. right; left. exists 0%nat,state,(S count); cbn.
      repeat split; auto. econstructor; eassumption.
    + inversion RUN; subst.
      match goal with STEP : namespace_step _ _ _ _ _ |- _ =>
        destruct (namespace_store_edge_cases _ _ _ _ _ _ EDGE STEP)
          as [[EVENT TARGET]|[EVENT TARGET]] end; subst.
      * match goal with TAIL : namespace_steps _ _ (live next) _ _ |- _ =>
          destruct (IH _ _ TAIL) as [[suffix [EVENTS TAILRUN]]|
            [[used [current [remaining [COUNT [EVENTS [TARGET PATH]]]]]]|
             [used [memory [COUNT [EVENTS [TARGET PM]]]]]]] end.
        -- left; exists suffix; cbn; split; [rewrite EVENTS; reflexivity|exact TAILRUN].
        -- right; left; exists (S used),current,remaining; cbn.
           split; [lia|]. split; [rewrite EVENTS; reflexivity|]. auto.
        -- right; right; exists (S used),memory; cbn.
           split; [lia|]. split; [rewrite EVENTS; reflexivity|]. auto.
      * match goal with TAIL : namespace_steps _ _ (dead _) _ _ |- _ =>
          destruct (namespace_dead_steps _ _ _ _ _ TAIL) as [EVENTS TARGET'] end; subst.
        right; right; exists 0%nat,(memory_of state); cbn; auto with arith.
Qed.

Lemma child_array_value pair le m :
  expression_value namespace_ge (child_env pair) le m (Evar _pair (tarray tint 2))
    (Vptr pair Ptrofs.zero).
Proof.
  eapply location_read_value; [apply local_location_value,child_local_bindings|].
  apply deref_loc_reference; reflexivity.
Qed.

Lemma child_pair_slot_value pair le m index value : 0 <= index <= 1 ->
  Mem.load Mint32 m pair (4*index) = Some (Vint value) ->
  expression_value namespace_ge (child_env pair) le m
    (Ederef (Ebinop Oadd (Evar _pair (tarray tint 2))
      (Econst_int (Int.repr index) tint) (tptr tint)) tint) (Vint value).
Proof.
  intros INDEX LOAD; eapply location_read_value with (b:=pair) (ofs:=Ptrofs.repr(4*index)).
  - apply pointer_location_value; eapply binary_expression_value.
    + apply child_array_value.
    + apply old_expression_value,value_int.
    + assert (index=0 \/ index=1) by lia; destruct H; subst index; reflexivity.
  - eapply deref_loc_value; [reflexivity|].
    unfold Mem.loadv; rewrite Ptrofs.unsigned_repr by
      (change Ptrofs.max_unsigned with 18446744073709551615; lia).
    destruct (zle _ _) as [BOUND|IMPOSSIBLE]; [exact LOAD|].
    exfalso; change (4*index+4 > 18446744073709551616) in IMPOSSIBLE; lia.
Qed.

Definition child_socket_guard :=
  match child_socket with Ssequence _ guard => guard | _ => Sskip end.
Definition child_socket_cont pair le k :=
  Kcall (Some _t'2) f_create_entry_child (child_env pair) le
    (Kseq child_socket_guard (Kseq (child_tail 1 (fn_body f_create_entry_child)) k)).

Theorem child_socket_source pair le m k :
  store_path namespace_ge (fun current => current = m)
    (State f_create_entry_child (fn_body f_create_entry_child) k (child_env pair) le m) 3
    (Callstate namespace_pair_definition
      [Vint (Int.repr 1);Vint (Int.repr 524289);Vint Int.zero;Vptr pair Ptrofs.zero]
      (child_socket_cont pair le k) m).
Proof.
  unfold child_socket_cont,child_socket_guard,child_socket,child_phase,child_tail; cbn [fn_body].
  child_route; child_route.
  eapply store_next; [child_memory|child_call _socketpair|apply store_done; child_memory].
  child_argument; child_argument; child_argument.
  eapply cons_argument_values; [apply child_array_value|reflexivity|apply no_argument_values].
Qed.

Theorem child_socket_success_source pair le m k :
  store_path namespace_ge (fun current => current = m)
    (Returnstate (Vint Int.zero) (child_socket_cont pair le k) m) 4
    (State f_create_entry_child (child_tail 1 (fn_body f_create_entry_child)) k
      (child_env pair) (PTree.set _t'2 (Vint Int.zero) le) m).
Proof.
  unfold child_socket_cont,child_socket_guard,child_socket,child_phase,child_tail; cbn [fn_body].
  child_route; child_route.
  eapply store_next; [child_memory|apply certified_if_edge with (v:=Vint Int.zero) (b:=false)|].
  - apply old_expression_value,value_temp; apply PTree.gss.
  - reflexivity.
  - child_route; apply store_done; child_memory.
Qed.

Definition child_duplicate_set := Sset _failure (Etempvar _t'3 tint).
Definition child_duplicate_call_env le second := PTree.set _t'15 (Vint second) le.
Definition child_duplicate_cont pair le second k :=
  Kcall (Some _t'3) f_create_entry_child (child_env pair) (child_duplicate_call_env le second)
    (Kseq child_duplicate_set (Kseq (child_tail 2 (fn_body f_create_entry_child)) k)).

Theorem child_duplicate_source pair le m k second :
  Mem.load Mint32 m pair 4 = Some (Vint second) ->
  store_path namespace_ge (fun current => current = m)
    (State f_create_entry_child (child_tail 1 (fn_body f_create_entry_child)) k (child_env pair) le m) 6
    (Callstate namespace_duplicate_definition [Vint second;Vint (Int.repr 60)]
      (child_duplicate_cont pair le second k) m).
Proof.
  intros SECOND; unfold child_duplicate_cont,child_duplicate_call_env,child_duplicate_set,child_tail;
    cbn [fn_body]; child_route; child_route; child_route; child_set.
  - apply child_pair_slot_value; [lia|exact SECOND].
  - child_route; eapply store_next; [child_memory|child_call _entry_duplicate_above|apply store_done; child_memory].
    child_argument; child_argument; apply no_argument_values.
Qed.

Definition child_duplicate_return_env le second failure :=
  PTree.set _failure (Vint failure)
    (PTree.set _t'3 (Vint failure) (child_duplicate_call_env le second)).

Theorem child_duplicate_return_source pair le m k second failure :
  store_path namespace_ge (fun current => current = m)
    (Returnstate (Vint failure) (child_duplicate_cont pair le second k) m) 4
    (State f_create_entry_child (child_tail 2 (fn_body f_create_entry_child)) k
      (child_env pair) (child_duplicate_return_env le second failure) m).
Proof.
  unfold child_duplicate_cont,child_duplicate_set,child_duplicate_return_env;
    child_route; child_route; child_set.
  - apply old_expression_value,value_temp; apply PTree.gss.
  - child_route; apply store_done; child_memory.
Qed.

Definition child_original_close_env le second := PTree.set _t'14 (Vint second) le.
Definition child_original_close_cont pair le second k :=
  Kcall None f_create_entry_child (child_env pair) (child_original_close_env le second)
    (Kseq (child_tail 3 (fn_body f_create_entry_child)) k).

Theorem child_close_original_source pair le m k second :
  Mem.load Mint32 m pair 4 = Some (Vint second) ->
  store_path namespace_ge (fun current => current = m)
    (State f_create_entry_child (child_tail 2 (fn_body f_create_entry_child)) k (child_env pair) le m) 5
    (Callstate LibraryMachine.close_definition [Vint second]
      (child_original_close_cont pair le second k) m).
Proof.
  intro SECOND; unfold child_original_close_cont,child_original_close_env,child_tail;
    cbn [fn_body]; child_route; child_route; child_set.
  - apply child_pair_slot_value; [lia|exact SECOND].
  - child_route; eapply store_next; [child_memory|child_call _close|apply store_done; child_memory].
    child_argument; apply no_argument_values.
Qed.

Theorem child_close_original_return_source pair le m k second returned :
  store_path namespace_ge (fun current => current = m)
    (Returnstate returned (child_original_close_cont pair le second k) m) 2
    (State f_create_entry_child (child_tail 3 (fn_body f_create_entry_child)) k
      (child_env pair) (child_original_close_env le second) m).
Proof.
  unfold child_original_close_cont,child_original_close_env; child_route; child_route;
    apply store_done; child_memory.
Qed.

Theorem child_duplicate_nonnegative_source pair le m k failure :
  le!_failure = Some (Vint failure) -> 0 <= Int.signed failure ->
  store_path namespace_ge (fun current => current = m)
    (State f_create_entry_child (child_tail 3 (fn_body f_create_entry_child)) k (child_env pair) le m) 3
    (State f_create_entry_child (child_tail 4 (fn_body f_create_entry_child)) k (child_env pair) le m).
Proof.
  intros FAILURE NONNEGATIVE; unfold child_tail; cbn [fn_body]; child_route.
  eapply store_next; [child_memory|apply certified_if_edge with (v:=Vint Int.zero) (b:=false)|].
  - eapply binary_expression_value; [apply old_expression_value,value_temp; exact FAILURE|
      apply old_expression_value,value_int|].
    change (Some (Val.of_bool (Int.lt failure Int.zero)) = Some (Vint Int.zero)).
    unfold Int.lt; rewrite Int.signed_zero; destruct (zlt (Int.signed failure) 0); [lia|reflexivity].
  - reflexivity.
  - child_route; apply store_done; child_memory.
Qed.

Definition child_mask_guard := match child_mask with Ssequence _ guard => guard | _ => Sskip end.
Definition child_mask_cont pair le k :=
  Kcall (Some _t'6) f_create_entry_child (child_env pair) le
    (Kseq child_mask_guard (Kseq (child_tail 5 (fn_body f_create_entry_child)) k)).

Theorem child_mask_source pair le m k :
  store_path namespace_ge (fun current => current = m)
    (State f_create_entry_child (child_tail 4 (fn_body f_create_entry_child)) k (child_env pair) le m) 3
    (Callstate namespace_mask_definition [Vlong Int64.mone] (child_mask_cont pair le k) m).
Proof.
  unfold child_mask_cont,child_mask_guard,child_mask,child_phase,child_tail; cbn [fn_body].
  child_route; child_route.
  eapply store_next; [child_memory|child_call _entry_signal_mask|apply store_done; child_memory].
  eapply cons_argument_values with (v:=Vlong Int64.mone); [|reflexivity|apply no_argument_values].
  split; [apply eval_Econst_long|].
  intros other VALUE; inversion VALUE; subst; try reflexivity.
  match goal with LVALUE : eval_lvalue _ _ _ _ _ _ _ _ |- _ => inversion LVALUE end.
Qed.

Theorem child_mask_success_source pair le m k :
  store_path namespace_ge (fun current => current = m)
    (Returnstate (Vlong Int64.zero) (child_mask_cont pair le k) m) 4
    (State f_create_entry_child (child_tail 5 (fn_body f_create_entry_child)) k
      (child_env pair) (PTree.set _t'6 (Vlong Int64.zero) le) m).
Proof.
  unfold child_mask_cont,child_mask_guard,child_mask,child_phase,child_tail; cbn [fn_body].
  child_route; child_route.
  eapply store_next; [child_memory|apply certified_if_edge with (v:=Vlong Int64.zero) (b:=false)|].
  - apply old_expression_value,value_temp; apply PTree.gss.
  - reflexivity.
  - child_route; apply store_done; child_memory.
Qed.

Definition child_default_guard := match child_signals with Ssequence _ guard=>guard|_=>Sskip end.
Definition child_default_cont pair le k :=
  Kcall (Some _t'8) f_create_entry_child (child_env pair) le
    (Kseq child_default_guard (Kseq (child_tail 6 (fn_body f_create_entry_child)) k)).

Theorem child_default_source pair le m k :
  store_path namespace_ge (fun current=>current=m)
    (State f_create_entry_child (child_tail 5 (fn_body f_create_entry_child)) k (child_env pair) le m) 3
    (Callstate namespace_default_definition [Vint (Int.repr 17)] (child_default_cont pair le k) m).
Proof.
  unfold child_default_cont,child_default_guard,child_signals,child_phase,child_tail; cbn [fn_body].
  child_route; child_route.
  eapply store_next; [child_memory|child_call _entry_signal_default|apply store_done; child_memory].
  child_argument; apply no_argument_values.
Qed.

Theorem child_default_success_source pair le m k :
  store_path namespace_ge (fun current=>current=m)
    (Returnstate (Vlong Int64.zero) (child_default_cont pair le k) m) 4
    (State f_create_entry_child (child_tail 6 (fn_body f_create_entry_child)) k
      (child_env pair) (PTree.set _t'8 (Vlong Int64.zero) le) m).
Proof.
  unfold child_default_cont,child_default_guard,child_signals,child_phase,child_tail; cbn [fn_body].
  child_route; child_route.
  eapply store_next; [child_memory|apply certified_if_edge with (v:=Vlong Int64.zero) (b:=false)|].
  - apply old_expression_value,value_temp; apply PTree.gss.
  - reflexivity.
  - child_route; apply store_done; child_memory.
Qed.

Definition child_publish_peer_env le first := PTree.set _t'10 (Vint first) le.

Theorem child_publish_peer_source pair le before after k first peer offset :
  Mem.load Mint32 before pair 0 = Some (Vint first) ->
  le!_peer = Some (Vptr peer offset) ->
  Mem.storev Mint32 before (Vptr peer offset) (Vint first) = Some after ->
  store_path namespace_ge (fun current => current = before \/ current = after)
    (State f_create_entry_child (child_tail 6 (fn_body f_create_entry_child)) k (child_env pair) le before) 6
    (State f_create_entry_child (child_tail 7 (fn_body f_create_entry_child)) k
      (child_env pair) (child_publish_peer_env le first) after).
Proof.
  intros FIRST PEER STORE; unfold child_tail; cbn [fn_body]; child_route; child_route; child_set.
  - apply child_pair_slot_value; [lia|exact FIRST].
  - child_route; eapply store_next; [child_memory| |].
    + eapply assignment_source_edge with (v:=Vint first) (w:=Vint first).
      * apply pointer_location_value; apply old_expression_value,value_temp; WriteAll.lookup.
      * apply old_expression_value,value_temp; apply PTree.gss.
      * reflexivity.
      * eapply assign_loc_value; [reflexivity|exact STORE].
    + child_route; apply store_done; child_memory.
Qed.

Definition child_fork_set := Sset _forked (Etempvar _t'9 tint).
Definition child_fork_cont pair le k :=
  Kcall (Some _t'9) f_create_entry_child (child_env pair) le
    (Kseq child_fork_set (Kseq (child_tail 8 (fn_body f_create_entry_child)) k)).

Theorem child_fork_source pair le m k :
  store_path namespace_ge (fun current => current = m)
    (State f_create_entry_child (child_tail 7 (fn_body f_create_entry_child)) k (child_env pair) le m) 3
    (Callstate namespace_fork_definition [] (child_fork_cont pair le k) m).
Proof.
  unfold child_fork_cont,child_fork_set,child_tail; cbn [fn_body].
  child_route; child_route.
  eapply store_next; [child_memory|child_call _fork|apply store_done; child_memory].
  apply no_argument_values.
Qed.

Definition child_fork_return_env le returned :=
  PTree.set _forked (Vint returned) (PTree.set _t'9 (Vint returned) le).

Theorem child_fork_return_source pair le m k returned :
  store_path namespace_ge (fun current => current = m)
    (Returnstate (Vint returned) (child_fork_cont pair le k) m) 4
    (State f_create_entry_child (child_tail 8 (fn_body f_create_entry_child)) k
      (child_env pair) (child_fork_return_env le returned) m).
Proof.
  unfold child_fork_cont,child_fork_set,child_fork_return_env.
  child_route; child_route; child_set.
  - apply old_expression_value,value_temp; apply PTree.gss.
  - child_route; apply store_done; child_memory.
Qed.

Theorem child_publish_pid_source pair le before after k returned object offset :
  le!_forked = Some (Vint returned) -> le!_child = Some (Vptr object offset) ->
  Mem.storev Mint32 before (Vptr object offset) (Vint returned) = Some after ->
  store_path namespace_ge (fun current => current = before \/ current = after)
    (State f_create_entry_child (child_tail 8 (fn_body f_create_entry_child)) k (child_env pair) le before) 3
    (State f_create_entry_child (child_tail 9 (fn_body f_create_entry_child)) k (child_env pair) le after).
Proof.
  intros FORKED CHILD STORE; unfold child_tail; cbn [fn_body]; child_route.
  eapply store_next; [child_memory| |].
  - eapply assignment_source_edge with (v:=Vint returned) (w:=Vint returned).
    + apply pointer_location_value; apply old_expression_value,value_temp; exact CHILD.
    + apply old_expression_value,value_temp; exact FORKED.
    + reflexivity.
    + eapply assign_loc_value; [reflexivity|exact STORE].
  - child_route; apply store_done; child_memory.
Qed.

Definition child_guest_cont pair le k :=
  Kcall None f_create_entry_child (child_env pair) le
    (Kseq (child_tail 10 (fn_body f_create_entry_child)) k).

Theorem child_select_guest_source pair le m k input output errors failure :
  le!_forked = Some (Vint Int.zero) ->
  le!_input = Some (Vint input) -> le!_output = Some (Vint output) ->
  le!_errors = Some (Vint errors) -> le!_failure = Some (Vint failure) ->
  store_path namespace_ge (fun current => current = m)
    (State f_create_entry_child (child_tail 9 (fn_body f_create_entry_child)) k (child_env pair) le m) 3
    (Callstate (Internal f_guest) [Vint input;Vint output;Vint errors;Vint failure]
      (child_guest_cont pair le k) m).
Proof.
  intros FORKED INPUT OUTPUT ERRORS FAILURE.
  unfold child_guest_cont,child_tail; cbn [fn_body]; child_route.
  eapply store_next; [child_memory|apply certified_if_edge with (v:=Vint Int.one) (b:=true)|].
  - eapply binary_expression_value; [apply old_expression_value,value_temp; exact FORKED|
      apply old_expression_value,value_int|reflexivity].
  - reflexivity.
  - eapply store_next; [child_memory|child_call _guest|apply store_done; child_memory].
    child_argument; child_argument; child_argument; child_argument; apply no_argument_values.
Qed.

Theorem child_select_parent_source pair le m k returned :
  le!_forked = Some (Vint returned) -> returned <> Int.zero ->
  store_path namespace_ge (fun current => current = m)
    (State f_create_entry_child (child_tail 9 (fn_body f_create_entry_child)) k (child_env pair) le m) 3
    (State f_create_entry_child (child_tail 10 (fn_body f_create_entry_child)) k (child_env pair) le m).
Proof.
  intros FORKED NONZERO; unfold child_tail; cbn [fn_body]; child_route.
  eapply store_next; [child_memory|apply certified_if_edge with (v:=Vint Int.zero) (b:=false)|].
  - eapply binary_expression_value; [apply old_expression_value,value_temp; exact FORKED|
      apply old_expression_value,value_int|].
    change (Some (Val.of_bool (Int.eq returned Int.zero)) = Some (Vint Int.zero)).
    rewrite Int.eq_false by exact NONZERO; reflexivity.
  - reflexivity.
  - child_route; apply store_done; child_memory.
Qed.

Definition child_failure_close_cont pair le k :=
  Kcall None f_create_entry_child (child_env pair) le (Kseq child_return k).

Theorem child_close_failure_source pair le m k failure :
  le!_failure = Some (Vint failure) ->
  store_path namespace_ge (fun current => current = m)
    (State f_create_entry_child (child_tail 10 (fn_body f_create_entry_child)) k (child_env pair) le m) 2
    (Callstate LibraryMachine.close_definition [Vint failure] (child_failure_close_cont pair le k) m).
Proof.
  intro FAILURE; unfold child_failure_close_cont,child_return,child_phase,child_tail; cbn [fn_body].
  child_route; eapply store_next; [child_memory|child_call _close|apply store_done; child_memory].
  child_argument; apply no_argument_values.
Qed.

Theorem child_finish_source pair le before after k returned :
  Mem.free_list before (blocks_of_env namespace_ge (child_env pair)) = Some after ->
  store_path namespace_ge (fun current => current = before \/ current = after)
    (Returnstate returned (child_failure_close_cont pair le k) before) 3
    (Returnstate (Vint Int.zero) (call_cont k) after).
Proof.
  intro FREE; unfold child_failure_close_cont,child_return,child_phase,child_tail; cbn [fn_body].
  child_route; child_route.
  eapply store_next; [child_memory|eapply certified_local_return_edge|apply store_done; child_memory].
  - apply old_expression_value,value_int.
  - reflexivity.
  - exact FREE.
Qed.

Lemma child_free_locals pair before : Mem.range_perm before pair 0 8 Cur Freeable ->
  exists after, Mem.free_list before (blocks_of_env namespace_ge (child_env pair)) = Some after.
Proof.
  intro OWN; destruct (Mem.range_perm_free _ _ _ _ OWN) as [after FREE]; exists after.
  change (Mem.free_list before [(pair,0,8)] = Some after); cbn; rewrite FREE; reflexivity.
Qed.

Definition child_socket_error_env le returned := PTree.set _t'2 (Vint returned) le.
Definition child_socket_error_cont pair le returned k :=
  Kcall (Some _t'1) f_create_entry_child (child_env pair) (child_socket_error_env le returned)
    (Kseq (Sreturn (Some (Etempvar _t'1 tint)))
      (Kseq (child_tail 1 (fn_body f_create_entry_child)) k)).

Theorem child_socket_failure_source pair le m k returned : returned <> Int.zero ->
  store_path namespace_ge (fun current => current = m)
    (Returnstate (Vint returned) (child_socket_cont pair le k) m) 5
    (Callstate (Internal f_error_number) [] (child_socket_error_cont pair le returned k) m).
Proof.
  intro NONZERO; unfold child_socket_cont,child_socket_guard,child_socket_error_cont,
    child_socket_error_env,child_socket,child_phase,child_tail; cbn [fn_body].
  child_route; child_route.
  eapply store_next; [child_memory|apply certified_if_edge with (v:=Vint returned) (b:=true)|].
  - apply old_expression_value,value_temp; apply PTree.gss.
  - change (Some (negb (Int.eq returned Int.zero)) = Some true).
    rewrite Int.eq_false by exact NONZERO; reflexivity.
  - child_route; eapply store_next; [child_memory|child_call _error_number|apply store_done; child_memory].
    apply no_argument_values.
Qed.

Theorem child_socket_error_return_source pair le before after k returned error :
  Mem.free_list before (blocks_of_env namespace_ge (child_env pair)) = Some after ->
  store_path namespace_ge (fun current => current = before \/ current = after)
    (Returnstate (Vint error) (child_socket_error_cont pair le returned k) before) 3
    (Returnstate (Vint error) (call_cont k) after).
Proof.
  intro FREE; unfold child_socket_error_cont; child_route; child_route.
  eapply store_next; [child_memory|eapply certified_local_return_edge|apply store_done; child_memory].
  - apply old_expression_value,value_temp; apply PTree.gss.
  - reflexivity.
  - exact FREE.
Qed.
