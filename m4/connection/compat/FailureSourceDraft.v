(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-callers.control: The actual child-failure preparation and reporting continuations. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Slice IO Machine ClightSteps WriteAll StoreSteps WriteBytes Writers LocalAccess CallAccess CallPaths Library LibraryMachine Fault.
Import ListNotations.
Open Scope Z_scope.

Definition failure_ge := Clight.globalenv Slice.prog.
Definition failure_env local := PTree.set _bytes (local,tarray tuchar 8) empty_env.
Definition failure_temps fd stage error := PTree.set _error (Vint error)
  (PTree.set _stage (Vint stage) (PTree.set _fd (Vint fd) (create_undef_temps (fn_temps f_fail_child)))).
Definition failure_initial fd stage error k m := Callstate (Internal f_fail_child)
  [Vint fd; Vint stage; Vint error] k m.
Definition failure_put_stage := Scall None
  (Evar _put32 (Tfunction [tptr tuchar;tuint] tvoid cc_default))
  [Evar _bytes (tarray tuchar 8); Etempvar _stage tuint].
Definition failure_put_error := Scall None
  (Evar _put32 (Tfunction [tptr tuchar;tuint] tvoid cc_default))
  [Ebinop Oadd (Evar _bytes (tarray tuchar 8)) (Econst_int (Int.repr 4) tint) (tptr tuchar);
   Ecast (Etempvar _error tint) tuint].
Definition failure_fault id literal len := Scall (Some id)
  (Evar _fault (Tfunction [tptr tschar] tint cc_default)) [Evar literal (tarray tschar len)].
Definition failure_exit := Scall None (Evar __exit (Tfunction [tint] tvoid cc_default))
  [Econst_int (Int.repr 125) tint].
Definition failure_write := Scall None
  (Evar _write_all (Tfunction [tint;tptr tvoid;tulong] tint cc_default))
  [Etempvar _fd tint; Evar _bytes (tarray tuchar 8); Etempvar _t'2 tint].
Definition failure_size := Sifthenelse (Etempvar _t'1 tint)
  (Sset _t'2 (Ecast (Econst_int (Int.repr 3) tint) tint))
  (Sset _t'2 (Ecast (Econst_int (Int.repr 8) tint) tint)).
Definition failure_after_drop := Sifthenelse (Eunop Onotbool (Etempvar _t'3 tint) tint)
  (Ssequence (Ssequence (failure_fault _t'1 ___stringlit_9 12) failure_size) failure_write) Sskip.
Definition failure_tail := Ssequence
  (Ssequence (failure_fault _t'3 ___stringlit_8 11) failure_after_drop) failure_exit.
Definition failure_drop_cont local fd stage error k := Kcall (Some _t'3) f_fail_child
  (failure_env local) (failure_temps fd stage error) (Kseq failure_after_drop (Kseq failure_exit k)).
Definition failure_drop_state local fd stage error drop k m :=
  Callstate (Internal f_fault) [Vptr drop Ptrofs.zero] (failure_drop_cont local fd stage error k) m.

Theorem failure_source_body : fn_body f_fail_child =
  Ssequence failure_put_stage (Ssequence failure_put_error failure_tail).
Proof. reflexivity. Qed.

Lemma failure_entry : forall m allocated local fd stage error k,
  Mem.alloc m 0 8 = (allocated,local) ->
  store_edge failure_ge (failure_initial fd stage error k m)
    (State f_fail_child (fn_body f_fail_child) k (failure_env local)
      (failure_temps fd stage error) allocated).
Proof.
  intros. apply function_entry_source_edge. constructor.
  - repeat (apply list_norepet_cons; [simpl; intuition discriminate|]); apply list_norepet_nil.
  - repeat (apply list_norepet_cons; [simpl; intuition discriminate|]); apply list_norepet_nil.
  - unfold list_disjoint, var_names; cbn. intros a b A B.
    destruct A as [A|[A|[A|A]]]; destruct B as [B|[B|[B|B]]]; try contradiction; subst; discriminate.
  - econstructor; [exact H|constructor].
  - reflexivity.
Qed.

Ltac failure_expression := first
  [apply old_expression_value; WriteAll.expression
  | eapply location_read_value;
    [eapply local_location_value; unfold failure_env; WriteAll.lookup|
     apply deref_loc_reference; reflexivity]
  | eapply binary_expression_value; [failure_expression|failure_expression|reflexivity]
  | eapply cast_expression_value; [failure_expression|reflexivity]].
Ltac failure_arguments := first
  [apply no_argument_values
  | eapply cons_argument_values; [failure_expression|reflexivity|failure_arguments]].
Ltac failure_route := eapply store_next; [assumption|apply unchanged_store_edge; WriteAll.structural|].
Ltac failure_call symbol function := eapply store_next; [assumption| |];
  [eapply certified_call_edge; [reflexivity|
    apply old_expression_value; eapply value_function;
      [unfold failure_env; cbn; reflexivity|exact symbol|reflexivity]|
    failure_arguments|exact function|reflexivity]|].

Theorem failure_prepare_source_path : forall (P : mem -> Prop)
    m allocated local first built fd stage error drop pb fb k,
  is_call_cont k ->
  Genv.find_symbol failure_ge _put32 = Some pb ->
  Genv.find_funct failure_ge (Vptr pb Ptrofs.zero) = Some (Internal f_put32) ->
  Genv.find_symbol failure_ge _fault = Some fb ->
  Genv.find_funct failure_ge (Vptr fb Ptrofs.zero) = Some (Internal f_fault) ->
  Genv.find_symbol failure_ge ___stringlit_8 = Some drop ->
  Mem.alloc m 0 8 = (allocated,local) ->
  byte_writes allocated local 0 (put32_values stage) first ->
  byte_writes first local 4 (put32_values error) built ->
  P m -> P allocated -> P first -> P built ->
  (forall after, writer_prefix allocated local 0 (put32_values stage) after -> P after) ->
  (forall after, writer_prefix first local 4 (put32_values error) after -> P after) ->
  store_path failure_ge P (failure_initial fd stage error k m) 96
    (failure_drop_state local fd stage error drop k built).
Proof.
  intros P m allocated local first built fd stage error drop pb fb k CALL PS PF FS FF DS
    ALLOC FIRST SECOND PM PA P1 P2 PRES1 PRES2.
  eapply store_next; [exact PM|apply failure_entry; exact ALLOC|].
  rewrite failure_source_body. failure_route. unfold failure_put_stage. unfold failure_temps.
  failure_call PS PF.
  eapply store_path_trans with (n:=42%nat).
  - eapply store_path_consequence; [eapply put32_source_path; [exact I|vm_compute; congruence|exact FIRST]|exact PRES1].
  - repeat failure_route. unfold failure_put_error. failure_call PS PF.
    change (Ptrofs.add Ptrofs.zero (Ptrofs.mul (Ptrofs.of_int (Int.repr 4)) (Ptrofs.repr 1))) with (Ptrofs.repr 4).
    eapply store_path_trans with (n:=42%nat).
    + eapply store_path_consequence; [eapply put32_source_path; [exact I|vm_compute; congruence|exact SECOND]|exact PRES2].
    + repeat failure_route. unfold failure_tail. repeat failure_route.
      unfold failure_fault. eapply store_next; [exact P2| |].
      * eapply certified_call_edge; [reflexivity|
          apply old_expression_value; eapply value_function;
          [unfold failure_env; cbn; reflexivity|exact FS|reflexivity]| |exact FF|reflexivity].
        eapply cons_argument_values.
        -- apply old_expression_value; eapply value_function;
           [unfold failure_env; cbn; reflexivity|exact DS|reflexivity].
        -- reflexivity.
        -- apply no_argument_values.
      * apply store_done; exact P2.
Qed.

Definition failure_write_cont local le k := Kcall None f_fail_child
  (failure_env local) le (Kseq failure_exit k).
Definition failure_exit_cont local le k := Kcall None f_fail_child (failure_env local) le k.

Theorem failure_exit_symbol : exists b,
  Genv.find_symbol failure_ge __exit = Some b /\
  Genv.find_funct failure_ge (Vptr b Ptrofs.zero) = Some exit_definition.
Proof. eexists; split; vm_compute; reflexivity. Qed.

Theorem failure_after_write_path : forall local le k value m,
  store_path failure_ge (fun after => after = m)
    (Returnstate value (failure_write_cont local le k) m) 3
    (Callstate exit_definition [Vint (Int.repr 125)] (failure_exit_cont local le k) m).
Proof.
  intros local le k value m. destruct failure_exit_symbol as [eb [ES EF]].
  unfold failure_write_cont, failure_exit_cont, failure_exit.
  eapply store_next; [reflexivity|apply unchanged_store_edge; apply edge_returnstate|].
  eapply store_next; [reflexivity|apply unchanged_store_edge; apply edge_skip_seq|].
  eapply store_next; [reflexivity| |].
  - eapply certified_call_edge; [reflexivity|
      apply old_expression_value; eapply value_function;
      [unfold failure_env; cbn; reflexivity|exact ES|reflexivity]|
      failure_arguments|exact EF|reflexivity].
  - apply store_done; reflexivity.
Qed.
