(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Actual function entry allocates fresh owned handoff storage. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine StoreSteps LocalAccess WriteAll FreshMemory ReceiverAllocation.
From EntryNative Require Import EntrySource NativeHandoffArguments.
Import ListNotations.
Open Scope Z_scope.

Record HandoffLocals := {
  handoff_handles : block;
  handoff_uid : block;
  handoff_numbers : block;
  handoff_encoded : block;
  handoff_arguments : block;
  handoff_environment : block
}.

Definition handoff_locals_env (b : HandoffLocals) : env :=
  PTree.set EntrySource._env (handoff_environment b, tarray (tptr tschar) 2)
    (PTree.set EntrySource._args (handoff_arguments b, tarray (tptr tschar) 74)
      (PTree.set EntrySource._encoded (handoff_encoded b, tulong)
        (PTree.set EntrySource._numbers (handoff_numbers b, tarray (tarray tschar 32) 4)
          (PTree.set EntrySource._uid (handoff_uid b, tarray tschar 32)
            (PTree.set EntrySource._handles (handoff_handles b, tarray tint 4) empty_env))))).

Definition handoff_parameter_env input output errors failure : temp_env :=
  PTree.set EntrySource._failure (Vint failure)
    (PTree.set EntrySource._errors (Vint errors)
      (PTree.set EntrySource._output (Vint output)
        (PTree.set EntrySource._input (Vint input)
          (create_undef_temps (fn_temps EntrySource.f_guest))))).

Definition handoff_objects (b : HandoffLocals) : list (block * Z) :=
  [(handoff_handles b,16); (handoff_uid b,32); (handoff_numbers b,128);
   (handoff_encoded b,8); (handoff_arguments b,592); (handoff_environment b,16)].

Definition handoff_allocations before b after := local_allocations before (handoff_objects b) after.

Definition handoff_local_ownership before b after :=
  old_memory before after /\ NoDup (map fst (handoff_objects b)) /\
  Forall (fun object => ~Mem.valid_block before (fst object) /\
    Mem.range_perm after (fst object) 0 (snd object) Cur Freeable) (handoff_objects b).

Theorem handoff_local_bindings b :
  (handoff_locals_env b) ! EntrySource._handles = Some (handoff_handles b,tarray tint 4) /\
  (handoff_locals_env b) ! EntrySource._uid = Some (handoff_uid b,tarray tschar 32) /\
  (handoff_locals_env b) ! EntrySource._numbers = Some (handoff_numbers b,tarray (tarray tschar 32) 4) /\
  (handoff_locals_env b) ! EntrySource._encoded = Some (handoff_encoded b,tulong) /\
  (handoff_locals_env b) ! EntrySource._args = Some (handoff_arguments b,tarray (tptr tschar) 74) /\
  (handoff_locals_env b) ! EntrySource._env = Some (handoff_environment b,tarray (tptr tschar) 2).
Proof. unfold handoff_locals_env; repeat split; WriteAll.lookup. Qed.

Theorem handoff_nonlocal_binding b id :
  ~In id [EntrySource._handles;EntrySource._uid;EntrySource._numbers;
          EntrySource._encoded;EntrySource._args;EntrySource._env] ->
  (handoff_locals_env b) ! id = None.
Proof.
  intros ABSENT; unfold handoff_locals_env.
  repeat (rewrite PTree.gso by (cbn in ABSENT; intuition congruence)).
  apply PTree.gempty.
Qed.

Definition handoff_global_names : list ident :=
  [EntrySource._policy__1; EntrySource._run_uid; EntrySource._root_path; EntrySource._mode;
   EntrySource._preflight; EntrySource._entry_decimal; EntrySource._number;
   EntrySource._entry_descriptor_flags; EntrySource._strcmp; EntrySource._fail_child;
   EntrySource._execve; EntrySource._error_number; EntrySource.___stringlit_1;
   EntrySource.___stringlit_111; EntrySource.___stringlit_112;
   EntrySource.___stringlit_113; EntrySource.___stringlit_114].

Theorem handoff_globals_unshadowed b :
  Forall (fun id => (handoff_locals_env b) ! id = None) handoff_global_names.
Proof.
  unfold handoff_global_names; repeat constructor;
    apply handoff_nonlocal_binding; cbn; intuition discriminate.
Qed.

Theorem handoff_parameter_bindings input output errors failure :
  (handoff_parameter_env input output errors failure) ! EntrySource._input = Some (Vint input) /\
  (handoff_parameter_env input output errors failure) ! EntrySource._output = Some (Vint output) /\
  (handoff_parameter_env input output errors failure) ! EntrySource._errors = Some (Vint errors) /\
  (handoff_parameter_env input output errors failure) ! EntrySource._failure = Some (Vint failure).
Proof. unfold handoff_parameter_env; repeat split; WriteAll.lookup. Qed.

Theorem handoff_allocation_ownership before b after : handoff_allocations before b after ->
  handoff_local_ownership before b after.
Proof.
  intros ALLOC; unfold handoff_allocations in ALLOC; unfold handoff_local_ownership.
  split; [eapply local_allocations_unchanged; exact ALLOC|].
  split; [eapply local_allocations_distinct|eapply local_allocations_objects]; exact ALLOC.
Qed.

Theorem handoff_allocation_preserves_permissions before b after : handoff_allocations before b after ->
  forall object offset kind permission, Mem.perm before object offset kind permission ->
    Mem.perm after object offset kind permission.
Proof. intros ALLOC; eapply local_allocations_perms; exact ALLOC. Qed.

Theorem handoff_allocation_preserves_load before b after chunk object offset value :
  handoff_allocations before b after -> Mem.load chunk before object offset = Some value ->
  Mem.load chunk after object offset = Some value.
Proof.
  intros ALLOC LOAD; eapply old_memory_load; [eapply local_allocations_unchanged; exact ALLOC|exact LOAD].
Qed.

Theorem handoff_allocated_separate_old before b after object size old :
  handoff_allocations before b after -> In (object,size) (handoff_objects b) ->
  Mem.valid_block before old -> object <> old.
Proof.
  intros ALLOC MEMBER VALID SAME; subst object.
  pose proof (local_allocations_objects _ _ _ ALLOC) as OBJECTS.
  rewrite Forall_forall in OBJECTS; destruct (OBJECTS _ MEMBER) as [FRESH OWN].
  exact (FRESH VALID).
Qed.

Theorem handoff_allocate_locals before : exists b after,
  alloc_variables handoff_ge empty_env before (fn_vars EntrySource.f_guest) (handoff_locals_env b) after /\
  handoff_allocations before b after.
Proof.
  destruct (Mem.alloc before 0 16) as [m1 handles] eqn:A1.
  destruct (Mem.alloc m1 0 32) as [m2 uid] eqn:A2.
  destruct (Mem.alloc m2 0 128) as [m3 numbers] eqn:A3.
  destruct (Mem.alloc m3 0 8) as [m4 encoded] eqn:A4.
  destruct (Mem.alloc m4 0 592) as [m5 arguments] eqn:A5.
  destruct (Mem.alloc m5 0 16) as [after environment] eqn:A6.
  exists {|handoff_handles:=handles;handoff_uid:=uid;handoff_numbers:=numbers;
           handoff_encoded:=encoded;handoff_arguments:=arguments;handoff_environment:=environment|},after.
  split.
  - unfold handoff_locals_env; cbn [fn_vars EntrySource.f_guest].
    econstructor; [exact A1|]. econstructor; [exact A2|]. econstructor; [exact A3|].
    econstructor; [exact A4|]. econstructor; [exact A5|]. econstructor; [exact A6|]. constructor.
  - unfold handoff_allocations,handoff_objects; cbn.
    econstructor; [exact A1|]. econstructor; [exact A2|]. econstructor; [exact A3|].
    econstructor; [exact A4|]. econstructor; [exact A5|]. econstructor; [exact A6|]. constructor.
Qed.

Theorem handoff_function_entry before b after input output errors failure :
  alloc_variables handoff_ge empty_env before (fn_vars EntrySource.f_guest) (handoff_locals_env b) after ->
  function_entry2 handoff_ge EntrySource.f_guest [Vint input;Vint output;Vint errors;Vint failure]
    before (handoff_locals_env b) (handoff_parameter_env input output errors failure) after.
Proof.
  intros ALLOC; constructor.
  - repeat (apply list_norepet_cons; [cbn; intuition discriminate|]); apply list_norepet_nil.
  - repeat (apply list_norepet_cons; [cbn; intuition discriminate|]); apply list_norepet_nil.
  - unfold list_disjoint,var_names; cbn. intros a c A C.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; try contradiction; subst; discriminate.
  - exact ALLOC.
  - reflexivity.
Qed.

Theorem handoff_entry_allocates before input output errors failure k : exists b after,
  store_edge handoff_ge
    (Callstate (Internal EntrySource.f_guest) [Vint input;Vint output;Vint errors;Vint failure] k before)
    (State EntrySource.f_guest (fn_body EntrySource.f_guest) k (handoff_locals_env b)
      (handoff_parameter_env input output errors failure) after) /\
  handoff_allocations before b after /\ handoff_local_ownership before b after.
Proof.
  destruct (handoff_allocate_locals before) as [b [after [VARS ALLOC]]].
  exists b,after; split.
  - apply function_entry_source_edge, handoff_function_entry; exact VARS.
  - split; [exact ALLOC|apply handoff_allocation_ownership; exact ALLOC].
Qed.
