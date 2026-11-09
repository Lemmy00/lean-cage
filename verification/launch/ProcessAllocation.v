(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: The actual stopped-child helper allocates fresh owned PID/readback storage. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine StoreSteps LocalAccess WriteAll FreshMemory ReceiverAllocation.
From EntryNative Require Import EntrySource.
Import ListNotations.
Open Scope Z_scope.

Definition admission_ge := Clight.globalenv EntrySource.prog.

Record AdmissionLocals := {
  admission_text : block;
  admission_encoded : block
}.

Definition admission_env (locals : AdmissionLocals) : env :=
  PTree.set EntrySource._encoded_pid (admission_encoded locals, tulong)
    (PTree.set EntrySource._pidtext (admission_text locals, tarray tschar 32) empty_env).

Definition admission_parameters child cgroup status : temp_env :=
  PTree.set EntrySource._status status
    (PTree.set EntrySource._cgfd (Vint cgroup)
      (PTree.set EntrySource._child (Vint child)
        (create_undef_temps (fn_temps EntrySource.f_admit_child)))).

Definition admission_objects (locals : AdmissionLocals) : list (block * Z) :=
  [(admission_text locals,32); (admission_encoded locals,8)].

Definition admission_allocations before locals after :=
  local_allocations before (admission_objects locals) after.

Theorem admission_local_bindings locals :
  (admission_env locals)!EntrySource._pidtext = Some (admission_text locals,tarray tschar 32) /\
  (admission_env locals)!EntrySource._encoded_pid = Some (admission_encoded locals,tulong).
Proof. unfold admission_env; split; WriteAll.lookup. Qed.

Theorem admission_nonlocal_binding locals id :
  id <> EntrySource._pidtext -> id <> EntrySource._encoded_pid ->
  (admission_env locals)!id = None.
Proof.
  intros TEXT ENCODED; unfold admission_env.
  repeat rewrite PTree.gso by congruence. apply PTree.gempty.
Qed.

Theorem admission_parameter_bindings child cgroup status :
  (admission_parameters child cgroup status)!EntrySource._child = Some (Vint child) /\
  (admission_parameters child cgroup status)!EntrySource._cgfd = Some (Vint cgroup) /\
  (admission_parameters child cgroup status)!EntrySource._status = Some status.
Proof. unfold admission_parameters; repeat split; WriteAll.lookup. Qed.

Theorem admission_allocation_objects before locals after :
  admission_allocations before locals after ->
  old_memory before after /\ NoDup (map fst (admission_objects locals)) /\
  Forall (fun object => ~Mem.valid_block before (fst object) /\
    Mem.range_perm after (fst object) 0 (snd object) Cur Freeable) (admission_objects locals).
Proof.
  intro ALLOC; split; [eapply local_allocations_unchanged; exact ALLOC|].
  split; [eapply local_allocations_distinct|eapply local_allocations_objects]; exact ALLOC.
Qed.

Theorem admission_allocate before : exists locals after,
  alloc_variables admission_ge empty_env before (fn_vars EntrySource.f_admit_child)
    (admission_env locals) after /\ admission_allocations before locals after.
Proof.
  destruct (Mem.alloc before 0 32) as [middle text] eqn:TEXT.
  destruct (Mem.alloc middle 0 8) as [after encoded] eqn:ENCODED.
  exists {|admission_text := text; admission_encoded := encoded|},after; split.
  - unfold admission_env; cbn [fn_vars EntrySource.f_admit_child].
    econstructor; [exact TEXT|]. econstructor; [exact ENCODED|]. constructor.
  - unfold admission_allocations,admission_objects; cbn.
    econstructor; [exact TEXT|]. econstructor; [exact ENCODED|]. constructor.
Qed.

Theorem admission_function_entry before locals after child cgroup status :
  alloc_variables admission_ge empty_env before (fn_vars EntrySource.f_admit_child)
    (admission_env locals) after ->
  function_entry2 admission_ge EntrySource.f_admit_child [Vint child;Vint cgroup;status]
    before (admission_env locals) (admission_parameters child cgroup status) after.
Proof.
  intro ALLOC; constructor.
  - repeat (apply list_norepet_cons; [cbn; intuition discriminate|]); apply list_norepet_nil.
  - repeat (apply list_norepet_cons; [cbn; intuition discriminate|]); apply list_norepet_nil.
  - unfold list_disjoint,var_names; cbn. intros a b A B.
    repeat destruct A as [A|A]; try contradiction; subst a;
      repeat destruct B as [B|B]; try contradiction; subst b; discriminate.
  - exact ALLOC.
  - reflexivity.
Qed.

Theorem admission_entry_allocates before child cgroup status k : exists locals after,
  store_edge admission_ge
    (Callstate (Internal EntrySource.f_admit_child) [Vint child;Vint cgroup;status] k before)
    (State EntrySource.f_admit_child (fn_body EntrySource.f_admit_child) k (admission_env locals)
      (admission_parameters child cgroup status) after) /\
  admission_allocations before locals after.
Proof.
  destruct (admission_allocate before) as [locals [after [VARS ALLOC]]].
  exists locals,after; split; [apply function_entry_source_edge, admission_function_entry; exact VARS|exact ALLOC].
Qed.
