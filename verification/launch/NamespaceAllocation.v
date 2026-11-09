(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: The actual local fork helper allocates its own fresh socketpair array. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine StoreSteps LocalAccess WriteAll FreshMemory ReceiverAllocation.
From EntryNative Require Import EntrySource.
From EntryNamespace Require Import NamespaceStructure.
Import ListNotations.
Open Scope Z_scope.

Record ChildArguments := {
  child_input : int;
  child_output : int;
  child_errors : int;
  child_peer_pointer : val;
  child_pid_pointer : val
}.

Definition child_parameters (args : ChildArguments) : temp_env :=
  PTree.set _child (child_pid_pointer args)
    (PTree.set _peer (child_peer_pointer args)
      (PTree.set _errors (Vint (child_errors args))
        (PTree.set _output (Vint (child_output args))
          (PTree.set _input (Vint (child_input args))
            (create_undef_temps (fn_temps f_create_entry_child)))))).

Definition child_values (args : ChildArguments) : list val :=
  [Vint (child_input args);Vint (child_output args);Vint (child_errors args);
   child_peer_pointer args;child_pid_pointer args].
Definition child_env pair := PTree.set _pair (pair,tarray tint 2) empty_env.
Definition child_allocations before pair after := local_allocations before [(pair,8)] after.

Theorem child_local_bindings pair : (child_env pair)!_pair = Some (pair,tarray tint 2).
Proof. unfold child_env; apply PTree.gss. Qed.

Theorem child_nonlocal_bindings pair id : id <> _pair -> (child_env pair)!id = None.
Proof. intro DIFFERENT; unfold child_env; rewrite PTree.gso by congruence; apply PTree.gempty. Qed.

Theorem child_parameter_bindings args :
  (child_parameters args)!_input = Some (Vint (child_input args)) /\
  (child_parameters args)!_output = Some (Vint (child_output args)) /\
  (child_parameters args)!_errors = Some (Vint (child_errors args)) /\
  (child_parameters args)!_peer = Some (child_peer_pointer args) /\
  (child_parameters args)!_child = Some (child_pid_pointer args).
Proof. unfold child_parameters; repeat split; WriteAll.lookup. Qed.

Theorem child_allocate before : exists pair after,
  alloc_variables namespace_ge empty_env before (fn_vars f_create_entry_child) (child_env pair) after /\
  child_allocations before pair after.
Proof.
  destruct (Mem.alloc before 0 8) as [after pair] eqn:ALLOC; exists pair,after; split.
  - unfold child_env; cbn [fn_vars f_create_entry_child]; econstructor; [exact ALLOC|constructor].
  - unfold child_allocations; econstructor; [exact ALLOC|constructor].
Qed.

Theorem child_function_entry before pair after args :
  alloc_variables namespace_ge empty_env before (fn_vars f_create_entry_child) (child_env pair) after ->
  function_entry2 namespace_ge f_create_entry_child (child_values args) before
    (child_env pair) (child_parameters args) after.
Proof.
  intro ALLOC; constructor.
  - repeat (apply list_norepet_cons; [cbn; intuition discriminate|]); apply list_norepet_nil.
  - repeat (apply list_norepet_cons; [cbn; intuition discriminate|]); apply list_norepet_nil.
  - unfold list_disjoint,var_names; cbn; intros a b A B.
    repeat destruct A as [A|A]; try contradiction; subst a;
      repeat destruct B as [B|B]; try contradiction; subst b; discriminate.
  - exact ALLOC.
  - reflexivity.
Qed.

Theorem child_entry_allocates before args k : exists pair after,
  store_edge namespace_ge
    (Callstate (Internal f_create_entry_child) (child_values args) k before)
    (State f_create_entry_child (fn_body f_create_entry_child) k
      (child_env pair) (child_parameters args) after) /\
  child_allocations before pair after /\ old_memory before after /\
  ~Mem.valid_block before pair /\ Mem.range_perm after pair 0 8 Cur Freeable.
Proof.
  destruct (child_allocate before) as [pair [after [VARS ALLOC]]]; exists pair,after.
  split; [apply function_entry_source_edge,child_function_entry; exact VARS|].
  split; [exact ALLOC|].
  split; [eapply local_allocations_unchanged; exact ALLOC|].
  pose proof (local_allocations_objects _ _ _ ALLOC) as OBJECTS.
  inversion OBJECTS; subst; exact H1.
Qed.

Theorem child_allocation_preserves_load before pair after chunk object offset value :
  child_allocations before pair after -> Mem.load chunk before object offset = Some value ->
  Mem.load chunk after object offset = Some value.
Proof.
  intros ALLOC LOAD; eapply old_memory_load; [eapply local_allocations_unchanged; exact ALLOC|exact LOAD].
Qed.

Record NamespaceAllocationResult := {
  namespace_allocated_env : env;
  namespace_allocated_memory : mem;
  namespace_allocated_objects : list (block*Z)
}.

Fixpoint namespace_allocate_variables (variables : list (ident*type)) e before
    : NamespaceAllocationResult :=
  match variables with
  | [] => {|namespace_allocated_env:=e;namespace_allocated_memory:=before;
            namespace_allocated_objects:=[]|}
  | (id,ty)::rest =>
      let '(middle,object) := Mem.alloc before 0 (sizeof namespace_ge ty) in
      let result := namespace_allocate_variables rest (PTree.set id (object,ty) e) middle in
      {|namespace_allocated_env:=namespace_allocated_env result;
        namespace_allocated_memory:=namespace_allocated_memory result;
        namespace_allocated_objects:=(object,sizeof namespace_ge ty)::namespace_allocated_objects result|}
  end.

Theorem namespace_allocate_variables_source variables e before :
  let result := namespace_allocate_variables variables e before in
  alloc_variables namespace_ge e before variables (namespace_allocated_env result)
    (namespace_allocated_memory result) /\
  local_allocations before (namespace_allocated_objects result) (namespace_allocated_memory result).
Proof.
  revert e before; induction variables as [|[id ty] rest IH]; intros e before; cbn.
  - split; constructor.
  - destruct (Mem.alloc before 0 (sizeof (prog_comp_env EntrySource.prog) ty))
      as [middle object] eqn:ALLOC; cbn.
    destruct (IH (PTree.set id (object,ty) e) middle) as [VARS OBJECTS].
    split.
    + econstructor; [exact ALLOC|exact VARS].
    + econstructor; [exact ALLOC|exact OBJECTS].
Qed.

Definition namespace_parameter_env parentfd report input output errors : temp_env :=
  PTree.set _errors (Vint errors) (PTree.set _output (Vint output)
    (PTree.set _input (Vint input) (PTree.set _report (Vint report)
      (PTree.set _parentfd (Vint parentfd) (create_undef_temps (fn_temps f_namespace_init)))))).

Theorem namespace_function_entry before e after parentfd report input output errors :
  alloc_variables namespace_ge empty_env before (fn_vars f_namespace_init) e after ->
  function_entry2 namespace_ge f_namespace_init
    [Vint parentfd;Vint report;Vint input;Vint output;Vint errors] before e
    (namespace_parameter_env parentfd report input output errors) after.
Proof.
  intro ALLOC; constructor.
  - repeat (apply list_norepet_cons; [cbn; intuition discriminate|]); apply list_norepet_nil.
  - repeat (apply list_norepet_cons; [cbn; intuition discriminate|]); apply list_norepet_nil.
  - unfold list_disjoint,var_names; cbn; intros a b A B.
    repeat destruct A as [A|A]; try contradiction; subst a;
      repeat destruct B as [B|B]; try contradiction; subst b; discriminate.
  - exact ALLOC.
  - reflexivity.
Qed.

Theorem namespace_entry_allocates before parentfd report input output errors k :
  exists e after objects,
    store_edge namespace_ge
      (Callstate (Internal f_namespace_init) [Vint parentfd;Vint report;Vint input;Vint output;Vint errors] k before)
      (State f_namespace_init (fn_body f_namespace_init) k e
        (namespace_parameter_env parentfd report input output errors) after) /\
    local_allocations before objects after /\ old_memory before after /\
    NoDup (map fst objects) /\
    Forall (fun object => ~Mem.valid_block before (fst object) /\
      Mem.range_perm after (fst object) 0 (snd object) Cur Freeable) objects.
Proof.
  pose proof (namespace_allocate_variables_source (fn_vars f_namespace_init) empty_env before)
    as [VARS ALLOC].
  do 3 eexists; split; [apply function_entry_source_edge,namespace_function_entry; exact VARS|].
  split; [exact ALLOC|]. split; [eapply local_allocations_unchanged; exact ALLOC|].
  split; [eapply local_allocations_distinct|eapply local_allocations_objects]; exact ALLOC.
Qed.

Local Opaque namespace_ge.

Theorem namespace_allocate_away variables e before id :
  ~In id (map fst variables) ->
  (namespace_allocated_env (namespace_allocate_variables variables e before))!id = e!id.
Proof.
  revert e before; induction variables as [|[name ty] rest IH]; intros e before ABSENT; cbn; [reflexivity|].
  destruct (Mem.alloc before 0 (sizeof namespace_ge ty))
    as [middle object] eqn:ALLOC; cbn.
  rewrite IH by (cbn in ABSENT; intuition).
  rewrite PTree.gso by (cbn in ABSENT; intuition); reflexivity.
Qed.

Theorem namespace_allocate_bindings variables e before :
  NoDup (map fst variables) ->
  forall id ty, In (id,ty) variables ->
  exists object,
    (namespace_allocated_env (namespace_allocate_variables variables e before))!id = Some (object,ty) /\
    In (object,sizeof namespace_ge ty)
      (namespace_allocated_objects (namespace_allocate_variables variables e before)).
Proof.
  revert e before; induction variables as [|[name type] rest IH]; intros e before DISTINCT id ty MEMBER;
    [contradiction|].
  inversion DISTINCT; subst.
  cbn; destruct (Mem.alloc before 0 (sizeof namespace_ge type))
    as [middle object] eqn:ALLOC; cbn.
  destruct MEMBER as [SAME|MEMBER].
  - inversion SAME; subst id ty; exists object; split; [|left; reflexivity].
    rewrite namespace_allocate_away by exact H1; apply PTree.gss.
  - destruct (IH (PTree.set name (object,type) e) middle H2 id ty MEMBER)
      as [other [BINDING OBJECT]].
    exists other; split; [exact BINDING|right; exact OBJECT].
Qed.

Theorem namespace_current_local_distinctness : NoDup (map fst (fn_vars f_namespace_init)).
Proof. repeat (constructor; [cbn; intuition discriminate|]); constructor. Qed.

Theorem namespace_owned_local_from_entry before id ty :
  In (id,ty) (fn_vars f_namespace_init) ->
  let result := namespace_allocate_variables (fn_vars f_namespace_init) empty_env before in
  exists object,
    (namespace_allocated_env result)!id = Some (object,ty) /\
    ~Mem.valid_block before object /\
    Mem.range_perm (namespace_allocated_memory result) object 0 (sizeof namespace_ge ty) Cur Freeable.
Proof.
  intro MEMBER.
  destruct (namespace_allocate_bindings _ empty_env before namespace_current_local_distinctness id ty MEMBER)
    as [object [BINDING OBJECT]].
  exists object; split; [exact BINDING|].
  destruct (namespace_allocate_variables_source (fn_vars f_namespace_init) empty_env before) as [VARS ALLOC].
  pose proof (local_allocations_objects _ _ _ ALLOC) as OWNED.
  rewrite Forall_forall in OWNED; exact (OWNED _ OBJECT).
Qed.

Definition namespace_env_valid (m : mem) (e : env) :=
  forall id object ty, e!id = Some (object,ty) -> Mem.valid_block m object.
Definition namespace_env_injective (e : env) :=
  forall id other object ty another other_ty,
    e!id = Some (object,ty) -> e!other = Some (another,other_ty) ->
    id <> other -> object <> another.

Lemma namespace_extend_env_valid before after e id object ty size :
  Mem.alloc before 0 size = (after,object) -> namespace_env_valid before e ->
  namespace_env_valid after (PTree.set id (object,ty) e).
Proof.
  intros ALLOC OLD query target target_ty LOOKUP.
  destruct (peq query id) as [SAME|DIFFERENT]; subst.
  - rewrite PTree.gss in LOOKUP; inversion LOOKUP; subst target.
    eapply Mem.valid_new_block; exact ALLOC.
  - rewrite PTree.gso in LOOKUP by exact DIFFERENT.
    eapply Mem.valid_block_alloc; [exact ALLOC|eapply OLD; exact LOOKUP].
Qed.

Lemma namespace_extend_env_injective before after e id object ty size :
  Mem.alloc before 0 size = (after,object) -> namespace_env_valid before e ->
  namespace_env_injective e -> namespace_env_injective (PTree.set id (object,ty) e).
Proof.
  intros ALLOC VALID INJECTIVE first second left left_ty right right_ty LEFT RIGHT DISTINCT SAME.
  pose proof (Mem.fresh_block_alloc _ _ _ _ _ ALLOC) as FRESH.
  destruct (peq first id) as [FIRST|FIRST]; destruct (peq second id) as [SECOND|SECOND].
  - subst first second; contradiction.
  - subst first; rewrite PTree.gss in LEFT.
    rewrite PTree.gso in RIGHT by exact SECOND; apply FRESH.
    assert (OBJECT : object = right) by congruence; rewrite OBJECT; eapply VALID; exact RIGHT.
  - subst second; rewrite PTree.gss in RIGHT.
    rewrite PTree.gso in LEFT by exact FIRST; apply FRESH.
    assert (OBJECT : object = left) by congruence; rewrite OBJECT; eapply VALID; exact LEFT.
  - rewrite PTree.gso in LEFT by exact FIRST; rewrite PTree.gso in RIGHT by exact SECOND.
    exact (INJECTIVE first second left left_ty right right_ty LEFT RIGHT DISTINCT SAME).
Qed.

Theorem namespace_allocations_preserve_env_shape variables e before result after :
  alloc_variables namespace_ge e before variables result after ->
  namespace_env_valid before e -> namespace_env_injective e ->
  namespace_env_valid after result /\ namespace_env_injective result.
Proof.
  intro ALLOC; induction ALLOC; intros VALID INJECTIVE; [auto|].
  apply IHALLOC.
  - eapply namespace_extend_env_valid; eassumption.
  - eapply namespace_extend_env_injective; eassumption.
Qed.

Theorem namespace_entry_has_distinct_local_objects before :
  namespace_env_injective
    (namespace_allocated_env (namespace_allocate_variables (fn_vars f_namespace_init) empty_env before)).
Proof.
  destruct (namespace_allocate_variables_source (fn_vars f_namespace_init) empty_env before) as [VARS ALLOC].
  assert (EMPTY_VALID : namespace_env_valid before empty_env).
  { intros id object ty LOOKUP; rewrite PTree.gempty in LOOKUP; discriminate. }
  assert (EMPTY_INJECTIVE : namespace_env_injective empty_env).
  { intros id other object ty another other_ty LEFT; rewrite PTree.gempty in LEFT; discriminate. }
  exact (proj2 (namespace_allocations_preserve_env_shape _ _ _ _ _ VARS EMPTY_VALID EMPTY_INJECTIVE)).
Qed.
