(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.acceptance: Prepared guest inputs and canonical parent locals admit useful entry. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import IO Machine ErrorNumber Library ProcessEffects FreshMemory ReceiverAllocation StoreSteps WriteAll.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffArguments NativeHandoffInput
  NativeHandoffInputWitness NativeHandoffInitial.
From EntryProcess Require Import ProcessMachine ProcessGlobalCalls ProcessAdmissionWitness.
From EntryReporting Require Import ResultLayout.
From EntryNamespace Require Import NamespaceMachine NamespaceStructure NamespaceAllocation NamespaceCaller NamespaceRelease NamespacePaths NamespacePrepared
  NamespaceBorrow NamespaceParentFrame NamespaceParentData NamespaceParentWitness.
Import ListNotations.
Open Scope Z_scope.

Lemma namespace_root_is_global:In _root_path namespace_parent_global_names.
Proof. unfold namespace_parent_global_names,namespace_constant_names;cbn;auto 20. Qed.
Lemma namespace_policy_is_global:In _policy__1 namespace_parent_global_names.
Proof. unfold namespace_parent_global_names,namespace_constant_names;cbn;auto 20. Qed.
Lemma namespace_root_is_foreign:~In _root_path namespace_constant_names.
Proof. unfold namespace_constant_names;cbn;intuition discriminate. Qed.
Lemma namespace_policy_is_foreign:~In _policy__1 namespace_constant_names.
Proof. unfold namespace_constant_names;cbn;intuition discriminate. Qed.
Lemma namespace_cgroup_is_foreign:~In _admission_cgroup namespace_constant_names.
Proof. unfold namespace_constant_names;cbn;intuition discriminate. Qed.

Lemma namespace_prepared_constants initial locals uid_after root_after prepared source:
  Genv.init_mem EntrySource.prog=Some initial ->old_memory initial locals ->
  Mem.store Mint32 locals(handoff_symbol _run_uid)0(Vint(Int.repr 100000))=Some uid_after ->
  Mem.storebytes uid_after(handoff_symbol _root_path)0(map Byte(handoff_fixture_root_bytes++[Byte.zero]))=Some root_after ->
  Mem.store Mptr root_after(handoff_symbol _policy__1)88(Vptr source Ptrofs.zero)=Some prepared ->
  namespace_parent_constants prepared Int64.zero(Int.repr 100000).
Proof.
  intros INITIAL OLD UID ROOT POLICY.
  pose proof(namespace_initial_constants _ INITIAL)as CONSTANTS.
  assert(LOCAL:namespace_parent_constants locals Int64.zero Int.zero).
  { eapply namespace_constants_preserved;[exact CONSTANTS|].
    eapply Mem.unchanged_on_implies;[exact OLD|].
    intros object position MEMBER VALID;eapply namespace_constants_valid;eassumption. }
  pose proof(namespace_constants_uid_store _ _ _ _ _ LOCAL UID)as UIDS.
  assert(ROOTS:namespace_parent_constants root_after Int64.zero(Int.repr 100000)).
  { eapply namespace_constants_bytes_foreign with(id:=_root_path);
      [exact namespace_root_is_global|exact namespace_root_is_foreign|exact UIDS|exact ROOT]. }
  eapply namespace_constants_store_foreign with(id:=_policy__1);
    [exact namespace_policy_is_global|exact namespace_policy_is_foreign|exact ROOTS|exact POLICY].
Qed.

Lemma namespace_prepared_old_permissions initial locals uid_after root_after prepared source:
  old_memory initial locals ->
  Mem.store Mint32 locals(handoff_symbol _run_uid)0(Vint(Int.repr 100000))=Some uid_after ->
  Mem.storebytes uid_after(handoff_symbol _root_path)0(map Byte(handoff_fixture_root_bytes++[Byte.zero]))=Some root_after ->
  Mem.store Mptr root_after(handoff_symbol _policy__1)88(Vptr source Ptrofs.zero)=Some prepared ->
  forall object position kind permission,Mem.perm initial object position kind permission ->
    Mem.perm prepared object position kind permission.
Proof.
  intros OLD UID ROOT POLICY object position kind permission PERM.
  eapply Mem.perm_store_1;[exact POLICY|]. eapply Mem.perm_storebytes_1;[exact ROOT|].
  eapply Mem.perm_store_1;[exact UID|]. eapply handoff_fixture_old_perm;eassumption.
Qed.

Definition namespace_useful_initial_temps:=
  PTree.set _sequence(Vlong Int64.zero)
    (namespace_parameter_env(Int.repr 3)(Int.repr 8)(Int.repr 4)(Int.repr 5)(Int.repr 6)).
Definition namespace_useful_parent_temps:=namespace_parent_ready_env namespace_useful_initial_temps(Int.repr 2).

Lemma namespace_initial_memory_form before:
  namespace_allocated_memory(namespace_allocate_variables(fn_vars f_namespace_init)empty_env before)=
    namespace_initial_memory before.
Proof. unfold namespace_initial_memory,namespace_initial_allocation;reflexivity. Qed.
Lemma namespace_initial_env_form before:
  namespace_allocated_env(namespace_allocate_variables(fn_vars f_namespace_init)empty_env before)=
    namespace_initial_env before.
Proof. unfold namespace_initial_env,namespace_initial_allocation;reflexivity. Qed.
Lemma namespace_handoff_symbol id:namespace_symbol id=handoff_symbol id.
Proof. unfold namespace_symbol,handoff_symbol,namespace_ge,handoff_ge;reflexivity. Qed.
Local Opaque namespace_symbol handoff_symbol.
Lemma namespace_preflight_cgroup_objects:handoff_symbol _preflight<>handoff_symbol _admission_cgroup.
Proof.
  apply namespace_parent_globals_distinct;
    [unfold namespace_parent_global_names,namespace_constant_names;cbn;auto 20|
     unfold namespace_parent_global_names,namespace_constant_names;cbn;auto 20|discriminate].
Qed.

Local Transparent handoff_symbol.
Lemma namespace_cgroup_prepared_globals:
  Forall(fun id=>handoff_symbol _admission_cgroup<>handoff_symbol id)
    ([_run_uid;_preflight;_mode;_policy__1;_root_path;___stringlit_1]++map fst handoff_literal_bytes).
Proof.
  unfold handoff_literal_bytes,handoff_symbol,handoff_ge;vm_compute;repeat constructor;discriminate.
Qed.
Local Opaque handoff_symbol.

Lemma namespace_cgroup_not_borrowed initial command source:
  Genv.init_mem EntrySource.prog=Some initial ->
  ~Mem.valid_block initial command ->~Mem.valid_block initial source ->
  ~In(namespace_symbol _admission_cgroup)(handoff_borrowed_blocks(handoff_fixture_input command source)).
Proof.
  intros INITIAL COMMAND SOURCE MEMBER.
  assert(CG:Mem.valid_block initial(handoff_symbol _admission_cgroup)).
  { apply namespace_parent_global_valid;[exact INITIAL|unfold namespace_parent_global_names,namespace_constant_names;cbn;auto 20]. }
  assert(OLD:forall id,In id([_run_uid;_preflight;_mode;_policy__1;_root_path;___stringlit_1]++map fst handoff_literal_bytes) ->
    handoff_symbol _admission_cgroup<>handoff_symbol id).
  { intros id PRESENT;pose proof namespace_cgroup_prepared_globals as GLOBALS;rewrite Forall_forall in GLOBALS;apply GLOBALS;exact PRESENT. }
  rewrite namespace_handoff_symbol in MEMBER.
  unfold handoff_borrowed_blocks,handoff_fixture_input in MEMBER;
    cbn[handoff_borrowed_uid handoff_borrowed_preflight handoff_borrowed_mode handoff_borrowed_source
      handoff_borrowed_arguments address_block map fst app]in MEMBER.
  change(In(handoff_symbol _admission_cgroup)
    ([handoff_symbol _run_uid;handoff_symbol _preflight;handoff_symbol _mode;handoff_symbol _policy__1;
      handoff_symbol _root_path;handoff_symbol ___stringlit_1;source]++
      (map(fun literal=>handoff_symbol(fst literal))handoff_literal_bytes++[command])))in MEMBER.
  apply in_app_or in MEMBER;destruct MEMBER as[GLOBALS|REST].
  - cbn in GLOBALS;repeat destruct GLOBALS as[SAME|GLOBALS];try contradiction.
    all: try solve[match type of SAME with
      |handoff_symbol ?id=handoff_symbol _admission_cgroup=>
        apply(OLD id);[apply in_or_app;left;cbn;auto 12|symmetry;exact SAME]
      end].
    apply SOURCE;rewrite SAME;exact CG.
  - apply in_app_or in REST;destruct REST as[LITERALS|ARGUMENTS].
    + apply in_map_iff in LITERALS;destruct LITERALS as[literal[SAME MEMBER]].
      apply(OLD(fst literal)ltac:(apply in_or_app;right;apply in_map;exact MEMBER));symmetry;exact SAME.
    + cbn in ARGUMENTS;destruct ARGUMENTS as[SAME|NONE];[apply COMMAND;rewrite SAME;exact CG|contradiction].
Qed.

Local Transparent handoff_symbol.
Lemma namespace_run_prepared_globals:
  Forall(fun id=>handoff_symbol _run_id<>handoff_symbol id)
    ([_run_uid;_preflight;_mode;_policy__1;_root_path;___stringlit_1]++map fst handoff_literal_bytes).
Proof.
  unfold handoff_literal_bytes,handoff_symbol,handoff_ge;vm_compute;repeat constructor;discriminate.
Qed.
Local Opaque handoff_symbol.

Lemma namespace_run_not_borrowed initial command source:
  Genv.init_mem EntrySource.prog=Some initial ->
  ~Mem.valid_block initial command ->~Mem.valid_block initial source ->
  ~In(handoff_symbol _run_id)(handoff_borrowed_blocks(handoff_fixture_input command source)).
Proof.
  intros INITIAL COMMAND SOURCE MEMBER.
  assert(RUN:Mem.valid_block initial(handoff_symbol _run_id)).
  { apply namespace_parent_global_valid;[exact INITIAL|unfold namespace_parent_global_names,namespace_constant_names;cbn;auto 20]. }
  assert(OLD:forall id,In id([_run_uid;_preflight;_mode;_policy__1;_root_path;___stringlit_1]++map fst handoff_literal_bytes) ->
    handoff_symbol _run_id<>handoff_symbol id).
  { intros id PRESENT;pose proof namespace_run_prepared_globals as GLOBALS;rewrite Forall_forall in GLOBALS;apply GLOBALS;exact PRESENT. }
  unfold handoff_borrowed_blocks,handoff_fixture_input in MEMBER;
    cbn[handoff_borrowed_uid handoff_borrowed_preflight handoff_borrowed_mode handoff_borrowed_source
      handoff_borrowed_arguments address_block map fst app]in MEMBER.
  change(In(handoff_symbol _run_id)
    ([handoff_symbol _run_uid;handoff_symbol _preflight;handoff_symbol _mode;handoff_symbol _policy__1;
      handoff_symbol _root_path;handoff_symbol ___stringlit_1;source]++
      (map(fun literal=>handoff_symbol(fst literal))handoff_literal_bytes++[command])))in MEMBER.
  apply in_app_or in MEMBER;destruct MEMBER as[GLOBALS|REST].
  - cbn in GLOBALS;repeat destruct GLOBALS as[SAME|GLOBALS];try contradiction.
    all: try solve[match type of SAME with
      |handoff_symbol ?id=handoff_symbol _run_id=>
        apply(OLD id);[apply in_or_app;left;cbn;auto 12|symmetry;exact SAME]
      end].
    apply SOURCE;rewrite SAME;exact RUN.
  - apply in_app_or in REST;destruct REST as[LITERALS|ARGUMENTS].
    + apply in_map_iff in LITERALS;destruct LITERALS as[literal[SAME MEMBER]].
      apply(OLD(fst literal)ltac:(apply in_or_app;right;apply in_map;exact MEMBER));symmetry;exact SAME.
    + cbn in ARGUMENTS;destruct ARGUMENTS as[SAME|NONE];[apply COMMAND;rewrite SAME;exact RUN|contradiction].
Qed.

Theorem namespace_actual_callback_input_for_run(run:int64):
  exists initial cell command source prepared e childobject pipe status temporary admission memory,
    Genv.init_mem EntrySource.prog=Some initial /\
    handoff_borrowed_input cell prepared(handoff_fixture_input command source) /\
    e=namespace_initial_env prepared /\
    (forall object position kind permission,Mem.perm(namespace_initial_memory prepared)object position kind permission ->
      Mem.perm memory object position kind permission) /\
    handoff_borrowed_input cell memory(handoff_fixture_input command source) /\
    namespace_useful_callback_input cell e namespace_useful_parent_temps memory childobject pipe status temporary admission
      run(Int.repr 100000)(Int.repr 8)Int64.zero.
Proof.
  destruct handoff_actual_initial_memory_exists as[initial INITIAL].
  destruct(handoff_actual_input_memory_owned _ INITIAL)
    as[cell[command[source[locals[uid_after[root_after[unidentified
      [TLS_FRESH[COMMAND_FRESH[SOURCE_FRESH[OLD[UID_STORE[ROOT_STORE[POLICY_STORE INPUT]]]]]]]]]]]]]].
  pose proof(namespace_prepared_constants _ _ _ _ _ _ INITIAL OLD UID_STORE ROOT_STORE POLICY_STORE)as UNIDENTIFIED_CONSTANTS.
  pose proof(namespace_prepared_old_permissions _ _ _ _ _ _ OLD UID_STORE ROOT_STORE POLICY_STORE)as UNIDENTIFIED_PERMS.
  assert(RUN_ACCESS:Mem.valid_access unidentified Mint64(handoff_symbol _run_id)0 Writable).
  { destruct(namespace_initial_run_access _ INITIAL)as[RANGE ALIGN];split;[|exact ALIGN].
    intros position BOUND;apply UNIDENTIFIED_PERMS;apply RANGE;exact BOUND. }
  destruct(Mem.valid_access_store _ _ _ _(Vlong run)RUN_ACCESS)as[prepared RUN_STORE].
  assert(RUN_TLS:handoff_symbol _run_id<>tls_block cell).
  { intro SAME;apply TLS_FRESH;rewrite <-SAME;apply namespace_parent_global_valid;
      [exact INITIAL|unfold namespace_parent_global_names,namespace_constant_names;cbn;auto 20]. }
  assert(PREPARED_INPUT:handoff_borrowed_input cell prepared(handoff_fixture_input command source)).
  { eapply namespace_store_preserves_borrows;
      [exact INPUT|eapply namespace_run_not_borrowed;eassumption|exact RUN_TLS|exact RUN_STORE]. }
  clear INPUT;rename PREPARED_INPUT into INPUT.
  pose proof(namespace_constants_run_store _ _ _ _ _ UNIDENTIFIED_CONSTANTS RUN_STORE)as CONSTANTS.
  assert(INITIAL_PERMS:forall object position kind permission,Mem.perm initial object position kind permission ->
    Mem.perm prepared object position kind permission).
  { intros object position kind permission PERM;eapply Mem.perm_store_1;[exact RUN_STORE|].
    apply UNIDENTIFIED_PERMS;exact PERM. }
  set(e:=namespace_initial_env prepared).
  set(allocated:=namespace_initial_memory prepared).
  destruct(namespace_allocate_variables_source(fn_vars f_namespace_init)empty_env prepared)as[VARS ALLOC].
  assert(ENTRY:function_entry2 namespace_ge f_namespace_init
    [Vint(Int.repr 3);Vint(Int.repr 8);Vint(Int.repr 4);Vint(Int.repr 5);Vint(Int.repr 6)]
    prepared e(namespace_parameter_env(Int.repr 3)(Int.repr 8)(Int.repr 4)(Int.repr 5)(Int.repr 6))allocated).
  { apply namespace_function_entry;exact VARS. }
  assert(GLOBAL:caller_env_global e)by(eapply actual_namespace_entry_globals;exact ENTRY).
  pose proof(namespace_entry_callees_are_global prepared)as[CREATE[ADMIT[CLOSE[CGGLOBAL[RELEASE[CLOCK[SEND[RESULT CHECKGLOBAL]]]]]]]].
  destruct(namespace_owned_local_from_entry prepared _child tint ltac:(cbn;auto 20))
    as[childobject[CHILD[CHILD_FRESH CHILD_OWNED]]].
  destruct(namespace_owned_local_from_entry prepared _pipefd(tarray tint 2)ltac:(cbn;auto 20))
    as[pipe[PIPE[PIPE_FRESH PIPE_OWNED]]].
  destruct(namespace_owned_local_from_entry prepared _status tint ltac:(cbn;auto 20))
    as[status[STATUS[STATUS_FRESH STATUS_OWNED]]].
  destruct(namespace_owned_local_from_entry prepared __res__6 result_type ltac:(cbn;auto 20))
    as[temporary[TEMPORARY[TEMP_FRESH TEMP_OWNED]]].
  destruct(namespace_owned_local_from_entry prepared _admission result_type ltac:(cbn;auto 20))
    as[admission[ADMISSION[ADMISSION_FRESH ADMISSION_OWNED]]].
  change(sizeof namespace_ge tint)with 4 in CHILD_OWNED,STATUS_OWNED.
  change(sizeof namespace_ge(tarray tint 2))with 8 in PIPE_OWNED.
  change(sizeof namespace_ge result_type)with 144 in TEMP_OWNED,ADMISSION_OWNED.
  rewrite(namespace_initial_memory_form prepared)in CHILD_OWNED,PIPE_OWNED,STATUS_OWNED,TEMP_OWNED,ADMISSION_OWNED.
  rewrite(namespace_initial_env_form prepared)in CHILD,PIPE,STATUS,TEMPORARY,ADMISSION.
  assert(OLD_ALLOC:old_memory prepared allocated)by(eapply local_allocations_unchanged;exact ALLOC).
  assert(PREPARED_READY:entry_errno_ready cell prepared)by(exact(handoff_borrowed_errno _ _ _ INPUT)).
  assert(TLS_VALID:Mem.valid_block prepared(tls_block cell)).
  { destruct PREPARED_READY as[error[LOW[HIGH[ACCESS LOAD]]]].
    eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[exact ACCESS|constructor]. }
  assert(PRIVATE:forall object,~Mem.valid_block prepared object ->object<>tls_block cell).
  { intros object FRESH SAME;subst object;contradiction. }
  assert(GLOBAL_VALID:forall id,In id namespace_parent_global_names ->Mem.valid_block prepared(handoff_symbol id)).
  { intros id MEMBER;eapply Mem.store_valid_block_1;[exact RUN_STORE|].
    eapply Mem.store_valid_block_1;[exact POLICY_STORE|].
    eapply Mem.storebytes_valid_block_1;[exact ROOT_STORE|].
    eapply Mem.store_valid_block_1;[exact UID_STORE|].
    eapply Mem.valid_block_unchanged_on;[exact OLD|].
    exact(namespace_parent_global_valid _ _ INITIAL MEMBER). }
  assert(CONSTANT_VALID:forall object,namespace_constant_object object ->Mem.valid_block prepared object)
    by(intros;eapply namespace_constants_valid;eassumption).
  assert(CG_ACCESS:Mem.valid_access allocated Mint32(namespace_symbol _admission_cgroup)0 Writable).
  { rewrite namespace_handoff_symbol.
    pose proof(namespace_initial_cgroup_access _ INITIAL)as[RANGE ALIGN];split;[|exact ALIGN].
    intros position BOUND;eapply handoff_fixture_old_perm;[exact OLD_ALLOC|].
    apply INITIAL_PERMS;apply RANGE;exact BOUND. }
  assert(CG_VALID:Mem.valid_block prepared(namespace_symbol _admission_cgroup)).
  { rewrite namespace_handoff_symbol.
    eapply Mem.perm_valid_block with(ofs:=0)(k:=Cur)(p:=Writable);apply INITIAL_PERMS.
    destruct(namespace_initial_cgroup_access _ INITIAL)as[RANGE ALIGN];apply RANGE;change(0<=0<4);lia. }
  assert(CHECK_VALID:Mem.valid_block initial(handoff_symbol _preflight)).
  { apply namespace_parent_global_valid;[exact INITIAL|unfold namespace_parent_global_names,namespace_constant_names;cbn;auto 20]. }
  assert(CG_TLS:namespace_symbol _admission_cgroup<>tls_block cell).
  { rewrite namespace_handoff_symbol;intro SAME;apply TLS_FRESH;rewrite <-SAME;apply namespace_parent_global_valid;
      [exact INITIAL|unfold namespace_parent_global_names,namespace_constant_names;cbn;auto 20]. }
  assert(CONSTANT_TLS:forall object,namespace_constant_object object ->object<>tls_block cell).
  { intros object MEMBER SAME;apply TLS_FRESH;rewrite <-SAME.
    apply in_map_iff in MEMBER;destruct MEMBER as[id[VALUE MEMBER]];subst object.
    apply namespace_parent_global_valid;[exact INITIAL|unfold namespace_parent_global_names;apply in_or_app;left;exact MEMBER]. }
  pose proof(namespace_entry_has_distinct_local_objects prepared)as DISTINCT.
  rewrite(namespace_initial_env_form prepared)in DISTINCT.
  assert(CHILD_PIPE:childobject<>pipe)by(eapply(DISTINCT _child _pipefd);[exact CHILD|exact PIPE|discriminate]).
  assert(CHILD_STATUS:childobject<>status)by(eapply(DISTINCT _child _status);[exact CHILD|exact STATUS|discriminate]).
  assert(PIPE_STATUS:pipe<>status)by(eapply(DISTINCT _pipefd _status);[exact PIPE|exact STATUS|discriminate]).
  assert(TEMP_ADMISSION:temporary<>admission)by(eapply(DISTINCT __res__6 _admission);[exact TEMPORARY|exact ADMISSION|discriminate]).
  assert(CHILD_CG:childobject<>namespace_symbol _admission_cgroup)by(intro SAME;apply CHILD_FRESH;rewrite SAME;exact CG_VALID).
  assert(PIPE_CG:pipe<>namespace_symbol _admission_cgroup)by(intro SAME;apply PIPE_FRESH;rewrite SAME;exact CG_VALID).
  assert(STATUS_CG:status<>namespace_symbol _admission_cgroup)by(intro SAME;apply STATUS_FRESH;rewrite SAME;exact CG_VALID).
  assert(CHILD_ACCESS:Mem.valid_access allocated Mint32 childobject 0 Writable).
  { split;[intros position BOUND;eapply Mem.perm_implies;[apply CHILD_OWNED;exact BOUND|constructor]|apply Z.divide_0_r]. }
  destruct(Mem.valid_access_store _ _ _ _(Vint(Int.repr 2))CHILD_ACCESS)as[child_set CHILD_STORE].
  assert(PIPE_ACCESS:Mem.valid_access child_set Mint32 pipe 0 Writable).
  { split;[intros position BOUND;eapply Mem.perm_store_1;[exact CHILD_STORE|];
      eapply Mem.perm_implies;[apply PIPE_OWNED;cbn in BOUND;lia|constructor]|apply Z.divide_0_r]. }
  destruct(Mem.valid_access_store _ _ _ _(Vint(Int.repr 9))PIPE_ACCESS)as[pipe_set PIPE_STORE].
  assert(CG_ACCESS':Mem.valid_access pipe_set Mint32(namespace_symbol _admission_cgroup)0 Writable).
  { eapply Mem.store_valid_access_1;[exact PIPE_STORE|]. eapply Mem.store_valid_access_1;[exact CHILD_STORE|exact CG_ACCESS]. }
  destruct(Mem.valid_access_store _ _ _ _(Vint(Int.repr 7))CG_ACCESS')as[cgroup_set CG_STORE].
  assert(STATUS_ACCESS:Mem.valid_access cgroup_set Mint32 status 0 Writable).
  { split;[intros position BOUND;eapply Mem.perm_store_1;[exact CG_STORE|];eapply Mem.perm_store_1;[exact PIPE_STORE|];
      eapply Mem.perm_store_1;[exact CHILD_STORE|];eapply Mem.perm_implies;
        [apply STATUS_OWNED;exact BOUND|constructor]|apply Z.divide_0_r]. }
  destruct(Mem.valid_access_store _ _ _ _(Vint Int.zero)STATUS_ACCESS)as[memory STATUS_STORE].
  assert(STORE_PERMS:forall object position kind permission,
    Mem.perm allocated object position kind permission ->Mem.perm memory object position kind permission).
  { intros object position kind permission PERM;eapply Mem.perm_store_1;[exact STATUS_STORE|].
    eapply Mem.perm_store_1;[exact CG_STORE|]. eapply Mem.perm_store_1;[exact PIPE_STORE|].
    eapply Mem.perm_store_1;[exact CHILD_STORE|exact PERM]. }
  assert(MEMORY_FRAME:Mem.unchanged_on(fun object _=>object<>childobject /\object<>pipe /\
    object<>namespace_symbol _admission_cgroup /\object<>status)allocated memory).
  { eapply Mem.unchanged_on_trans;[eapply Mem.store_unchanged_on;[exact CHILD_STORE|intros;tauto]|].
    eapply Mem.unchanged_on_trans;[eapply Mem.store_unchanged_on;[exact PIPE_STORE|intros;tauto]|].
    eapply Mem.unchanged_on_trans;[eapply Mem.store_unchanged_on;[exact CG_STORE|intros;tauto]|].
    eapply Mem.store_unchanged_on;[exact STATUS_STORE|intros;tauto]. }
  assert(ALLOC_READY:entry_errno_ready cell allocated).
  { eapply namespace_errno_unchanged;[exact PREPARED_READY|].
    eapply Mem.unchanged_on_implies;[exact OLD_ALLOC|].
    intros object position SAME VALID;subst object;exact TLS_VALID. }
  assert(MEMORY_READY:entry_errno_ready cell memory).
  { eapply namespace_errno_unchanged;[exact ALLOC_READY|].
    eapply Mem.unchanged_on_implies;[exact MEMORY_FRAME|].
    intros object position SAME VALID;subst object;split.
    - intro SAME;apply CHILD_FRESH;rewrite <-SAME;exact TLS_VALID.
    - split.
      + intro SAME;apply PIPE_FRESH;rewrite <-SAME;exact TLS_VALID.
      + split;[intro SAME;apply CG_TLS;symmetry;exact SAME|].
        intro SAME;apply STATUS_FRESH;rewrite <-SAME;exact TLS_VALID. }
  assert(ALLOC_CONSTANTS:namespace_parent_constants allocated run(Int.repr 100000)).
  { eapply namespace_constants_preserved;[exact CONSTANTS|].
    eapply Mem.unchanged_on_implies;[exact OLD_ALLOC|]. intros object position MEMBER VALID;apply CONSTANT_VALID;exact MEMBER. }
  assert(MEMORY_CONSTANTS:namespace_parent_constants memory run(Int.repr 100000)).
  { eapply namespace_constants_preserved;[exact ALLOC_CONSTANTS|].
    eapply Mem.unchanged_on_implies;[exact MEMORY_FRAME|].
    intros object position MEMBER VALID;repeat split.
    - intro SAME;apply CHILD_FRESH;rewrite <-SAME;apply CONSTANT_VALID;exact MEMBER.
    - intro SAME;apply PIPE_FRESH;rewrite <-SAME;apply CONSTANT_VALID;exact MEMBER.
    - rewrite namespace_handoff_symbol;apply namespace_constant_foreign;[unfold namespace_parent_global_names,namespace_constant_names;cbn;auto 20|
        exact namespace_cgroup_is_foreign|exact MEMBER].
    - intro SAME;apply STATUS_FRESH;rewrite <-SAME;apply CONSTANT_VALID;exact MEMBER. }
  assert(MEMORY_BORROWED:handoff_borrowed_input cell memory(handoff_fixture_input command source)).
  { eapply namespace_store_preserves_borrows with(object:=status);[| |apply PRIVATE;exact STATUS_FRESH|exact STATUS_STORE].
    - eapply namespace_store_preserves_borrows with(object:=namespace_symbol _admission_cgroup);
        [|apply namespace_cgroup_not_borrowed with(initial:=initial);assumption|exact CG_TLS|exact CG_STORE].
      eapply namespace_store_preserves_borrows with(object:=pipe);[| |apply PRIVATE;exact PIPE_FRESH|exact PIPE_STORE].
      + eapply namespace_store_preserves_borrows with(object:=childobject);[| |apply PRIVATE;exact CHILD_FRESH|exact CHILD_STORE].
        * eapply namespace_allocation_preserves_borrows;[exact INPUT|exact ALLOC].
        * eapply namespace_fresh_local_separate_borrows;[exact INPUT|exact CHILD_FRESH].
      + eapply namespace_fresh_local_separate_borrows;[exact INPUT|exact PIPE_FRESH].
    - eapply namespace_fresh_local_separate_borrows;[exact INPUT|exact STATUS_FRESH]. }
  exists initial,cell,command,source,prepared,e,childobject,pipe,status,temporary,admission,memory.
  split;[exact INITIAL|]. split;[exact INPUT|]. split;[reflexivity|]. split;[exact STORE_PERMS|]. split;[exact MEMORY_BORROWED|]. constructor.
  - exact GLOBAL.
  - split;assumption.
  - repeat split;assumption.
  - unfold namespace_useful_parent_temps,namespace_parent_ready_env,namespace_admission_ready_env,
      namespace_parent_checked_env,namespace_created_env,namespace_useful_initial_temps,namespace_parameter_env;
      repeat split;WriteAll.lookup.
  - repeat split.
    + erewrite Mem.load_store_other;[|exact STATUS_STORE|left;exact CHILD_STATUS].
      erewrite Mem.load_store_other;[|exact CG_STORE|left;exact CHILD_CG].
      erewrite Mem.load_store_other;[|exact PIPE_STORE|left;exact CHILD_PIPE].
      erewrite Mem.load_store_same by exact CHILD_STORE;reflexivity.
    + erewrite Mem.load_store_other;[|exact STATUS_STORE|left;exact PIPE_STATUS].
      erewrite Mem.load_store_other;[|exact CG_STORE|left;exact PIPE_CG].
      erewrite Mem.load_store_same by exact PIPE_STORE;reflexivity.
    + erewrite Mem.load_store_other;[|exact STATUS_STORE|left;intro SAME;apply STATUS_CG;symmetry;exact SAME].
      erewrite Mem.load_store_same by exact CG_STORE;reflexivity.
    + rewrite namespace_handoff_symbol;eapply Mem.load_unchanged_on;[exact MEMORY_FRAME| |].
      * intros position RANGE;repeat split.
        -- intro SAME;apply CHILD_FRESH;rewrite <-SAME;apply GLOBAL_VALID;
             unfold namespace_parent_global_names,namespace_constant_names;cbn;auto 20.
        -- intro SAME;apply PIPE_FRESH;rewrite <-SAME;apply GLOBAL_VALID;
             unfold namespace_parent_global_names,namespace_constant_names;cbn;auto 20.
        -- intro SAME;exact(namespace_preflight_cgroup_objects
             (eq_trans SAME(namespace_handoff_symbol _admission_cgroup))).
        -- intro SAME;apply STATUS_FRESH;rewrite <-SAME;apply GLOBAL_VALID;
             unfold namespace_parent_global_names,namespace_constant_names;cbn;auto 20.
      * eapply old_memory_load;
          [exact OLD_ALLOC|exact(handoff_borrowed_preflight_load _ _ _ INPUT)].
  - exact MEMORY_READY.
  - eapply Mem.store_valid_access_1;[exact STATUS_STORE|exact STATUS_ACCESS].
  - eapply Mem.store_valid_access_1;[exact STATUS_STORE|].
    eapply Mem.store_valid_access_1;[exact CG_STORE|exact CG_ACCESS'].
  - intros position RANGE;apply STORE_PERMS;apply TEMP_OWNED;exact RANGE.
  - intros position RANGE;apply STORE_PERMS;apply ADMISSION_OWNED;exact RANGE.
  - repeat split;try exact TEMP_ADMISSION;try exact CG_TLS;apply PRIVATE;assumption.
  - exact MEMORY_CONSTANTS.
  - intros object MEMBER;repeat split.
    + intro SAME;apply STATUS_FRESH;rewrite <-SAME;apply CONSTANT_VALID;exact MEMBER.
    + apply CONSTANT_TLS;exact MEMBER.
    + rewrite namespace_handoff_symbol;apply namespace_constant_foreign;[unfold namespace_parent_global_names,namespace_constant_names;cbn;auto 20|
        exact namespace_cgroup_is_foreign|exact MEMBER].
    + intro SAME;apply TEMP_FRESH;rewrite <-SAME;apply CONSTANT_VALID;exact MEMBER.
    + intro SAME;apply ADMISSION_FRESH;rewrite <-SAME;apply CONSTANT_VALID;exact MEMBER.
Qed.

Theorem namespace_actual_callback_input_owned:
  exists initial cell command source prepared e childobject pipe status temporary admission memory,
    Genv.init_mem EntrySource.prog=Some initial /\
    handoff_borrowed_input cell prepared(handoff_fixture_input command source) /\
    e=namespace_initial_env prepared /\
    (forall object position kind permission,Mem.perm(namespace_initial_memory prepared)object position kind permission ->
      Mem.perm memory object position kind permission) /\
    handoff_borrowed_input cell memory(handoff_fixture_input command source) /\
    namespace_useful_callback_input cell e namespace_useful_parent_temps memory childobject pipe status temporary admission
      Int64.zero(Int.repr 100000)(Int.repr 8)Int64.zero.
Proof. exact(namespace_actual_callback_input_for_run Int64.zero). Qed.

Theorem namespace_actual_callback_input:
  exists initial cell command source prepared e childobject pipe status temporary admission memory,
    Genv.init_mem EntrySource.prog=Some initial /\
    handoff_borrowed_input cell prepared(handoff_fixture_input command source) /\
    e=namespace_initial_env prepared /\
    namespace_useful_callback_input cell e namespace_useful_parent_temps memory childobject pipe status temporary admission
      Int64.zero(Int.repr 100000)(Int.repr 8)Int64.zero.
Proof.
  destruct namespace_actual_callback_input_owned as(initial &cell &command &source &prepared &e &childobject &pipe
    &status &temporary &admission &memory &INITIAL &INPUT &CANONICAL &PERMISSIONS &BORROWED &CALLBACKS).
  exists initial,cell,command,source,prepared,e,childobject,pipe,status,temporary,admission,memory.
  split;[exact INITIAL|]. split;[exact INPUT|]. split;assumption.
Qed.

Theorem namespace_actual_useful_parent:
  exists initial cell command source prepared e childobject pipe status temporary admission memory events final,
    Genv.init_mem EntrySource.prog=Some initial /\
    handoff_borrowed_input cell prepared(handoff_fixture_input command source) /\
    e=namespace_initial_env prepared /\
    namespace_useful_callback_input cell e namespace_useful_parent_temps memory childobject pipe status temporary admission
      Int64.zero(Int.repr 100000)(Int.repr 8)Int64.zero /\
    namespace_steps namespace_ge cell
      (live(State f_namespace_init(namespace_tail 20)Kstop e namespace_useful_parent_temps memory))events
      (live(Callstate(Internal f_release_child)[Vint(Int.repr 2);Vint(Int.repr 9)]
        (namespace_release_cont e(namespace_useful_published_env namespace_useful_parent_temps Int64.zero)
          (Int.repr 2)(Int.repr 9)Kstop)final)).
Proof.
  destruct namespace_actual_callback_input as(initial &cell &command &source &prepared &e &childobject &pipe
    &status &temporary &admission &memory &INITIAL &INPUT &CANONICAL &CALLBACKS).
  destruct(namespace_useful_callbacks_reach_release _ _ _ _ _ _ _ _ _ _ _ _ _ CALLBACKS)
    as[events[final RUN]].
  exists initial,cell,command,source,prepared,e,childobject,pipe,status,temporary,admission,memory,events,final.
  split;[exact INITIAL|]. split;[exact INPUT|]. split;[exact CANONICAL|]. split;assumption.
Qed.
