(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.acceptance: Useful prepared caller entry owns one common fork and its full grant. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import IO Machine ErrorNumber Library ProcessEffects FreshMemory ReceiverAllocation StoreSteps WriteAll LibraryMachine.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffArguments NativeHandoffInput NativeHandoffInputWitness.
From EntryProcess Require Import ProcessMachine ProcessGlobalCalls ProcessAllocation ProcessReleaseWitness.
From EntryReporting Require Import ResultLayout.
From EntryNamespace Require Import NamespaceMachine NamespaceStructure NamespaceAllocation NamespaceCaller NamespaceRelease
  NamespacePaths NamespacePrepared NamespaceBorrow NamespaceParentFrame NamespaceParentData NamespaceParentWitness
  NamespaceParentInput NamespaceForkWitness NamespaceSenderWitness.
Import ListNotations.
Open Scope Z_scope.

Lemma namespace_prepared_global_bounds:
  Forall(fun id=>Pos.le(handoff_symbol id)(handoff_symbol _mode))
    (namespace_constant_names++[_admission_cgroup;_preflight]).
Proof.
  assert(CHECK:forallb(fun id=>Pos.leb(handoff_symbol id)(handoff_symbol _mode))
    (namespace_constant_names++[_admission_cgroup;_preflight])=true).
  { unfold namespace_constant_names,handoff_symbol,handoff_ge;vm_compute;reflexivity. }
  apply Forall_forall;intros id MEMBER;apply Pos.leb_le.
  rewrite forallb_forall in CHECK;apply CHECK;exact MEMBER.
Qed.
Lemma namespace_launch_process_environment:admission_ge=namespace_ge.
Proof. reflexivity. Qed.
Local Opaque handoff_symbol namespace_symbol namespace_ge.

Lemma namespace_prepared_globals_exist cell prepared input id:
  handoff_borrowed_input cell prepared input ->
  In id(namespace_constant_names++[_admission_cgroup;_preflight]) ->
  Mem.valid_block prepared(handoff_symbol id).
Proof.
  intros INPUT MEMBER;pose proof(namespace_prepared_global_bounds)as BOUNDS.
  rewrite Forall_forall in BOUNDS;pose proof(BOUNDS id MEMBER)as LESS.
  pose proof(handoff_loadv_valid _ _ _ _ _ (handoff_borrowed_mode_load _ _ _ INPUT))as VALID.
  unfold Mem.valid_block in *;eapply Pos.le_lt_trans;[exact LESS|exact VALID].
Qed.

Lemma namespace_canonical_env_fresh prepared:
  namespace_old_env_fresh prepared(namespace_initial_env prepared).
Proof.
  destruct(namespace_allocate_variables_source(fn_vars f_namespace_init)empty_env prepared)as[VARS ALLOC].
  assert(EMPTY:namespace_old_env_fresh prepared empty_env).
  { intros id object ty LOOKUP;rewrite PTree.gempty in LOOKUP;discriminate. }
  pose proof(namespace_actual_allocation_fresh prepared _ _ _ _ _ VARS(fun object VALID=>VALID)EMPTY)as FRESH.
  rewrite(namespace_initial_env_form prepared)in FRESH;exact FRESH.
Qed.

Theorem namespace_callback_outputs_private cell prepared borrowed e le memory childobject pipe status temporary admission
    run uid report sequence:
  handoff_borrowed_input cell prepared borrowed ->e=namespace_initial_env prepared ->
  namespace_useful_callback_input cell e le memory childobject pipe status temporary admission run uid report sequence ->
  childobject<>tls_block cell /\pipe<>tls_block cell /\childobject<>pipe /\
    ~In childobject(handoff_borrowed_blocks borrowed) /\~In pipe(handoff_borrowed_blocks borrowed) /\
    (forall object,namespace_constant_object object ->object<>childobject /\object<>pipe) /\
    namespace_symbol _admission_cgroup<>childobject /\namespace_symbol _admission_cgroup<>pipe /\
    namespace_symbol _preflight<>childobject /\namespace_symbol _preflight<>pipe.
Proof.
  intros INPUT CANONICAL CALLBACKS;subst e.
  pose proof(namespace_useful_locals _ _ _ _ _ _ _ _ _ _ _ _ _ CALLBACKS)as[CHILD[PIPE[STATUS REST]]].
  pose proof(namespace_canonical_env_fresh prepared)as FRESH.
  assert(CHILD_FRESH:~Mem.valid_block prepared childobject)by(exact(FRESH _ _ _ CHILD)).
  assert(PIPE_FRESH:~Mem.valid_block prepared pipe)by(exact(FRESH _ _ _ PIPE)).
  assert(TLS:Mem.valid_block prepared(tls_block cell)).
  { destruct(handoff_borrowed_errno _ _ _ INPUT)as[error[LOW[HIGH[ACCESS LOAD]]]].
    eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[exact ACCESS|constructor]. }
  assert(OLD:forall object,namespace_constant_object object ->Mem.valid_block prepared object).
  { intros object MEMBER;apply in_map_iff in MEMBER;destruct MEMBER as[id[SAME MEMBER]];subst object.
    eapply namespace_prepared_globals_exist;[exact INPUT|apply in_or_app;left;exact MEMBER]. }
  assert(CG:Mem.valid_block prepared(namespace_symbol _admission_cgroup)).
  { rewrite namespace_handoff_symbol;eapply namespace_prepared_globals_exist;[exact INPUT|apply in_or_app;right;cbn;auto]. }
  assert(CHECK:Mem.valid_block prepared(namespace_symbol _preflight)).
  { rewrite namespace_handoff_symbol;eapply namespace_prepared_globals_exist;[exact INPUT|apply in_or_app;right;cbn;auto]. }
  split;[intro SAME;apply CHILD_FRESH;rewrite SAME;exact TLS|].
  split;[intro SAME;apply PIPE_FRESH;rewrite SAME;exact TLS|]. split.
  - pose proof(namespace_entry_has_distinct_local_objects prepared)as DISTINCT.
    rewrite(namespace_initial_env_form prepared)in DISTINCT.
    exact(DISTINCT _child _pipefd _ _ _ _ CHILD PIPE ltac:(discriminate)).
  - split;[eapply namespace_fresh_local_separate_borrows;eassumption|].
    split;[eapply namespace_fresh_local_separate_borrows;eassumption|]. split.
    + intros object MEMBER;split;intro SAME;
        [apply CHILD_FRESH|apply PIPE_FRESH];rewrite <-SAME;apply OLD;exact MEMBER.
    + split;[intro SAME;apply CHILD_FRESH;rewrite <-SAME;exact CG|].
      split;[intro SAME;apply PIPE_FRESH;rewrite <-SAME;exact CG|].
      split;intro SAME;[apply CHILD_FRESH|apply PIPE_FRESH];rewrite <-SAME;exact CHECK.
Qed.

Theorem namespace_callback_after_child cell prepared borrowed e le next before after childobject pipe status temporary admission
    run uid report sequence:
  handoff_borrowed_input cell prepared borrowed ->e=namespace_initial_env prepared ->
  namespace_useful_callback_input cell e le before childobject pipe status temporary admission run uid report sequence ->
  next!_bad=Some(Vint Int.zero) ->next!_report=Some(Vint report) ->next!_sequence=Some(Vlong sequence) ->
  entry_errno_ready cell after ->Mem.load Mint32 after childobject 0=Some(Vint(Int.repr 2)) ->
  Mem.load Mint32 after pipe 0=Some(Vint(Int.repr 9)) ->
  Mem.unchanged_on(namespace_child_old before pipe childobject)before after ->
  (forall object position kind permission,Mem.perm before object position kind permission ->Mem.perm after object position kind permission) ->
  namespace_useful_callback_input cell e next after childobject pipe status temporary admission run uid report sequence.
Proof.
  intros INPUT CANONICAL CALLBACKS BAD REPORT SEQUENCE READY PID PEER FRAME PERMS.
  destruct(namespace_callback_outputs_private _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INPUT CANONICAL CALLBACKS)
    as[CHILD_TLS[PIPE_TLS[CHILD_PIPE[CHILD_PRIVATE[PIPE_PRIVATE[CONSTANT_PRIVATE[CG_CHILD[CG_PIPE[CHECK_CHILD CHECK_PIPE]]]]]]]]].
  destruct CALLBACKS as[GLOBAL GLOBAL_CELLS LOCALS TEMPS[OLD_PID[OLD_PEER[CGROUP CHECK]]]OLD_READY STATUS_ACCESS CGROUP_ACCESS
    TEMP_OWNED ADMISSION_OWNED SEPARATE CONSTANTS CONSTANT_SEPARATE].
  assert(CONSTANTS_AFTER:namespace_parent_constants after run uid).
  { eapply namespace_constants_preserved;[exact CONSTANTS|].
    eapply Mem.unchanged_on_implies;[exact FRAME|].
    intros object position MEMBER VALID;split;[eapply namespace_constants_valid;eassumption|].
    destruct(CONSTANT_PRIVATE _ MEMBER)as[CHILD PIPE];split;assumption. }
  constructor.
  - exact GLOBAL.
  - exact GLOBAL_CELLS.
  - exact LOCALS.
  - repeat split;assumption.
  - split;[exact PID|]. split;[exact PEER|]. split.
    + eapply Mem.load_unchanged_on;[exact FRAME| |exact CGROUP].
      intros position RANGE;split.
      * eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[eapply Mem.load_valid_access;exact CGROUP|constructor].
      * split;assumption.
    + eapply Mem.load_unchanged_on;[exact FRAME| |exact CHECK].
      intros position RANGE;split.
      * eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[eapply Mem.load_valid_access;exact CHECK|constructor].
      * split;assumption.
  - exact READY.
  - destruct STATUS_ACCESS as[RANGE ALIGN];split;[intros position BOUND;apply PERMS;apply RANGE;exact BOUND|exact ALIGN].
  - destruct CGROUP_ACCESS as[RANGE ALIGN];split;[intros position BOUND;apply PERMS;apply RANGE;exact BOUND|exact ALIGN].
  - intros position BOUND;apply PERMS;apply TEMP_OWNED;exact BOUND.
  - intros position BOUND;apply PERMS;apply ADMISSION_OWNED;exact BOUND.
  - exact SEPARATE.
  - exact CONSTANTS_AFTER.
  - exact CONSTANT_SEPARATE.
Qed.

Lemma namespace_callback_status_private cell prepared borrowed e le memory childobject pipe status temporary admission
    run uid report sequence:
  handoff_borrowed_input cell prepared borrowed ->e=namespace_initial_env prepared ->
  namespace_useful_callback_input cell e le memory childobject pipe status temporary admission run uid report sequence ->
  status<>childobject /\status<>pipe /\status<>namespace_symbol _admission_cgroup /\status<>namespace_symbol _preflight.
Proof.
  intros INPUT CANONICAL CALLBACKS;subst e.
  pose proof(namespace_useful_locals _ _ _ _ _ _ _ _ _ _ _ _ _ CALLBACKS)as[CHILD[PIPE[STATUS REST]]].
  pose proof(namespace_entry_has_distinct_local_objects prepared)as DISTINCT.
  rewrite(namespace_initial_env_form prepared)in DISTINCT.
  pose proof(namespace_canonical_env_fresh prepared)as FRESH.
  split;[exact(DISTINCT _status _child _ _ _ _ STATUS CHILD ltac:(discriminate))|].
  split;[exact(DISTINCT _status _pipefd _ _ _ _ STATUS PIPE ltac:(discriminate))|].
  split.
  - intro SAME;apply(FRESH _ _ _ STATUS);rewrite SAME,namespace_handoff_symbol;
      eapply namespace_prepared_globals_exist;[exact INPUT|apply in_or_app;right;cbn;auto].
  - intro SAME;apply(FRESH _ _ _ STATUS);rewrite SAME,namespace_handoff_symbol;
      eapply namespace_prepared_globals_exist;[exact INPUT|apply in_or_app;right;cbn;auto].
Qed.

Theorem namespace_callback_after_status cell e le next before after childobject pipe status temporary admission
    run uid report sequence:
  namespace_useful_callback_input cell e le before childobject pipe status temporary admission run uid report sequence ->
  next!_bad=Some(Vint Int.zero) ->next!_report=Some(Vint report) ->next!_sequence=Some(Vlong sequence) ->
  status<>childobject ->status<>pipe ->status<>namespace_symbol _admission_cgroup ->status<>namespace_symbol _preflight ->
  Mem.store Mint32 before status 0(Vint Int.zero)=Some after ->
  namespace_useful_callback_input cell e next after childobject pipe status temporary admission run uid report sequence.
Proof.
  intros[GLOBAL GLOBAL_CELLS LOCALS TEMPS[PID[PEER[CGROUP CHECK]]]READY STATUS_ACCESS CGROUP_ACCESS
    TEMP_OWNED ADMISSION_OWNED SEPARATE CONSTANTS CONSTANT_SEPARATE]
    BAD REPORT SEQUENCE STATUS_CHILD STATUS_PIPE STATUS_CGROUP STATUS_CHECK STORE.
  assert(CONSTANTS_AFTER:namespace_parent_constants after run uid).
  { eapply namespace_constants_preserved;[exact CONSTANTS|].
    eapply Mem.store_unchanged_on;[exact STORE|].
    intros position RANGE MEMBER;exact(proj1(CONSTANT_SEPARATE _ MEMBER)eq_refl). }
  constructor.
  - exact GLOBAL.
  - exact GLOBAL_CELLS.
  - exact LOCALS.
  - repeat split;assumption.
  - split;[|split;[|split]];erewrite Mem.load_store_other;
      [exact PID|exact STORE|left;intro SAME;apply STATUS_CHILD;symmetry;exact SAME|
       exact PEER|exact STORE|left;intro SAME;apply STATUS_PIPE;symmetry;exact SAME|
       exact CGROUP|exact STORE|left;intro SAME;apply STATUS_CGROUP;symmetry;exact SAME|
       exact CHECK|exact STORE|left;intro SAME;apply STATUS_CHECK;symmetry;exact SAME].
  - eapply namespace_errno_store;[exact(proj1 SEPARATE)|exact READY|exact STORE].
  - eapply Mem.store_valid_access_1;eassumption.
  - eapply Mem.store_valid_access_1;eassumption.
  - intros position RANGE;eapply Mem.perm_store_1;[exact STORE|apply TEMP_OWNED;exact RANGE].
  - intros position RANGE;eapply Mem.perm_store_1;[exact STORE|apply ADMISSION_OWNED;exact RANGE].
  - exact SEPARATE.
  - exact CONSTANTS_AFTER.
  - exact CONSTANT_SEPARATE.
Qed.

Definition namespace_parent_prefix_event event:=event=namespace_source_event \/
  exists descriptor,In descriptor[Int.repr 3;Int.repr 4;Int.repr 5;Int.repr 6;Int.repr 60] /\
    event=namespace_close_event descriptor(close_ok None).

Lemma namespace_parent_prefix_sources count:
  Forall namespace_parent_prefix_event(repeat namespace_source_event count).
Proof. induction count;constructor;[left;reflexivity|exact IHcount]. Qed.

Ltac namespace_useful_prefix_profile:=
  lazymatch goal with
  | |-Forall _ (?first++?rest)=>apply Forall_app;split;namespace_useful_prefix_profile
  | |-Forall _ (repeat namespace_source_event ?count)=>apply namespace_parent_prefix_sources
  | |-Forall _ (namespace_close_event ?descriptor (close_ok None)::?rest)=>
    constructor;[right;exists descriptor;split;[cbn;auto 8|reflexivity]|namespace_useful_prefix_profile]
  | |-Forall _ []=>constructor
  end.

Theorem namespace_useful_parent_return_to_setup_for_run(run:int64) cell prepared borrowed e memory childobject pipe status temporary admission:
  handoff_borrowed_input cell prepared borrowed ->e=namespace_initial_env prepared ->
  namespace_useful_callback_input cell e namespace_useful_parent_temps memory childobject pipe status temporary admission
    run(Int.repr 100000)(Int.repr 8)Int64.zero ->
  exists events after,
    namespace_steps namespace_ge cell
      (live(Returnstate(Vint Int.zero)(namespace_creation_cont e namespace_useful_parent_temps Kstop)memory))events
      (live(State f_namespace_init(namespace_tail 20)Kstop e
        (namespace_parent_ready_env namespace_useful_parent_temps(Int.repr 2))after)) /\
    namespace_useful_callback_input cell e(namespace_parent_ready_env namespace_useful_parent_temps(Int.repr 2))after
      childobject pipe status temporary admission run(Int.repr 100000)(Int.repr 8)Int64.zero /\Forall namespace_parent_prefix_event events.
Proof.
  intros INPUT CANONICAL CALLBACKS.
  pose proof(namespace_useful_globals _ _ _ _ _ _ _ _ _ _ _ _ _ CALLBACKS)as GLOBAL.
  pose proof(namespace_useful_locals _ _ _ _ _ _ _ _ _ _ _ _ _ CALLBACKS)as[CHILD[PIPE[STATUS REST]]].
  pose proof(namespace_useful_captures _ _ _ _ _ _ _ _ _ _ _ _ _ CALLBACKS)as[PID[PEER[CGROUP CHECK]]].
  pose proof(namespace_useful_errno _ _ _ _ _ _ _ _ _ _ _ _ _ CALLBACKS)as READY.
  pose proof(namespace_useful_status _ _ _ _ _ _ _ _ _ _ _ _ _ CALLBACKS)as STATUS_ACCESS.
  destruct(namespace_callback_status_private _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INPUT CANONICAL CALLBACKS)
    as[STATUS_CHILD[STATUS_PIPE[STATUS_CGROUP STATUS_CHECK]]].
  assert(CLOSE:e!_close=None)by(apply GLOBAL;vm_compute;reflexivity).
  assert(CLOSE_EFFECT:close_effect cell memory(close_ok None)memory)
    by(split;[apply entry_errno_ready_tls;exact READY|constructor]).
  destruct(Mem.valid_access_store _ _ _ _(Vint Int.zero)STATUS_ACCESS)as[after STORE].
  eexists;exists after;split.
  - eapply namespace_steps_append;[eapply namespace_store_path_actual;apply namespace_create_return_source|].
    eapply namespace_steps_append.
    + apply namespace_close_phase_run with(index:=0%nat)(id:=_input)(descriptor:=Int.repr 4)(reply:=close_ok None);
        [reflexivity|exact CLOSE|unfold namespace_created_env,namespace_useful_parent_temps,namespace_parent_ready_env,
          namespace_admission_ready_env,namespace_parent_checked_env,namespace_useful_initial_temps,namespace_parameter_env;WriteAll.lookup|exact CLOSE_EFFECT].
    + eapply namespace_steps_append.
      * apply namespace_close_phase_run with(index:=1%nat)(id:=_output)(descriptor:=Int.repr 5)(reply:=close_ok None);
          [reflexivity|exact CLOSE|unfold namespace_created_env,namespace_useful_parent_temps,namespace_parent_ready_env,
            namespace_admission_ready_env,namespace_parent_checked_env,namespace_useful_initial_temps,namespace_parameter_env;WriteAll.lookup|exact CLOSE_EFFECT].
      * eapply namespace_steps_append.
        -- apply namespace_close_phase_run with(index:=2%nat)(id:=_errors)(descriptor:=Int.repr 6)(reply:=close_ok None);
            [reflexivity|exact CLOSE|unfold namespace_created_env,namespace_useful_parent_temps,namespace_parent_ready_env,
              namespace_admission_ready_env,namespace_parent_checked_env,namespace_useful_initial_temps,namespace_parameter_env;WriteAll.lookup|exact CLOSE_EFFECT].
        -- eapply namespace_steps_append.
           ++ apply namespace_close_phase_run with(index:=3%nat)(id:=_parentfd)(descriptor:=Int.repr 3)(reply:=close_ok None);
                [reflexivity|exact CLOSE|unfold namespace_created_env,namespace_useful_parent_temps,namespace_parent_ready_env,
                  namespace_admission_ready_env,namespace_parent_checked_env,namespace_useful_initial_temps,namespace_parameter_env;WriteAll.lookup|exact CLOSE_EFFECT].
           ++ eapply namespace_steps_append.
              ** eapply namespace_store_path_actual;apply namespace_parent_child_source with(object:=childobject)(child:=Int.repr 2);
                  [exact CHILD|exact PID|change(0<=2);lia].
              ** eapply namespace_store_path_actual;apply namespace_admission_initialize_source with(status:=status);[exact STATUS|exact STORE].
  - split.
    + eapply namespace_callback_after_status;[exact CALLBACKS| | | |exact STATUS_CHILD|exact STATUS_PIPE|exact STATUS_CGROUP|exact STATUS_CHECK|exact STORE].
      all: unfold namespace_parent_ready_env,namespace_admission_ready_env,namespace_parent_checked_env,
        namespace_created_env,namespace_useful_parent_temps,namespace_useful_initial_temps,namespace_parameter_env;WriteAll.lookup.
    + namespace_useful_prefix_profile.
Qed.

Theorem namespace_useful_parent_return_to_setup cell prepared borrowed e memory childobject pipe status temporary admission:
  handoff_borrowed_input cell prepared borrowed ->e=namespace_initial_env prepared ->
  namespace_useful_callback_input cell e namespace_useful_parent_temps memory childobject pipe status temporary admission
    Int64.zero(Int.repr 100000)(Int.repr 8)Int64.zero ->
  exists events after,
    namespace_steps namespace_ge cell
      (live(Returnstate(Vint Int.zero)(namespace_creation_cont e namespace_useful_parent_temps Kstop)memory))events
      (live(State f_namespace_init(namespace_tail 20)Kstop e
        (namespace_parent_ready_env namespace_useful_parent_temps(Int.repr 2))after)) /\
    namespace_useful_callback_input cell e(namespace_parent_ready_env namespace_useful_parent_temps(Int.repr 2))after
      childobject pipe status temporary admission Int64.zero(Int.repr 100000)(Int.repr 8)Int64.zero.
Proof.
  intros INPUT CANONICAL CALLBACKS.
  destruct(namespace_useful_parent_return_to_setup_for_run Int64.zero cell prepared borrowed e memory childobject pipe
    status temporary admission INPUT CANONICAL CALLBACKS)as[events[after[RUN[OUTPUT PROFILE]]]].
  exists events,after;split;assumption.
Qed.

Theorem namespace_useful_phase9_to_setup_for_run(run:int64) cell prepared borrowed e memory childobject pipe status temporary admission:
  handoff_borrowed_input cell prepared borrowed ->e=namespace_initial_env prepared ->
  handoff_borrowed_input cell memory borrowed ->
  (forall object position kind permission,Mem.perm(namespace_initial_memory prepared)object position kind permission ->
    Mem.perm memory object position kind permission) ->
  namespace_useful_callback_input cell e namespace_useful_parent_temps memory childobject pipe status temporary admission
    run(Int.repr 100000)(Int.repr 8)Int64.zero ->
  exists pair allocated paired fork_memory parameters child_memory parent_events setup_memory,
    namespace_steps namespace_ge cell
      (live(State f_namespace_init(namespace_tail 9)Kstop e namespace_useful_parent_temps memory))
      (repeat namespace_source_event 4++namespace_child_common_log pair(Int.repr 9)(Int.repr 10))
      (live(Callstate namespace_fork_definition[]
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory)) /\
    namespace_step namespace_ge cell
      (live(Callstate namespace_fork_definition[]
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory))
      (namespace_forked(Int.repr 2))
      (live(Returnstate(Vint(Int.repr 2))
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory)) /\
    namespace_steps namespace_ge cell
      (live(Returnstate(Vint(Int.repr 2))
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory))
      (repeat namespace_source_event 4++repeat namespace_source_event 3++repeat namespace_source_event 3++
        repeat namespace_source_event 2++[namespace_close_event(Int.repr 60)(close_ok None)]++repeat namespace_source_event 3)
      (live(Returnstate(Vint Int.zero)(namespace_creation_cont e namespace_useful_parent_temps Kstop)child_memory)) /\
    namespace_steps namespace_ge cell
      (live(Returnstate(Vint Int.zero)(namespace_creation_cont e namespace_useful_parent_temps Kstop)child_memory))parent_events
      (live(State f_namespace_init(namespace_tail 20)Kstop e
        (namespace_parent_ready_env namespace_useful_parent_temps(Int.repr 2))setup_memory)) /\
    namespace_useful_callback_input cell e(namespace_parent_ready_env namespace_useful_parent_temps(Int.repr 2))setup_memory
      childobject pipe status temporary admission run(Int.repr 100000)(Int.repr 8)Int64.zero /\
    child_allocations memory pair allocated /\Mem.store Mint32 paired pipe 0(Vint(Int.repr 9))=Some fork_memory /\
    entry_errno_ready cell fork_memory /\handoff_borrowed_input cell fork_memory borrowed /\
    namespace_useful_child_input cell borrowed fork_memory parameters /\Forall namespace_parent_prefix_event parent_events.
Proof.
  intros INPUT CANONICAL BORROWED PREPARED_PERMS CALLBACKS.
  pose proof(namespace_useful_globals _ _ _ _ _ _ _ _ _ _ _ _ _ CALLBACKS)as GLOBAL.
  pose proof(namespace_useful_locals _ _ _ _ _ _ _ _ _ _ _ _ _ CALLBACKS)as[CHILD[PIPE[STATUS REST]]].
  pose proof(namespace_useful_errno _ _ _ _ _ _ _ _ _ _ _ _ _ CALLBACKS)as READY.
  destruct(namespace_callback_outputs_private _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INPUT CANONICAL CALLBACKS)
    as[CHILD_TLS[PIPE_TLS[CHILD_PIPE[CHILD_PRIVATE[PIPE_PRIVATE[CONSTANT_PRIVATE[CG_CHILD[CG_PIPE[CHECK_CHILD CHECK_PIPE]]]]]]]]].
  assert(PEER_OWNED:Mem.range_perm memory pipe 0 4 Cur Freeable).
  { destruct(namespace_owned_local_from_entry prepared _pipefd(tarray tint 2)ltac:(cbn;auto 20))
      as[other[BINDING[FRESH OWNED]]].
    rewrite(namespace_initial_env_form prepared)in BINDING;rewrite <-CANONICAL in BINDING.
    rewrite PIPE in BINDING;injection BINDING as SAME;subst other.
    change(sizeof namespace_ge(tarray tint 2))with 8 in OWNED.
    rewrite(namespace_initial_memory_form prepared)in OWNED.
    intros position BOUND;apply PREPARED_PERMS;apply OWNED;lia. }
  assert(PID_OWNED:Mem.range_perm memory childobject 0 4 Cur Freeable).
  { destruct(namespace_owned_local_from_entry prepared _child tint ltac:(cbn;auto 20))
      as[other[BINDING[FRESH OWNED]]].
    rewrite(namespace_initial_env_form prepared)in BINDING;rewrite <-CANONICAL in BINDING.
    rewrite CHILD in BINDING;injection BINDING as SAME;subst other.
    change(sizeof namespace_ge tint)with 4 in OWNED.
    rewrite(namespace_initial_memory_form prepared)in OWNED.
    intros position BOUND;apply PREPARED_PERMS;apply OWNED;exact BOUND. }
  destruct(namespace_child_useful_source_framed cell memory pipe childobject(Int.repr 4)(Int.repr 5)(Int.repr 6)
    READY PEER_OWNED PID_OWNED ltac:(intro SAME;apply CHILD_PIPE;symmetry;exact SAME)PIPE_TLS CHILD_TLS)
    as(pair &allocated &paired &fork_memory &parameters &final_temps &child_memory &ALLOC &PEER_STORE
      &COMMON &FORK &PARENT &TEMPS &CHILD_READY &PEER_VALUE &PID_VALUE &CHILD_FRAME &CHILD_PERMS
      &COMMON_READY &COMMON_FRAME &COMMON_PERMS &CHILD_ARGUMENTS).
  assert(COMMON_BORROWED:handoff_borrowed_input cell fork_memory borrowed).
  { eapply handoff_borrowed_input_framed;[exact BORROWED| |exact COMMON_READY].
    eapply Mem.unchanged_on_implies;[exact COMMON_FRAME|].
    intros object position MEMBER VALID;split.
    - pose proof(handoff_borrowed_objects_valid _ _ _ BORROWED)as OBJECTS.
      rewrite Forall_forall in OBJECTS;apply OBJECTS;exact MEMBER.
    - intro SAME;apply PIPE_PRIVATE;rewrite <-SAME;exact MEMBER. }
  assert(CHILD_CALLBACKS:namespace_useful_callback_input cell e namespace_useful_parent_temps child_memory
    childobject pipe status temporary admission run(Int.repr 100000)(Int.repr 8)Int64.zero).
  { eapply namespace_callback_after_child;[exact INPUT|exact CANONICAL|exact CALLBACKS| | | |
      exact CHILD_READY|exact PID_VALUE|exact PEER_VALUE|exact CHILD_FRAME|exact CHILD_PERMS].
    all: unfold namespace_useful_parent_temps,namespace_parent_ready_env,namespace_admission_ready_env,
      namespace_parent_checked_env,namespace_created_env,namespace_useful_initial_temps,namespace_parameter_env;WriteAll.lookup. }
  destruct(namespace_useful_parent_return_to_setup_for_run run cell prepared borrowed e child_memory childobject pipe status temporary admission
    INPUT CANONICAL CHILD_CALLBACKS)
    as[parent_events[setup_memory[PARENT_SOURCE[SETUP_CALLBACKS PARENT_PROFILE]]]].
  assert(CREATE:e!_create_entry_child=None)by(apply GLOBAL;vm_compute;reflexivity).
  pose proof(namespace_create_call_source e namespace_useful_parent_temps memory Kstop(Int.repr 4)(Int.repr 5)(Int.repr 6)
    pipe childobject CREATE PIPE CHILD
    ltac:(unfold namespace_useful_parent_temps,namespace_parent_ready_env,namespace_admission_ready_env,
      namespace_parent_checked_env,namespace_created_env,namespace_useful_initial_temps,namespace_parameter_env;WriteAll.lookup)
    ltac:(unfold namespace_useful_parent_temps,namespace_parent_ready_env,namespace_admission_ready_env,
      namespace_parent_checked_env,namespace_created_env,namespace_useful_initial_temps,namespace_parameter_env;WriteAll.lookup)
    ltac:(unfold namespace_useful_parent_temps,namespace_parent_ready_env,namespace_admission_ready_env,
      namespace_parent_checked_env,namespace_created_env,namespace_useful_initial_temps,namespace_parameter_env;WriteAll.lookup)
    ltac:(unfold namespace_useful_parent_temps,namespace_parent_ready_env,namespace_admission_ready_env,
      namespace_parent_checked_env,namespace_created_env,namespace_useful_initial_temps,namespace_parameter_env;WriteAll.lookup))as CALL.
  exists pair,allocated,paired,fork_memory,parameters,child_memory,parent_events,setup_memory.
  split.
  - eapply namespace_steps_append;[eapply namespace_store_path_actual;exact CALL|].
    exact(namespace_plug_actual_steps _ _ _ _ _ (namespace_creation_cont e namespace_useful_parent_temps Kstop)I COMMON).
  - split.
    + exact(NamespaceContexts.plug_namespace_step _ _ _ _ _ (namespace_creation_cont e namespace_useful_parent_temps Kstop)I FORK).
    + split.
      * exact(namespace_plug_actual_steps _ _ _ _ _ (namespace_creation_cont e namespace_useful_parent_temps Kstop)I PARENT).
      * split;[exact PARENT_SOURCE|]. split;[exact SETUP_CALLBACKS|].
        split;[exact ALLOC|]. split;[exact PEER_STORE|]. split;[exact COMMON_READY|].
        split;[exact COMMON_BORROWED|]. split;[exists childobject;split;assumption|exact PARENT_PROFILE].
Qed.

Theorem namespace_useful_phase9_to_setup cell prepared borrowed e memory childobject pipe status temporary admission:
  handoff_borrowed_input cell prepared borrowed ->e=namespace_initial_env prepared ->
  handoff_borrowed_input cell memory borrowed ->
  (forall object position kind permission,Mem.perm(namespace_initial_memory prepared)object position kind permission ->
    Mem.perm memory object position kind permission) ->
  namespace_useful_callback_input cell e namespace_useful_parent_temps memory childobject pipe status temporary admission
    Int64.zero(Int.repr 100000)(Int.repr 8)Int64.zero ->
  exists pair allocated paired fork_memory parameters child_memory parent_events setup_memory,
    namespace_steps namespace_ge cell
      (live(State f_namespace_init(namespace_tail 9)Kstop e namespace_useful_parent_temps memory))
      (repeat namespace_source_event 4++namespace_child_common_log pair(Int.repr 9)(Int.repr 10))
      (live(Callstate namespace_fork_definition[]
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory)) /\
    namespace_step namespace_ge cell
      (live(Callstate namespace_fork_definition[]
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory))
      (namespace_forked(Int.repr 2))
      (live(Returnstate(Vint(Int.repr 2))
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory)) /\
    namespace_steps namespace_ge cell
      (live(Returnstate(Vint(Int.repr 2))
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory))
      (repeat namespace_source_event 4++repeat namespace_source_event 3++repeat namespace_source_event 3++
        repeat namespace_source_event 2++[namespace_close_event(Int.repr 60)(close_ok None)]++repeat namespace_source_event 3)
      (live(Returnstate(Vint Int.zero)(namespace_creation_cont e namespace_useful_parent_temps Kstop)child_memory)) /\
    namespace_steps namespace_ge cell
      (live(Returnstate(Vint Int.zero)(namespace_creation_cont e namespace_useful_parent_temps Kstop)child_memory))parent_events
      (live(State f_namespace_init(namespace_tail 20)Kstop e
        (namespace_parent_ready_env namespace_useful_parent_temps(Int.repr 2))setup_memory)) /\
    namespace_useful_callback_input cell e(namespace_parent_ready_env namespace_useful_parent_temps(Int.repr 2))setup_memory
      childobject pipe status temporary admission Int64.zero(Int.repr 100000)(Int.repr 8)Int64.zero /\
    child_allocations memory pair allocated /\Mem.store Mint32 paired pipe 0(Vint(Int.repr 9))=Some fork_memory /\
    entry_errno_ready cell fork_memory /\handoff_borrowed_input cell fork_memory borrowed.
Proof.
  intros INPUT CANONICAL BORROWED PERMISSIONS CALLBACKS.
  destruct(namespace_useful_phase9_to_setup_for_run Int64.zero cell prepared borrowed e memory childobject pipe
    status temporary admission INPUT CANONICAL BORROWED PERMISSIONS CALLBACKS)
    as(pair &allocated &paired &fork_memory &parameters &child_memory &parent_events &setup_memory
      &COMMON &FORK &PARENT &PARENT_SOURCE &SETUP_CALLBACKS &ALLOC &PEER_STORE &READY &COMMON_BORROWED &CHILD_ARGUMENTS &PARENT_PROFILE).
  exists pair,allocated,paired,fork_memory,parameters,child_memory,parent_events,setup_memory.
  split;[exact COMMON|]. split;[exact FORK|]. split;[exact PARENT|]. split;[exact PARENT_SOURCE|].
  split;[exact SETUP_CALLBACKS|]. split;[exact ALLOC|]. split;[exact PEER_STORE|]. split;assumption.
Qed.

Theorem namespace_useful_callbacks_ready_shaped cell e le memory childobject pipe status temporary admission run uid sequence:
  namespace_useful_callback_input cell e le memory childobject pipe status temporary admission run uid(Int.repr 8)sequence ->
  exists events final,
    namespace_steps namespace_ge cell(live(State f_namespace_init(namespace_tail 20)Kstop e le memory))events
      (live(Callstate(Internal f_release_child)[Vint(Int.repr 2);Vint(Int.repr 9)]
        (namespace_release_cont e(namespace_useful_published_env le sequence)(Int.repr 2)(Int.repr 9)Kstop)final)) /\
    entry_errno_ready cell final /\
    inhabited(NamespaceCallbackShape cell memory status admission(Int.repr 8)sequence events).
Proof.
  intro INPUT.
  assert(SENDER:forall before,
    EntryReporting.SenderProgram.sender_input cell before admission 0(namespace_admitted_record run uid(Int64.repr 1000))
      (repeat Byte.zero 32)(handoff_global_address ___stringlit_1)NativeHandoffInitial.handoff_normal_bytes
      (fun tag=>handoff_symbol(EntryReporting.SenderSelectors.report_literal tag)) ->entry_errno_ready cell before ->
    exists events after,library_steps EntryReporting.ResultLayout.result_ge cell
      (live(EntryReporting.SenderSource.sender_initial(Int.repr 8)sequence admission 0 Kstop before))events
      (live(Returnstate(Vint Int.zero)Kstop after)) /\entry_errno_ready cell after).
  { intros before OWN READY.
    exact(admitted_sender_returns_ready cell before sequence admission run uid(Int64.repr 1000)(repeat Byte.zero 32)
      (handoff_global_address ___stringlit_1)NativeHandoffInitial.handoff_normal_bytes
      (fun tag=>handoff_symbol(EntryReporting.SenderSelectors.report_literal tag))OWN READY). }
  exact(namespace_useful_callbacks_reach_release_shaped cell e le memory childobject pipe status temporary admission
    run uid(Int.repr 8)sequence(entry_errno_ready cell)SENDER INPUT).
Qed.

Theorem namespace_useful_callbacks_ready cell e le memory childobject pipe status temporary admission run uid sequence:
  namespace_useful_callback_input cell e le memory childobject pipe status temporary admission run uid(Int.repr 8)sequence ->
  exists events final,
    namespace_steps namespace_ge cell(live(State f_namespace_init(namespace_tail 20)Kstop e le memory))events
      (live(Callstate(Internal f_release_child)[Vint(Int.repr 2);Vint(Int.repr 9)]
        (namespace_release_cont e(namespace_useful_published_env le sequence)(Int.repr 2)(Int.repr 9)Kstop)final)) /\
    entry_errno_ready cell final.
Proof.
  intro INPUT;destruct(namespace_useful_callbacks_ready_shaped cell e le memory childobject pipe status temporary admission
    run uid sequence INPUT)as[events[final[RUN[READY SHAPE]]]].
  exists events,final;split;assumption.
Qed.

Theorem namespace_ready_release_source_shaped_owned cell e le before sequence:
  entry_errno_ready cell before ->
  exists events after request,
    namespace_steps namespace_ge cell
      (live(Callstate(Internal f_release_child)[Vint(Int.repr 2);Vint(Int.repr 9)]
        (namespace_release_cont e(namespace_useful_published_env le sequence)(Int.repr 2)(Int.repr 9)Kstop)before))
      (map namespace_process events)
      (live(Returnstate(Vint Int.zero)
        (namespace_release_cont e(namespace_useful_published_env le sequence)(Int.repr 2)(Int.repr 9)Kstop)after)) /\
    descriptor request=Int.repr 9 /\operation request=writing /\
    In(process_entry(entry_library(original_event(io_step request(transfer[Byte.repr 165]None)))))events /\events=release_useful_events(Int.repr 2)request.
Proof.
  intro READY;destruct(release_useful_source_execution_shaped_owned cell before(Int.repr 2)(Int.repr 9)READY)
    as[events[after[RUN[request[DESCRIPTOR[WRITING[WRITE SHAPE]]]]]]].
  pose proof(namespace_process_steps_preserved _ _ _ _ _ RUN)as LIFTED.
  rewrite namespace_launch_process_environment in LIFTED.
  exists events,after,request;split.
  - exact(namespace_plug_actual_steps _ _ _ _ _
      (namespace_release_cont e(namespace_useful_published_env le sequence)(Int.repr 2)(Int.repr 9)Kstop)I LIFTED).
  - split;[exact DESCRIPTOR|]. split;[exact WRITING|]. split;assumption.
Qed.

Theorem namespace_ready_release_source_shaped cell e le before sequence:
  entry_errno_ready cell before ->
  exists events after request,
    namespace_steps namespace_ge cell
      (live(Callstate(Internal f_release_child)[Vint(Int.repr 2);Vint(Int.repr 9)]
        (namespace_release_cont e(namespace_useful_published_env le sequence)(Int.repr 2)(Int.repr 9)Kstop)before))
      (map namespace_process events)
      (live(Returnstate(Vint Int.zero)
        (namespace_release_cont e(namespace_useful_published_env le sequence)(Int.repr 2)(Int.repr 9)Kstop)after)) /\
    descriptor request=Int.repr 9 /\
    In(process_entry(entry_library(original_event(io_step request(transfer[Byte.repr 165]None)))))events /\events=release_useful_events(Int.repr 2)request.
Proof.
  intro READY;destruct(namespace_ready_release_source_shaped_owned cell e le before sequence READY)
    as(events &after &request &RUN &DESCRIPTOR &WRITING &WRITE &SHAPE).
  exists events,after,request;split;[exact RUN|]. split;[exact DESCRIPTOR|]. split;assumption.
Qed.

Theorem namespace_ready_release_source cell e le before sequence:
  entry_errno_ready cell before ->
  exists events after request,
    namespace_steps namespace_ge cell
      (live(Callstate(Internal f_release_child)[Vint(Int.repr 2);Vint(Int.repr 9)]
        (namespace_release_cont e(namespace_useful_published_env le sequence)(Int.repr 2)(Int.repr 9)Kstop)before))
      (map namespace_process events)
      (live(Returnstate(Vint Int.zero)
        (namespace_release_cont e(namespace_useful_published_env le sequence)(Int.repr 2)(Int.repr 9)Kstop)after)) /\
    descriptor request=Int.repr 9 /\
    In(process_entry(entry_library(original_event(io_step request(transfer[Byte.repr 165]None)))))events.
Proof.
  intro READY;destruct(namespace_ready_release_source_shaped cell e le before sequence READY)
    as(events &after &request &RUN &DESCRIPTOR &WRITE &SHAPE).
  exists events,after,request;split;[exact RUN|]. split;assumption.
Qed.

Definition namespace_useful_release_temps:=
  namespace_useful_published_env(namespace_parent_ready_env namespace_useful_parent_temps(Int.repr 2))Int64.zero.

Record NamespaceUsefulParentShape cell e pair parameters before suffix final request:Type:={
  useful_parent_prefix:list namespace_event;
  useful_callback_before:mem;
  useful_callback_status:block;
  useful_callback_admission:block;
  useful_callbacks:list namespace_event;
  useful_before_release:mem;
  useful_release_events:list process_event;
  useful_prefix_source:namespace_steps namespace_ge cell
    (live(Returnstate(Vint(Int.repr 2))
      (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))before))
    useful_parent_prefix(live(State f_namespace_init(namespace_tail 20)Kstop e
      (namespace_parent_ready_env namespace_useful_parent_temps(Int.repr 2))useful_callback_before));
  useful_prefix_profile:Forall namespace_parent_prefix_event useful_parent_prefix;
  useful_callback_source:namespace_steps namespace_ge cell
    (live(State f_namespace_init(namespace_tail 20)Kstop e
      (namespace_parent_ready_env namespace_useful_parent_temps(Int.repr 2))useful_callback_before))useful_callbacks
    (live(Callstate(Internal f_release_child)[Vint(Int.repr 2);Vint(Int.repr 9)]
      (namespace_release_cont e namespace_useful_release_temps(Int.repr 2)(Int.repr 9)Kstop)useful_before_release));
  useful_callback_shape:NamespaceCallbackShape cell useful_callback_before useful_callback_status
    useful_callback_admission(Int.repr 8)Int64.zero useful_callbacks;
  useful_release_ready:entry_errno_ready cell useful_before_release;
  useful_release_source:namespace_steps namespace_ge cell
    (live(Callstate(Internal f_release_child)[Vint(Int.repr 2);Vint(Int.repr 9)]
      (namespace_release_cont e namespace_useful_release_temps(Int.repr 2)(Int.repr 9)Kstop)useful_before_release))
    (map namespace_process useful_release_events)
    (live(Returnstate(Vint Int.zero)(namespace_release_cont e namespace_useful_release_temps(Int.repr 2)(Int.repr 9)Kstop)final));
  useful_release_shape:useful_release_events=release_useful_events(Int.repr 2)request;
  useful_request_descriptor:descriptor request=Int.repr 9;
  useful_request_writing:operation request=writing;
  useful_parent_event_order:suffix=useful_parent_prefix++useful_callbacks++map namespace_process useful_release_events
}.

Definition namespace_useful_preparation cell command source prepared e memory run:Prop:=
  (forall object position kind permission,Mem.perm(namespace_initial_memory prepared)object position kind permission ->
    Mem.perm memory object position kind permission) /\
  handoff_borrowed_input cell memory(handoff_fixture_input command source) /\
  exists childobject pipe status temporary admission,
    namespace_useful_callback_input cell e namespace_useful_parent_temps memory childobject pipe status temporary admission
      run(Int.repr 100000)(Int.repr 8)Int64.zero.

Theorem namespace_actual_local_grant_for_run_shaped_prepared(run:int64):
  exists initial cell command source prepared e memory pair fork_memory parameters suffix final request,
    Globalenvs.Genv.init_mem EntrySource.prog=Some initial /\
    handoff_borrowed_input cell prepared(handoff_fixture_input command source) /\
    e=namespace_initial_env prepared /\
    Mem.load Mint64 memory(handoff_symbol _run_id)0=Some(Vlong run) /\
    namespace_steps namespace_ge cell
      (live(State f_namespace_init(namespace_tail 9)Kstop e namespace_useful_parent_temps memory))
      (repeat namespace_source_event 4++namespace_child_common_log pair(Int.repr 9)(Int.repr 10))
      (live(Callstate namespace_fork_definition[]
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory)) /\
    entry_errno_ready cell fork_memory /\handoff_borrowed_input cell fork_memory(handoff_fixture_input command source) /\
    namespace_useful_child_input cell(handoff_fixture_input command source)fork_memory parameters /\
    namespace_step namespace_ge cell
      (live(Callstate namespace_fork_definition[]
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory))
      (namespace_forked(Int.repr 2))
      (live(Returnstate(Vint(Int.repr 2))
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory)) /\
    namespace_step namespace_ge cell
      (live(Callstate namespace_fork_definition[]
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory))
      (namespace_forked Int.zero)
      (live(Returnstate(Vint Int.zero)
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory)) /\
    namespace_steps namespace_ge cell
      (live(Returnstate(Vint(Int.repr 2))
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory))suffix
      (live(Returnstate(Vint Int.zero)
        (namespace_release_cont e namespace_useful_release_temps(Int.repr 2)(Int.repr 9)Kstop)final)) /\
    descriptor request=Int.repr 9 /\
    In(namespace_process(process_entry(entry_library(original_event(io_step request(transfer[Byte.repr 165]None))))))suffix /\
    inhabited(NamespaceUsefulParentShape cell e pair parameters fork_memory suffix final request) /\
    namespace_useful_preparation cell command source prepared e memory run.
Proof.
  destruct(namespace_actual_callback_input_for_run run)as(initial &cell &command &source &prepared &e &childobject &pipe
    &status &temporary &admission &memory &INITIAL &INPUT &CANONICAL &PERMISSIONS &BORROWED &CALLBACKS).
  pose proof(namespace_useful_constants _ _ _ _ _ _ _ _ _ _ _ _ _ CALLBACKS)as CONSTANTS.
  pose proof(proj1(namespace_constant_result _ _ _ CONSTANTS))as RUN_VALUE.
  destruct(namespace_useful_phase9_to_setup_for_run run cell prepared(handoff_fixture_input command source)e memory
    childobject pipe status temporary admission INPUT CANONICAL BORROWED PERMISSIONS CALLBACKS)
    as(pair &allocated &paired &fork_memory &parameters &child_memory &parent_events &setup_memory
      &COMMON &FORK &PARENT &PARENT_SOURCE &SETUP_CALLBACKS &ALLOC &PEER_STORE &COMMON_READY &COMMON_BORROWED &CHILD_ARGUMENTS &PARENT_PROFILE).
  destruct(namespace_useful_callbacks_ready_shaped cell e(namespace_parent_ready_env namespace_useful_parent_temps(Int.repr 2))setup_memory
    childobject pipe status temporary admission run(Int.repr 100000)Int64.zero SETUP_CALLBACKS)
    as(callbacks &before_release &CALLBACK_RUN &RELEASE_READY &CALLBACK_SHAPE).
  destruct CALLBACK_SHAPE as[CALLBACK_SHAPE].
  destruct(namespace_ready_release_source_shaped_owned cell e(namespace_parent_ready_env namespace_useful_parent_temps(Int.repr 2))before_release Int64.zero
    RELEASE_READY)as(release_events &final &request &RELEASE_RUN &DESCRIPTOR &WRITING &WRITE &RELEASE_SHAPE).
  set(prefix:=(repeat namespace_source_event 4++repeat namespace_source_event 3++repeat namespace_source_event 3++
    repeat namespace_source_event 2++[namespace_close_event(Int.repr 60)(close_ok None)]++repeat namespace_source_event 3)++parent_events).
  assert(PREFIX_SOURCE:namespace_steps namespace_ge cell
    (live(Returnstate(Vint(Int.repr 2))
      (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory))prefix
    (live(State f_namespace_init(namespace_tail 20)Kstop e(namespace_parent_ready_env namespace_useful_parent_temps(Int.repr 2))setup_memory))).
  { unfold prefix;eapply namespace_steps_append;[exact PARENT|exact PARENT_SOURCE]. }
  assert(PREFIX_PROFILE:Forall namespace_parent_prefix_event prefix).
  { unfold prefix;apply Forall_app;split;[namespace_useful_prefix_profile|exact PARENT_PROFILE]. }
  assert(PREPARATION:namespace_useful_preparation cell command source prepared e memory run).
  { split;[exact PERMISSIONS|]. split;[exact BORROWED|].
    exists childobject,pipe,status,temporary,admission;exact CALLBACKS. }
  exists initial,cell,command,source,prepared,e,memory,pair,fork_memory,parameters,
    ((repeat namespace_source_event 4++repeat namespace_source_event 3++repeat namespace_source_event 3++
      repeat namespace_source_event 2++[namespace_close_event(Int.repr 60)(close_ok None)]++repeat namespace_source_event 3)++
      parent_events++callbacks++map namespace_process release_events),final,request.
  split;[exact INITIAL|]. split;[exact INPUT|]. split;[exact CANONICAL|]. split;[exact RUN_VALUE|]. split;[exact COMMON|].
  split;[exact COMMON_READY|]. split;[exact COMMON_BORROWED|]. split;[exact CHILD_ARGUMENTS|]. split;[exact FORK|]. split.
  - apply namespace_fork_step;[apply namespace_partial_refl|exact COMMON_READY].
  - split.
    + eapply namespace_steps_append;[exact PARENT|].
      eapply namespace_steps_append;[exact PARENT_SOURCE|].
      eapply namespace_steps_append;[exact CALLBACK_RUN|]. exact RELEASE_RUN.
    + split;[exact DESCRIPTOR|]. split.
      * apply in_or_app;right;apply in_or_app;right;apply in_or_app;right.
        apply in_map;exact WRITE.
      * split.
        -- constructor.
           refine{|useful_parent_prefix:=prefix;useful_callback_before:=setup_memory;
          useful_callback_status:=status;useful_callback_admission:=admission;useful_callbacks:=callbacks;
          useful_before_release:=before_release;useful_release_events:=release_events;
          useful_prefix_source:=PREFIX_SOURCE;useful_prefix_profile:=PREFIX_PROFILE;
          useful_callback_source:=CALLBACK_RUN;useful_callback_shape:=CALLBACK_SHAPE;
          useful_release_ready:=RELEASE_READY;useful_release_source:=RELEASE_RUN;
          useful_release_shape:=RELEASE_SHAPE;useful_request_descriptor:=DESCRIPTOR;useful_request_writing:=WRITING|}.
           unfold prefix;repeat rewrite <-app_assoc;reflexivity.
        -- exact PREPARATION.
Qed.

Theorem namespace_actual_local_grant_for_run_shaped(run:int64):
  exists initial cell command source prepared e memory pair fork_memory parameters suffix final request,
    Globalenvs.Genv.init_mem EntrySource.prog=Some initial /\
    handoff_borrowed_input cell prepared(handoff_fixture_input command source) /\
    e=namespace_initial_env prepared /\
    Mem.load Mint64 memory(handoff_symbol _run_id)0=Some(Vlong run) /\
    namespace_steps namespace_ge cell
      (live(State f_namespace_init(namespace_tail 9)Kstop e namespace_useful_parent_temps memory))
      (repeat namespace_source_event 4++namespace_child_common_log pair(Int.repr 9)(Int.repr 10))
      (live(Callstate namespace_fork_definition[]
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory)) /\
    entry_errno_ready cell fork_memory /\handoff_borrowed_input cell fork_memory(handoff_fixture_input command source) /\
    namespace_useful_child_input cell(handoff_fixture_input command source)fork_memory parameters /\
    namespace_step namespace_ge cell
      (live(Callstate namespace_fork_definition[]
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory))
      (namespace_forked(Int.repr 2))
      (live(Returnstate(Vint(Int.repr 2))
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory)) /\
    namespace_step namespace_ge cell
      (live(Callstate namespace_fork_definition[]
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory))
      (namespace_forked Int.zero)
      (live(Returnstate(Vint Int.zero)
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory)) /\
    namespace_steps namespace_ge cell
      (live(Returnstate(Vint(Int.repr 2))
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory))suffix
      (live(Returnstate(Vint Int.zero)
        (namespace_release_cont e namespace_useful_release_temps(Int.repr 2)(Int.repr 9)Kstop)final)) /\
    descriptor request=Int.repr 9 /\
    In(namespace_process(process_entry(entry_library(original_event(io_step request(transfer[Byte.repr 165]None))))))suffix /\
    inhabited(NamespaceUsefulParentShape cell e pair parameters fork_memory suffix final request).
Proof.
  destruct(namespace_actual_local_grant_for_run_shaped_prepared run)as(initial &cell &command &source &prepared &e &memory &pair
    &fork_memory &parameters &suffix &final &request &INITIAL &INPUT &CANONICAL &RUN_VALUE &COMMON &READY &BORROWED
    &ARGUMENTS &PARENT &CHILD &GRANT &DESCRIPTOR &WRITE &SHAPE &PREPARATION).
  exists initial,cell,command,source,prepared,e,memory,pair,fork_memory,parameters,suffix,final,request.
  repeat match goal with H:?P|-?P /\_=>split;[exact H|]end.
  exact SHAPE.
Qed.

Theorem namespace_actual_local_grant_for_run(run:int64):
  exists initial cell command source prepared e memory pair fork_memory parameters suffix final request,
    Globalenvs.Genv.init_mem EntrySource.prog=Some initial /\
    handoff_borrowed_input cell prepared(handoff_fixture_input command source) /\
    e=namespace_initial_env prepared /\
    Mem.load Mint64 memory(handoff_symbol _run_id)0=Some(Vlong run) /\
    namespace_steps namespace_ge cell
      (live(State f_namespace_init(namespace_tail 9)Kstop e namespace_useful_parent_temps memory))
      (repeat namespace_source_event 4++namespace_child_common_log pair(Int.repr 9)(Int.repr 10))
      (live(Callstate namespace_fork_definition[]
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory)) /\
    entry_errno_ready cell fork_memory /\handoff_borrowed_input cell fork_memory(handoff_fixture_input command source) /\
    namespace_useful_child_input cell(handoff_fixture_input command source)fork_memory parameters /\
    namespace_step namespace_ge cell
      (live(Callstate namespace_fork_definition[]
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory))
      (namespace_forked(Int.repr 2))
      (live(Returnstate(Vint(Int.repr 2))
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory)) /\
    namespace_step namespace_ge cell
      (live(Callstate namespace_fork_definition[]
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory))
      (namespace_forked Int.zero)
      (live(Returnstate(Vint Int.zero)
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory)) /\
    namespace_steps namespace_ge cell
      (live(Returnstate(Vint(Int.repr 2))
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory))suffix
      (live(Returnstate(Vint Int.zero)
        (namespace_release_cont e namespace_useful_release_temps(Int.repr 2)(Int.repr 9)Kstop)final)) /\
    descriptor request=Int.repr 9 /\
    In(namespace_process(process_entry(entry_library(original_event(io_step request(transfer[Byte.repr 165]None))))))suffix.
Proof.
  destruct(namespace_actual_local_grant_for_run_shaped run)as(initial &cell &command &source &prepared &e &memory &pair
    &fork_memory &parameters &suffix &final &request &INITIAL &INPUT &CANONICAL &RUN_VALUE &COMMON &READY &BORROWED
    &ARGUMENTS &PARENT &CHILD &GRANT &DESCRIPTOR &WRITE &SHAPE).
  exists initial,cell,command,source,prepared,e,memory,pair,fork_memory,parameters,suffix,final,request.
  repeat match goal with H:?P|-?P /\_=>split;[exact H|]end.
  exact WRITE.
Qed.

Theorem namespace_actual_local_grant:
  exists initial cell command source prepared e memory pair fork_memory parameters suffix final request,
    Globalenvs.Genv.init_mem EntrySource.prog=Some initial /\
    handoff_borrowed_input cell prepared(handoff_fixture_input command source) /\
    e=namespace_initial_env prepared /\
    namespace_steps namespace_ge cell
      (live(State f_namespace_init(namespace_tail 9)Kstop e namespace_useful_parent_temps memory))
      (repeat namespace_source_event 4++namespace_child_common_log pair(Int.repr 9)(Int.repr 10))
      (live(Callstate namespace_fork_definition[]
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory)) /\
    entry_errno_ready cell fork_memory /\handoff_borrowed_input cell fork_memory(handoff_fixture_input command source) /\
    namespace_step namespace_ge cell
      (live(Callstate namespace_fork_definition[]
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory))
      (namespace_forked(Int.repr 2))
      (live(Returnstate(Vint(Int.repr 2))
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory)) /\
    namespace_step namespace_ge cell
      (live(Callstate namespace_fork_definition[]
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory))
      (namespace_forked Int.zero)
      (live(Returnstate(Vint Int.zero)
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory)) /\
    namespace_steps namespace_ge cell
      (live(Returnstate(Vint(Int.repr 2))
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory))suffix
      (live(Returnstate(Vint Int.zero)
        (namespace_release_cont e namespace_useful_release_temps(Int.repr 2)(Int.repr 9)Kstop)final)) /\
    descriptor request=Int.repr 9 /\
    In(namespace_process(process_entry(entry_library(original_event(io_step request(transfer[Byte.repr 165]None))))))suffix.
Proof.
  destruct(namespace_actual_local_grant_for_run Int64.zero)as(initial &cell &command &source &prepared &e &memory &pair
    &fork_memory &parameters &suffix &final &request &INITIAL &INPUT &CANONICAL &RUN_VALUE &COMMON &READY &BORROWED
    &CHILD_ARGUMENTS &PARENT &CHILD &GRANT &DESCRIPTOR &WRITE).
  exists initial,cell,command,source,prepared,e,memory,pair,fork_memory,parameters,suffix,final,request.
  split;[exact INITIAL|]. split;[exact INPUT|]. split;[exact CANONICAL|]. split;[exact COMMON|].
  split;[exact READY|]. split;[exact BORROWED|]. split;[exact PARENT|]. split;[exact CHILD|].
  split;[exact GRANT|]. split;assumption.
Qed.
