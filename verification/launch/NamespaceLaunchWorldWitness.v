(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.acceptance: Useful source entry and both fork branches share one private channel. *)
From Stdlib Require Import ZArith List.
From compcert Require Import AST Integers Values Memory Globalenvs Ctypes Clight.
Require Import IO Machine LibraryMachine ProcessEffects.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffArguments NativeHandoffInput
  NativeHandoffInputWitness.
From EntryProcess Require Import ProcessMachine ProcessCaller ProcessPreparedOrigins.
From EntryNamespace Require Import NamespaceMachine NamespacePaths NamespaceCaller NamespaceRelease NamespacePrepared
  NamespaceStructure NamespaceAllocation
  NamespaceObjects NamespaceKernel NamespaceWorldTrace NamespaceChannel NamespaceQueue NamespaceFork
  NamespaceParentInput NamespaceForkWitness NamespaceForkWorldWitness NamespaceLaunchWitness.
Import ListNotations.
Open Scope Z_scope.

Lemma namespace_useful_prepared_source_started prepared memory:
  caller_source_machine(live(State f_namespace_init(namespace_tail 9)Kstop
    (namespace_initial_env prepared)namespace_useful_parent_temps memory)).
Proof.
  destruct(namespace_allocate_variables_source(fn_vars f_namespace_init)empty_env prepared)as[VARIABLES ALLOCATIONS].
  rewrite(namespace_initial_env_form prepared)in VARIABLES.
  eapply caller_namespace_prepared_frontier;exact VARIABLES.
Qed.

Lemma namespace_useful_phase9_queue pair queues:
  namespace_queue_steps namespace_queue_model fork_fixture_initial queues
    (repeat namespace_source_event 4++namespace_child_common_log pair(Int.repr 9)(Int.repr 10))
    fork_fixture_world(fork_fixture_reset queues).
Proof.
  cbn[repeat app];do 4(eapply namespace_queue_cons;
    [eapply namespace_queue_other;
      [apply namespace_kernel_source|intros;discriminate|intros;reflexivity]|]).
  apply namespace_useful_common_queue.
Qed.

Theorem namespace_actual_local_grant_owned_shaped_prepared:
  exists initial cell command source prepared e memory pair fork_memory parameters suffix final request,
    Genv.init_mem EntrySource.prog=Some initial /\
    handoff_borrowed_input cell prepared(handoff_fixture_input command source) /\
    e=namespace_initial_env prepared /\
    Mem.load Mint64 memory(handoff_symbol _run_id)0=Some(Vlong Int64.one) /\
    caller_source_machine(live(State f_namespace_init(namespace_tail 9)Kstop e
      namespace_useful_parent_temps memory)) /\
    namespace_steps namespace_ge cell
      (live(State f_namespace_init(namespace_tail 9)Kstop e namespace_useful_parent_temps memory))
      (repeat namespace_source_event 4++namespace_child_common_log pair(Int.repr 9)(Int.repr 10))
      (live(Callstate namespace_fork_definition[]
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory)) /\
    namespace_queue_steps namespace_queue_model fork_fixture_initial(fun _=>channel_empty)
      (repeat namespace_source_event 4++namespace_child_common_log pair(Int.repr 9)(Int.repr 10))
      fork_fixture_world(fork_fixture_reset(fun _=>channel_empty)) /\
    fork_fixture_reset(fun _=>channel_empty)60%nat=channel_empty /\
    fork_matches fork_fixture_world fork_fixture_snapshot /\
    NativeForkCopy cell fork_memory fork_memory fork_memory /\
    handoff_borrowed_input cell fork_memory(handoff_fixture_input command source) /\
    namespace_useful_child_input cell(handoff_fixture_input command source)fork_memory parameters /\
    namespace_step namespace_ge cell
      (live(Callstate namespace_fork_definition[]
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory))
      (namespace_forked(Int.repr 2))
      (live(Returnstate(Vint(Int.repr 2))
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory)) /\
    namespace_fork_effect fork_fixture_world fork_fixture_snapshot(Int.repr 2)fork_fixture_world /\
    namespace_step namespace_ge cell
      (live(Callstate namespace_fork_definition[]
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory))
      (namespace_forked Int.zero)
      (live(Returnstate(Vint Int.zero)
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory)) /\
    namespace_fork_effect fork_fixture_world fork_fixture_snapshot Int.zero
      (namespace_fork_child fork_fixture_world fork_fixture_snapshot) /\
    namespace_steps namespace_ge cell
      (live(Returnstate(Vint(Int.repr 2))
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory))suffix
      (live(Returnstate(Vint Int.zero)
        (namespace_release_cont e namespace_useful_release_temps(Int.repr 2)(Int.repr 9)Kstop)final)) /\
    descriptor request=Int.repr 9 /\
    In(namespace_process(process_entry(entry_library(original_event(io_step request(transfer[Byte.repr 165]None))))))suffix /\
    inhabited(NamespaceUsefulParentShape cell e pair parameters fork_memory suffix final request) /\
    namespace_useful_preparation cell command source prepared e memory Int64.one.
Proof.
  destruct(namespace_actual_local_grant_for_run_shaped_prepared Int64.one)as(initial &cell &command &source &prepared &e &memory &pair &fork_memory
    &parameters &suffix &final &request &INITIAL &INPUT &CANONICAL &RUN_VALUE &COMMON &READY &BORROWED &CHILD_ARGUMENTS &PARENT &CHILD &GRANT
    &DESCRIPTOR &WRITE &SHAPE &PREPARATION).
  destruct namespace_useful_common_fork as[MATCH[ACTION[MASK[PARENT_EFFECT CHILD_EFFECT]]]].
  exists initial,cell,command,source,prepared,e,memory,pair,fork_memory,parameters,suffix,final,request.
  split;[exact INITIAL|]. split;[exact INPUT|]. split;[exact CANONICAL|]. split;[exact RUN_VALUE|].
  split;[rewrite CANONICAL;apply namespace_useful_prepared_source_started|]. split;[exact COMMON|].
  split;[apply namespace_useful_phase9_queue|]. split;[reflexivity|]. split;[exact MATCH|].
  split;[apply namespace_useful_fork_copy;exact READY|]. split;[exact BORROWED|].
  split;[exact CHILD_ARGUMENTS|].
  split;[exact PARENT|]. split;[exact PARENT_EFFECT|]. split;[exact CHILD|].
  split;[exact CHILD_EFFECT|]. split;[exact GRANT|]. split;[exact DESCRIPTOR|]. split;[exact WRITE|]. split;assumption.
Qed.

Theorem namespace_actual_local_grant_owned_shaped:
  exists initial cell command source prepared e memory pair fork_memory parameters suffix final request,
    Genv.init_mem EntrySource.prog=Some initial /\
    handoff_borrowed_input cell prepared(handoff_fixture_input command source) /\
    e=namespace_initial_env prepared /\
    Mem.load Mint64 memory(handoff_symbol _run_id)0=Some(Vlong Int64.one) /\
    caller_source_machine(live(State f_namespace_init(namespace_tail 9)Kstop e
      namespace_useful_parent_temps memory)) /\
    namespace_steps namespace_ge cell
      (live(State f_namespace_init(namespace_tail 9)Kstop e namespace_useful_parent_temps memory))
      (repeat namespace_source_event 4++namespace_child_common_log pair(Int.repr 9)(Int.repr 10))
      (live(Callstate namespace_fork_definition[]
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory)) /\
    namespace_queue_steps namespace_queue_model fork_fixture_initial(fun _=>channel_empty)
      (repeat namespace_source_event 4++namespace_child_common_log pair(Int.repr 9)(Int.repr 10))
      fork_fixture_world(fork_fixture_reset(fun _=>channel_empty)) /\
    fork_fixture_reset(fun _=>channel_empty)60%nat=channel_empty /\
    fork_matches fork_fixture_world fork_fixture_snapshot /\
    NativeForkCopy cell fork_memory fork_memory fork_memory /\
    handoff_borrowed_input cell fork_memory(handoff_fixture_input command source) /\
    namespace_useful_child_input cell(handoff_fixture_input command source)fork_memory parameters /\
    namespace_step namespace_ge cell
      (live(Callstate namespace_fork_definition[]
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory))
      (namespace_forked(Int.repr 2))
      (live(Returnstate(Vint(Int.repr 2))
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory)) /\
    namespace_fork_effect fork_fixture_world fork_fixture_snapshot(Int.repr 2)fork_fixture_world /\
    namespace_step namespace_ge cell
      (live(Callstate namespace_fork_definition[]
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory))
      (namespace_forked Int.zero)
      (live(Returnstate(Vint Int.zero)
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory)) /\
    namespace_fork_effect fork_fixture_world fork_fixture_snapshot Int.zero
      (namespace_fork_child fork_fixture_world fork_fixture_snapshot) /\
    namespace_steps namespace_ge cell
      (live(Returnstate(Vint(Int.repr 2))
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory))suffix
      (live(Returnstate(Vint Int.zero)
        (namespace_release_cont e namespace_useful_release_temps(Int.repr 2)(Int.repr 9)Kstop)final)) /\
    descriptor request=Int.repr 9 /\
    In(namespace_process(process_entry(entry_library(original_event(io_step request(transfer[Byte.repr 165]None))))))suffix /\
    inhabited(NamespaceUsefulParentShape cell e pair parameters fork_memory suffix final request).
Proof.
  destruct namespace_actual_local_grant_owned_shaped_prepared as(initial &cell &command &source &prepared &e &memory &pair &fork_memory &parameters &suffix &final &request &INITIAL &INPUT &CANONICAL &RUN_VALUE &STARTED &COMMON &QUEUES &EMPTY &MATCH &COPY &BORROWED &ARGUMENTS &PARENT &PARENT_EFFECT &CHILD &CHILD_EFFECT &GRANT &DESCRIPTOR &WRITE &SHAPE &PREPARATION).
  exists initial,cell,command,source,prepared,e,memory,pair,fork_memory,parameters,suffix,final,request.
  repeat match goal with H:?P|-?P /\_=>split;[exact H|]end.
  exact SHAPE.
Qed.

Theorem namespace_actual_local_grant_owned:
  exists initial cell command source prepared e memory pair fork_memory parameters suffix final request,
    Genv.init_mem EntrySource.prog=Some initial /\
    handoff_borrowed_input cell prepared(handoff_fixture_input command source) /\
    e=namespace_initial_env prepared /\
    Mem.load Mint64 memory(handoff_symbol _run_id)0=Some(Vlong Int64.one) /\
    caller_source_machine(live(State f_namespace_init(namespace_tail 9)Kstop e
      namespace_useful_parent_temps memory)) /\
    namespace_steps namespace_ge cell
      (live(State f_namespace_init(namespace_tail 9)Kstop e namespace_useful_parent_temps memory))
      (repeat namespace_source_event 4++namespace_child_common_log pair(Int.repr 9)(Int.repr 10))
      (live(Callstate namespace_fork_definition[]
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory)) /\
    namespace_queue_steps namespace_queue_model fork_fixture_initial(fun _=>channel_empty)
      (repeat namespace_source_event 4++namespace_child_common_log pair(Int.repr 9)(Int.repr 10))
      fork_fixture_world(fork_fixture_reset(fun _=>channel_empty)) /\
    fork_fixture_reset(fun _=>channel_empty)60%nat=channel_empty /\
    fork_matches fork_fixture_world fork_fixture_snapshot /\
    NativeForkCopy cell fork_memory fork_memory fork_memory /\
    handoff_borrowed_input cell fork_memory(handoff_fixture_input command source) /\
    namespace_useful_child_input cell(handoff_fixture_input command source)fork_memory parameters /\
    namespace_step namespace_ge cell
      (live(Callstate namespace_fork_definition[]
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory))
      (namespace_forked(Int.repr 2))
      (live(Returnstate(Vint(Int.repr 2))
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory)) /\
    namespace_fork_effect fork_fixture_world fork_fixture_snapshot(Int.repr 2)fork_fixture_world /\
    namespace_step namespace_ge cell
      (live(Callstate namespace_fork_definition[]
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory))
      (namespace_forked Int.zero)
      (live(Returnstate(Vint Int.zero)
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory)) /\
    namespace_fork_effect fork_fixture_world fork_fixture_snapshot Int.zero
      (namespace_fork_child fork_fixture_world fork_fixture_snapshot) /\
    namespace_steps namespace_ge cell
      (live(Returnstate(Vint(Int.repr 2))
        (child_fork_cont pair parameters(namespace_creation_cont e namespace_useful_parent_temps Kstop))fork_memory))suffix
      (live(Returnstate(Vint Int.zero)
        (namespace_release_cont e namespace_useful_release_temps(Int.repr 2)(Int.repr 9)Kstop)final)) /\
    descriptor request=Int.repr 9 /\
    In(namespace_process(process_entry(entry_library(original_event(io_step request(transfer[Byte.repr 165]None))))))suffix.
Proof.
  destruct namespace_actual_local_grant_owned_shaped as(initial &cell &command &source &prepared &e &memory &pair &fork_memory
    &parameters &suffix &final &request &INITIAL &INPUT &CANONICAL &RUN_VALUE &STARTED &COMMON &QUEUES &EMPTY
    &MATCH &COPY &BORROWED &ARGUMENTS &PARENT &PARENT_EFFECT &CHILD &CHILD_EFFECT &GRANT &DESCRIPTOR &WRITE &SHAPE).
  exists initial,cell,command,source,prepared,e,memory,pair,fork_memory,parameters,suffix,final,request.
  repeat match goal with H:?P|-?P /\_=>split;[exact H|]end.
  exact WRITE.
Qed.
