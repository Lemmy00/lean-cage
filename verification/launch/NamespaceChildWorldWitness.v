(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.acceptance: The useful owned fork's zero branch reaches its actual fresh worker. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Clight.
Require Import IO Machine ErrorNumber Library LibraryMachine ProcessEffects StoreSteps WriteAll.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffArguments NativeHandoffStructure
  NativeHandoffAllocation NativeHandoffInput NativeHandoffInputWitness NativeHandoffInitial NativeHandoffMemory
  NativeHandoffGuest NativeHandoffExec NativeHandoffUseful NativeHandoffNonvacuity NativeHandoffTraceEvents
  NativeHandoffTrace NativeHandoffWire NativeHandoffTables NativeHandoffPrefix NativeHandoffLoop.
From EntryProcess Require Import ProcessMachine ProcessCaller.
From EntryNamespace Require Import NamespaceMachine NamespaceStructure NamespacePaths NamespaceCaller NamespaceRelease
  NamespaceBorrow NamespacePrepared NamespaceParentInput NamespaceParentWitness NamespaceForkWitness NamespaceObjects
  NamespaceKernel NamespaceWorldTrace NamespaceQueue NamespaceChannel NamespaceFork NamespaceGuestFlags NamespaceGuestImage
  NamespaceLaunchWitness NamespaceForkWorldWitness NamespaceLaunchWorldWitness.
From LeanCageMainNumber Require Import NumberMath.
Import ListNotations.
Open Scope Z_scope.

Lemma namespace_child_handoff_environment:namespace_ge=handoff_ge.
Proof. reflexivity. Qed.
Local Opaque namespace_ge handoff_ge handoff_symbol.

Theorem namespace_useful_zero_child_source cell borrowed memory pair parameters k:
  handoff_borrowed_input cell memory borrowed ->
  namespace_useful_child_input cell borrowed memory parameters ->
  exists after,
    handoff_borrowed_input cell after borrowed /\
    namespace_steps namespace_ge cell
      (live(Returnstate(Vint Int.zero)(child_fork_cont pair parameters k)memory))
      (repeat namespace_source_event 4++repeat namespace_source_event 3++repeat namespace_source_event 3)
      (live(Callstate(Internal f_guest)[Vint(Int.repr 4);Vint(Int.repr 5);Vint(Int.repr 6);Vint(Int.repr 60)]
        (child_guest_cont pair(child_fork_return_env parameters Int.zero)k)after)).
Proof.
  intros INPUT[pid[ARGUMENTS PRIVATE]].
  destruct ARGUMENTS as[IN OUT ERR FAILURE PID ACCESS TLS].
  destruct(Mem.valid_access_store _ _ _ _(Vint Int.zero)ACCESS)as[after STORE].
  exists after;split.
  - eapply namespace_store_preserves_borrows;[exact INPUT|exact PRIVATE|exact TLS|exact STORE].
  - eapply namespace_steps_append;[eapply namespace_store_path_actual;apply child_fork_return_source|].
    eapply namespace_steps_append.
    + eapply namespace_store_path_actual;apply child_publish_pid_source with(returned:=Int.zero)(object:=pid)(offset:=Ptrofs.zero).
      * unfold child_fork_return_env;WriteAll.lookup.
      * unfold child_fork_return_env;WriteAll.lookup.
      * exact STORE.
    + eapply namespace_store_path_actual;apply child_select_guest_source with
        (input:=Int.repr 4)(output:=Int.repr 5)(errors:=Int.repr 6)(failure:=Int.repr 60).
      all:unfold child_fork_return_env;WriteAll.lookup.
Qed.

Lemma namespace_useful_guest_event_kernel world event:
  Forall namespace_good_flag(handoff_event_flags event) ->
  namespace_kernel_event world(namespace_guest_event event)
    (namespace_apply_flags world(handoff_event_flags event)).
Proof.
  destruct event;cbn[handoff_event_flags];intro GOOD;
    try solve[inversion GOOD;contradiction];try solve[apply namespace_kernel_passive;reflexivity].
  - destruct event;cbn[handoff_event_flags]in GOOD|-*;
      try solve[inversion GOOD;contradiction];try solve[apply namespace_kernel_passive;reflexivity].
    destruct ev;cbn[handoff_event_flags]in GOOD|-*;
      try solve[inversion GOOD;contradiction];try solve[apply namespace_kernel_passive;reflexivity].
    destruct t;cbn[handoff_event_flags]in GOOD|-*;
      try solve[inversion GOOD;contradiction].
    apply namespace_kernel_source.
  - inversion GOOD as[|tag rest HEAD TAIL];subst.
    cbn[namespace_good_flag]in HEAD;destruct HEAD as[RETURNED FLAGS];subst returned.
    destruct FLAGS as[FLAGS|FLAGS];subst flags;cbn[namespace_apply_flags namespace_apply_flag].
    + rewrite Int.eq_true;apply namespace_kernel_flags_zero.
    + rewrite Int.eq_false by(vm_compute;discriminate);apply namespace_kernel_flags_one.
Qed.

Lemma namespace_useful_apply_flags_app world first second:
  namespace_apply_flags world(first++second)=namespace_apply_flags(namespace_apply_flags world first)second.
Proof. revert world;induction first;intro world;cbn;[reflexivity|apply IHfirst]. Qed.

Theorem namespace_useful_guest_prefix_kernel world events:
  Forall namespace_good_flag(handoff_flags_projection events) ->
  namespace_kernel_steps world(map namespace_guest_event events)
    (namespace_apply_flags world(handoff_flags_projection events)).
Proof.
  revert world;induction events as[|event rest IH];intros world GOOD;[constructor|].
  unfold handoff_flags_projection in GOOD|-*;cbn[flat_map]in GOOD|-*.
  apply Forall_app in GOOD as[HEAD TAIL].
  cbn[map];rewrite namespace_useful_apply_flags_app.
  econstructor;[apply namespace_useful_guest_event_kernel;exact HEAD|apply IH;exact TAIL].
Qed.

Lemma namespace_useful_waits_image_kernel world waits path arguments environment:
  namespace_kernel_steps world(map namespace_guest_event
    (repeat entry_primitive_wait waits++[entry_image path arguments environment]))
    (namespace_exec world default_signal_action).
Proof.
  induction waits;cbn[repeat app map].
  - econstructor;[apply namespace_kernel_exec;intro;reflexivity|constructor].
  - econstructor;[apply namespace_kernel_passive;reflexivity|exact IHwaits].
Qed.

Theorem namespace_useful_image_kernel cell input memory input_fd output_fd errors_fd failure k
    events target path arguments environment world:
  handoff_borrowed_input cell memory input ->
  entry_handoff_steps handoff_ge cell
    (live(Callstate(Internal f_guest)[Vint input_fd;Vint output_fd;Vint errors_fd;Vint failure]k memory))events target ->
  In(entry_image path arguments environment)events ->
  exists after,
    namespace_kernel_steps world(map namespace_guest_event events)after /\
    namespace_table after=exec_table(handoff_stdio_table(namespace_table world)input_fd output_fd errors_fd failure) /\
    namespace_sigchld after=default_signal_action /\namespace_signal_mask after=namespace_signal_mask world /\
    namespace_ambient after=namespace_ambient world.
Proof.
  intros INPUT RUN IMAGE.
  destruct(handoff_guest_image_flags _ _ _ _ _ _ _ _ _ _ _ _ _ INPUT RUN IMAGE)
    as[prefix[b[after[caller[suffix[waits[EVENTS[FLAGS[PREFIX[PATH[ARGS[ENV TARGET]]]]]]]]]]]].
  assert(GOOD:Forall namespace_good_flag(handoff_flags_projection prefix)).
  { rewrite FLAGS;unfold handoff_expected_flags;repeat(apply Forall_cons;
      [cbn[namespace_good_flag];auto|]);constructor. }
  pose proof(namespace_useful_guest_prefix_kernel world prefix GOOD)as KERNEL.
  destruct(expected_guest_flags_determine_table _ _ _ _ _ _ _ KERNEL FLAGS)
    as[TABLE[ACTION[MASK AMBIENT]]].
  exists(namespace_exec(namespace_apply_flags world(handoff_flags_projection prefix))default_signal_action);split.
  - rewrite EVENTS,map_app;eapply namespace_kernel_steps_append;[exact KERNEL|].
    apply namespace_useful_waits_image_kernel.
  - change(exec_table(namespace_table(namespace_apply_flags world(handoff_flags_projection prefix)))=
      exec_table(handoff_stdio_table(namespace_table world)input_fd output_fd errors_fd failure) /\
      default_signal_action=default_signal_action /\
      namespace_signal_mask(namespace_apply_flags world(handoff_flags_projection prefix))=namespace_signal_mask world /\
      namespace_ambient(namespace_apply_flags world(handoff_flags_projection prefix))=namespace_ambient world).
    rewrite TABLE,MASK,AMBIENT;repeat split;reflexivity.
Qed.

Theorem namespace_useful_zero_child_image cell command source memory pair parameters k:
  handoff_borrowed_input cell memory(handoff_fixture_input command source) ->
  namespace_useful_child_input cell(handoff_fixture_input command source)memory parameters ->
  exists branch_memory b after caller prefix,
    let call:=child_guest_cont pair(child_fork_return_env parameters Int.zero)k in
    let endpoint:=Callstate entry_exec_definition
      [Vptr(handoff_symbol ___stringlit_111)Ptrofs.zero;
       Vptr(handoff_arguments b)Ptrofs.zero;Vptr(handoff_environment b)Ptrofs.zero]
      (handoff_exec_cont(handoff_locals_env b)caller(Kseq(guest_tail 24(fn_body f_guest))call))after in
    handoff_borrowed_input cell branch_memory(handoff_fixture_input command source) /\
    handoff_image_snapshot cell(handoff_fixture_input command source)(Int.repr 4)(Int.repr 5)(Int.repr 6)(Int.repr 60)endpoint /\
    handoff_chosen_image_data cell(handoff_fixture_input command source)b handoff_admitted_example_words after
      handoff_example_uid handoff_admitted_example_encode /\
    namespace_steps namespace_ge cell
      (live(Returnstate(Vint Int.zero)(child_fork_cont pair parameters k)memory))
      ((repeat namespace_source_event 4++repeat namespace_source_event 3++repeat namespace_source_event 3)++
       map namespace_guest_event(prefix++[entry_image(Vptr(handoff_symbol ___stringlit_111)Ptrofs.zero)
         (Vptr(handoff_arguments b)Ptrofs.zero)(Vptr(handoff_environment b)Ptrofs.zero)]))(dead after) /\
    entry_handoff_steps handoff_ge cell
      (live(Callstate(Internal f_guest)[Vint(Int.repr 4);Vint(Int.repr 5);Vint(Int.repr 6);Vint(Int.repr 60)]call branch_memory))
      (prefix++[entry_image(Vptr(handoff_symbol ___stringlit_111)Ptrofs.zero)
        (Vptr(handoff_arguments b)Ptrofs.zero)(Vptr(handoff_environment b)Ptrofs.zero)])(dead after).
Proof.
  intros INPUT ARGUMENTS.
  destruct(namespace_useful_zero_child_source cell(handoff_fixture_input command source)memory pair parameters k INPUT ARGUMENTS)
    as[branch_memory[BORROWED BRANCH]].
  destruct handoff_example_uid_correct as[LENGTH[NONZERO PARSED]].
  assert(UIDBOUND:100000<=Int.unsigned(handoff_borrowed_uid(handoff_fixture_input command source))<=100999)
    by(change(100000<=100000<=100999);lia).
  destruct(handoff_useful_image_data cell(handoff_fixture_input command source)branch_memory
    (Int.repr 4)(Int.repr 5)(Int.repr 6)(Int.repr 60)
    (child_guest_cont pair(child_fork_return_env parameters Int.zero)k)handoff_example_uid handoff_admitted_example_encode
    BORROWED eq_refl UIDBOUND handoff_admitted_example_checked LENGTH NONZERO PARSED handoff_admitted_example_encoding)
    as[b[after[caller[prefix[SNAPSHOT[DATA[PREFIX RUN]]]]]]].
  exists branch_memory,b,after,caller,prefix;cbn zeta;split;[exact BORROWED|]. split;[exact SNAPSHOT|]. split;[exact DATA|]. split.
  - eapply namespace_steps_append;[exact BRANCH|].
    rewrite namespace_child_handoff_environment;apply namespace_entry_runs_are_preserved;exact RUN.
  - exact RUN.
Qed.

Lemma namespace_useful_sources_kernel world count:
  namespace_kernel_steps world(repeat namespace_source_event count)world.
Proof. induction count;cbn[repeat];[constructor|econstructor;[apply namespace_kernel_source|exact IHcount]]. Qed.

Definition namespace_useful_worker_bytes b memory:=exists uidbytes inputbytes outputbytes errorsbytes failurebytes,
  handoff_argv_bytes memory(handoff_arguments b)
    (map Byte.repr[47;108;101;97;110;99;97;103;101;45;101;110;116;114;121]::
      map Byte.repr[114;117;110]::uidbytes::handoff_fixture_root_bytes::inputbytes::outputbytes::errorsbytes::failurebytes::
      handoff_normal_bytes::[handoff_fixture_command_bytes]) /\
  handoff_argv_bytes memory(handoff_environment b)[map Byte.repr[76;67;95;65;76;76;61;67]] /\
  decimal_number uidbytes=Some 100000 /\decimal_number inputbytes=Some 4 /\
  decimal_number outputbytes=Some 5 /\decimal_number errorsbytes=Some 6 /\decimal_number failurebytes=Some 60.

Theorem namespace_useful_snapshot_worker_bytes cell command source b memory caller k:
  handoff_image_snapshot cell(handoff_fixture_input command source)(Int.repr 4)(Int.repr 5)(Int.repr 6)(Int.repr 60)
    (Callstate entry_exec_definition
      [Vptr(handoff_symbol ___stringlit_111)Ptrofs.zero;
       Vptr(handoff_arguments b)Ptrofs.zero;Vptr(handoff_environment b)Ptrofs.zero]
      (handoff_exec_cont(handoff_locals_env b)caller(Kseq(guest_tail 24(fn_body f_guest))k))memory) ->
  namespace_useful_worker_bytes b memory.
Proof.
  intro SNAPSHOT.
  destruct(handoff_snapshot_wire _ _ _ _ _ _ _ SNAPSHOT)
    as[actual[after[temps[suffix[uidbytes[inputbytes[outputbytes[errorsbytes[failurebytes
      [STATE[FAILURE[WIRE[ENVIRONMENT[UID[IN[OUT[ERR FAIL]]]]]]]]]]]]]]]]].
  pose proof(f_equal(fun state=>match state with Callstate _ _ _ m|State _ _ _ _ _ m|Returnstate _ _ m=>m end)STATE)as MEMORY.
  change(memory=after)in MEMORY;subst after.
  pose proof(f_equal(fun state=>match state with Callstate _(_::Vptr object _::_)_ _=>object|_=>handoff_arguments b end)STATE)as ARGV.
  change(handoff_arguments b=handoff_arguments actual)in ARGV.
  pose proof(f_equal(fun state=>match state with Callstate _(_::_::Vptr object _::_)_ _=>object|_=>handoff_environment b end)STATE)as ENVP.
  change(handoff_environment b=handoff_environment actual)in ENVP.
  rewrite <-ARGV in WIRE;rewrite <-ENVP in ENVIRONMENT.
  exists uidbytes,inputbytes,outputbytes,errorsbytes,failurebytes.
  split;[exact WIRE|]. split;[exact ENVIRONMENT|]. repeat split;assumption.
Qed.

Definition namespace_canonical_worker_bytes b memory:=
  handoff_argv_bytes memory(handoff_arguments b)
    [map Byte.repr[47;108;101;97;110;99;97;103;101;45;101;110;116;114;121];
     map Byte.repr[114;117;110];handoff_example_uid;handoff_fixture_root_bytes;
     [Byte.repr 52];[Byte.repr 53];[Byte.repr 54];map Byte.repr[54;48];
     handoff_normal_bytes;handoff_fixture_command_bytes] /\
  handoff_argv_bytes memory(handoff_environment b)[map Byte.repr[76;67;95;65;76;76;61;67]].

Theorem namespace_chosen_worker_bytes cell command source b memory:
  handoff_chosen_image_data cell(handoff_fixture_input command source)b handoff_admitted_example_words memory
    handoff_example_uid handoff_admitted_example_encode ->namespace_canonical_worker_bytes b memory.
Proof.
  intros[LIVE UID UIDLENGTH HISTORY ARGSTABLE ENVTABLE].
  change(handoff_fd_history b handoff_admitted_example_words memory 0
    [[Byte.repr 52];[Byte.repr 53];[Byte.repr 54];map Byte.repr[54;48]])in HISTORY.
  cbn[handoff_fd_history]in HISTORY.
  destruct HISTORY as[IT[IL[IP[OT[OL[OP[ET[EL[EP[FT[FL[FP DONE]]]]]]]]]]]].
  pose proof(handoff_live_borrowed _ _ _ _ _ LIVE)as BORROWED.
  split.
  - exists(handoff_prefix_values b(handoff_borrowed_preflight(handoff_fixture_input command source))
      (address_block(handoff_borrowed_mode(handoff_fixture_input command source)))
      (Ptrofs.repr(address_offset(handoff_borrowed_mode(handoff_fixture_input command source))))++
      map handoff_argument_value(handoff_borrowed_arguments(handoff_fixture_input command source))).
    split;[exact ARGSTABLE|].
    apply Forall2_app with(l1':=[map Byte.repr[47;108;101;97;110;99;97;103;101;45;101;110;116;114;121];
      map Byte.repr[114;117;110];handoff_example_uid;handoff_fixture_root_bytes;
      [Byte.repr 52];[Byte.repr 53];[Byte.repr 54];map Byte.repr[54;48];handoff_normal_bytes])
      (l2':=[handoff_fixture_command_bytes]);[|eapply handoff_borrowed_strings;exact BORROWED].
    unfold handoff_prefix_values.
    apply Forall2_cons;[eapply handoff_owned_literal;[exact BORROWED|unfold handoff_literal_bytes;cbn;auto 8]|].
    apply Forall2_cons.
    { change(handoff_value_string memory
        (Vptr(handoff_symbol ___stringlit_112)Ptrofs.zero)(map Byte.repr[114;117;110])).
      eapply handoff_owned_literal;[exact BORROWED|unfold handoff_literal_bytes;cbn;auto 8]. }
    apply Forall2_cons;[eapply handoff_number_value_string;[exact UID|lia]|].
    apply Forall2_cons.
    { exists(handoff_global_address _root_path);split;[reflexivity|].
      exact(handoff_borrowed_root_text _ _ _ BORROWED). }
    apply Forall2_cons;[eapply handoff_number_value_string;[exact IT|lia]|].
    apply Forall2_cons;[eapply handoff_number_value_string;[exact OT|lia]|].
    apply Forall2_cons;[eapply handoff_number_value_string;[exact ET|lia]|].
    apply Forall2_cons;[eapply handoff_number_value_string;[exact FT|lia]|].
    apply Forall2_cons.
    { exists(handoff_borrowed_mode(handoff_fixture_input command source));split;[reflexivity|].
      exact(handoff_borrowed_mode_text _ _ _ BORROWED). }
    apply Forall2_nil.
  - exists[Vptr(handoff_symbol ___stringlit_114)Ptrofs.zero];split;[exact ENVTABLE|].
    constructor;[|constructor]. eapply handoff_owned_literal;
      [exact BORROWED|unfold handoff_literal_bytes;cbn;auto 8].
Qed.

Definition namespace_useful_child_image_fields cell command source memory pair parameters k
    branch_memory b after caller prefix world:=
    let call:=child_guest_cont pair(child_fork_return_env parameters Int.zero)k in
    let image:=entry_image(Vptr(handoff_symbol ___stringlit_111)Ptrofs.zero)
      (Vptr(handoff_arguments b)Ptrofs.zero)(Vptr(handoff_environment b)Ptrofs.zero) in
    let events:=(repeat namespace_source_event 4++repeat namespace_source_event 3++repeat namespace_source_event 3)++
      map namespace_guest_event(prefix++[image]) in
    handoff_borrowed_input cell branch_memory(handoff_fixture_input command source) /\
    handoff_image_snapshot cell(handoff_fixture_input command source)(Int.repr 4)(Int.repr 5)(Int.repr 6)(Int.repr 60)
      (Callstate entry_exec_definition
        [Vptr(handoff_symbol ___stringlit_111)Ptrofs.zero;
         Vptr(handoff_arguments b)Ptrofs.zero;Vptr(handoff_environment b)Ptrofs.zero]
        (handoff_exec_cont(handoff_locals_env b)caller(Kseq(guest_tail 24(fn_body f_guest))call))after) /\
    namespace_useful_worker_bytes b after /\
    namespace_canonical_worker_bytes b after /\
    namespace_steps namespace_ge cell
      (live(Returnstate(Vint Int.zero)(child_fork_cont pair parameters k)memory))events(dead after) /\
    entry_handoff_steps handoff_ge cell
      (live(Callstate(Internal f_guest)[Vint(Int.repr 4);Vint(Int.repr 5);Vint(Int.repr 6);Vint(Int.repr 60)]call branch_memory))
      (prefix++[image])(dead after) /\
    namespace_kernel_steps(namespace_fork_child fork_fixture_world fork_fixture_snapshot)events world /\
    namespace_table world=fork_fixture_worker_table /\
    (forall descriptor,namespace_table world descriptor=fork_fixture_worker_slot descriptor) /\
    namespace_sigchld world=default_signal_action /\
    namespace_signal_mask world=namespace_blockable_mask Int64.mone.


Definition namespace_useful_child_replacement cell command source memory pair parameters k:=
  exists branch_memory b after caller prefix world,
    namespace_useful_child_image_fields cell command source memory pair parameters k
      branch_memory b after caller prefix world.

Theorem namespace_useful_zero_child_replacement cell command source memory pair parameters k:
  handoff_borrowed_input cell memory(handoff_fixture_input command source) ->
  namespace_useful_child_input cell(handoff_fixture_input command source)memory parameters ->
  namespace_useful_child_replacement cell command source memory pair parameters k.
Proof.
  intros INPUT ARGUMENTS.
  destruct(namespace_useful_zero_child_image cell command source memory pair parameters k INPUT ARGUMENTS)
    as[branch_memory[b[after[caller[prefix[BORROWED[SNAPSHOT[DATA[SOURCE GUEST]]]]]]]]].
  assert(IMAGE:In(entry_image(Vptr(handoff_symbol ___stringlit_111)Ptrofs.zero)
    (Vptr(handoff_arguments b)Ptrofs.zero)(Vptr(handoff_environment b)Ptrofs.zero))
    (prefix++[entry_image(Vptr(handoff_symbol ___stringlit_111)Ptrofs.zero)
      (Vptr(handoff_arguments b)Ptrofs.zero)(Vptr(handoff_environment b)Ptrofs.zero)])).
  { apply in_or_app;right;cbn;auto. }
  destruct(namespace_useful_image_kernel _ _ _ _ _ _ _ _ _ _ _ _ _
    (namespace_fork_child fork_fixture_world fork_fixture_snapshot)BORROWED GUEST IMAGE)
    as[world[KERNEL[TABLE[ACTION[MASK AMBIENT]]]]].
  assert(EXACT:namespace_table world=fork_fixture_worker_table)by exact TABLE.
  exists branch_memory,b,after,caller,prefix,world;cbn zeta.
  split;[exact BORROWED|]. split;[exact SNAPSHOT|].
  split;[eapply namespace_useful_snapshot_worker_bytes;exact SNAPSHOT|].
  split;[eapply namespace_chosen_worker_bytes;exact DATA|].
  split;[exact SOURCE|]. split;[exact GUEST|]. split.
  - eapply namespace_kernel_steps_append;[|exact KERNEL].
    eapply namespace_kernel_steps_append;[apply namespace_useful_sources_kernel|].
    eapply namespace_kernel_steps_append;apply namespace_useful_sources_kernel.
  - split;[exact EXACT|]. split.
    + intro descriptor;rewrite EXACT;apply namespace_useful_worker_table_exact.
    + split;[exact ACTION|]. rewrite MASK;reflexivity.
Qed.

Theorem namespace_actual_parent_and_child_entry_shaped_prepared:
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
    namespace_useful_child_replacement cell command source fork_memory pair parameters
      (namespace_creation_cont e namespace_useful_parent_temps Kstop) /\
    inhabited(NamespaceUsefulParentShape cell e pair parameters fork_memory suffix final request) /\
    namespace_useful_preparation cell command source prepared e memory Int64.one.
Proof.
  destruct namespace_actual_local_grant_owned_shaped_prepared as(initial &cell &command &source &prepared &e &memory &pair &fork_memory
    &parameters &suffix &final &request &INITIAL &INPUT &CANONICAL &RUN_VALUE &STARTED &COMMON &QUEUES &EMPTY
    &MATCH &COPY &BORROWED &ARGUMENTS &PARENT &PARENT_EFFECT &CHILD &CHILD_EFFECT &GRANT &DESCRIPTOR &WRITE &SHAPE &PREPARATION).
  pose proof(namespace_useful_zero_child_replacement cell command source fork_memory pair parameters
    (namespace_creation_cont e namespace_useful_parent_temps Kstop)BORROWED ARGUMENTS)as CHILD_IMAGE.
  exists initial,cell,command,source,prepared,e,memory,pair,fork_memory,parameters,suffix,final,request.
  repeat match goal with H:?P|-?P /\_=>split;[exact H|]end.
  exact PREPARATION.
Qed.

Theorem namespace_actual_parent_and_child_entry_shaped:
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
    namespace_useful_child_replacement cell command source fork_memory pair parameters
      (namespace_creation_cont e namespace_useful_parent_temps Kstop) /\
    inhabited(NamespaceUsefulParentShape cell e pair parameters fork_memory suffix final request).
Proof.
  destruct namespace_actual_parent_and_child_entry_shaped_prepared as(initial &cell &command &source &prepared &e &memory &pair &fork_memory &parameters &suffix &final &request &INITIAL &INPUT &CANONICAL &RUN_VALUE &STARTED &COMMON &QUEUES &EMPTY &MATCH &COPY &BORROWED &ARGUMENTS &PARENT &PARENT_EFFECT &CHILD &CHILD_EFFECT &GRANT &DESCRIPTOR &WRITE &CHILD_IMAGE &SHAPE &PREPARATION).
  exists initial,cell,command,source,prepared,e,memory,pair,fork_memory,parameters,suffix,final,request.
  repeat match goal with H:?P|-?P /\_=>split;[exact H|]end.
  exact SHAPE.
Qed.

Theorem namespace_actual_parent_and_child_entry:
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
    namespace_useful_child_replacement cell command source fork_memory pair parameters
      (namespace_creation_cont e namespace_useful_parent_temps Kstop).
Proof.
  destruct namespace_actual_parent_and_child_entry_shaped as(initial &cell &command &source &prepared &e &memory &pair &fork_memory
    &parameters &suffix &final &request &INITIAL &INPUT &CANONICAL &RUN_VALUE &STARTED &COMMON &QUEUES &EMPTY
    &MATCH &COPY &BORROWED &ARGUMENTS &PARENT &PARENT_EFFECT &CHILD &CHILD_EFFECT &GRANT &DESCRIPTOR &WRITE &CHILD_IMAGE &SHAPE).
  exists initial,cell,command,source,prepared,e,memory,pair,fork_memory,parameters,suffix,final,request.
  repeat match goal with H:?P|-?P /\_=>split;[exact H|]end.
  exact CHILD_IMAGE.
Qed.
