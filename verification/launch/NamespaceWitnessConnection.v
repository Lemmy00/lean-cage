(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.acceptance: Actual useful image data equal the ordinary worker consumer's data. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Maps Integers AST Values Memory Globalenvs Ctypes Clight.
From LeanImport Require Import Lean.
Require Import Machine.
From EntryNative Require Import EntrySource NativeHandoffArguments NativeHandoffAllocation NativeHandoffInput NativeHandoffInputWitness
  NativeHandoffWire NativeHandoffUseful NativeHandoffInitial.
From EntryNamespace Require Import NamespaceObjects NamespaceKernel NamespaceForkWorldWitness NamespaceWitnessImport.
From EntryNamespace Require Import NamespaceMachine NamespaceStructure NamespacePaths NamespaceCaller NamespaceRelease
  NamespacePrepared NamespaceFork NamespaceQueue NamespaceChannel NamespaceParentInput NamespaceForkWitness
  NamespaceLaunchWitness NamespaceLaunchWorldWitness NamespaceChildWorldWitness
  NamespaceParentWitness NamespaceParentFrame NamespaceParentData NamespaceTLS.
From EntryNative Require Import NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessCaller.
Require Import IO LibraryMachine.
Import ListNotations.
Local Close Scope lean_scope.
Local Open Scope Z_scope.

Definition witness_table_objects(table:DescriptorTable)(fd:Lean.Nat):NamespaceWitnessImport.Option_inst1 Lean.Nat:=
  if Z.leb(Z.of_nat(nat_of_Nat fd))Int.max_signed then
    match table(Int.repr(Z.of_nat(nat_of_Nat fd)))with
    |Some binding=>NamespaceWitnessImport.Option_some_inst1 Lean.Nat(Nat_of_nat
      (match descriptor_object binding with
       |ordinary_object object_id=>object_id*3
       |release_endpoint channel parent_endpoint=>channel*3+1
       |release_endpoint channel child_endpoint=>channel*3+2 end))
    |None=>NamespaceWitnessImport.Option_none_inst1 Lean.Nat end
  else NamespaceWitnessImport.Option_none_inst1 Lean.Nat.
Definition witness_table_cloexec(table:DescriptorTable)(fd:Lean.Nat):NamespaceWitnessImport.Bool:=
  if Z.leb(Z.of_nat(nat_of_Nat fd))Int.max_signed then
    match table(Int.repr(Z.of_nat(nat_of_Nat fd)))with
    |Some binding=>if descriptor_cloexec binding then NamespaceWitnessImport.Bool_true else NamespaceWitnessImport.Bool_false
    |None=>NamespaceWitnessImport.Bool_false end
  else NamespaceWitnessImport.Bool_false.

Theorem witness_consumer_objects_absent fd:
  nat_of_Nat fd<>0%nat ->nat_of_Nat fd<>2%nat ->nat_of_Nat fd<>4%nat ->
  nat_of_Nat fd<>5%nat ->nat_of_Nat fd<>6%nat ->nat_of_Nat fd<>60%nat ->
  LeanCage_Entry_CallerWitness_objects fd=NamespaceWitnessImport.Option_none_inst1 Lean.Nat.
Proof.
  intros ZERO TWO FOUR FIVE SIX SIXTY.
  do 61(destruct fd as[|fd];[vm_compute in *;first[reflexivity|exfalso;tauto]|]).
  vm_compute;reflexivity.
Qed.

(* §AR-entry.acceptance: Retained preparation facts belong to the same actual source witness. *)
Theorem namespace_useful_preparation_raw cell command source prepared e memory run:
  handoff_borrowed_input cell prepared(handoff_fixture_input command source) ->
  namespace_useful_preparation cell command source prepared e memory run ->
  Mem.valid_block prepared(tls_block cell) /\
  Forall(Mem.valid_block prepared)(handoff_borrowed_blocks(handoff_fixture_input command source)) /\
  Mem.valid_block prepared(namespace_symbol _admission_cgroup) /\
  Mem.valid_block prepared(namespace_symbol _preflight) /\
  namespace_symbol _admission_cgroup<>tls_block cell /\
  Mem.load Mint32 memory(namespace_symbol _admission_cgroup)0=Some(Vint(Int.repr 7)) /\
  handoff_borrowed_input cell memory(handoff_fixture_input command source) /\
  (forall object position kind permission,Mem.perm(namespace_initial_memory prepared)object position kind permission ->
    Mem.perm memory object position kind permission).
Proof.
  intros INPUT[PERMISSIONS[BORROWED[childobject[pipe[status[temporary[admission CALLBACKS]]]]]]].
  split;[apply namespace_errno_ready_valid;exact(handoff_borrowed_errno _ _ _ INPUT)|].
  split;[exact(handoff_borrowed_objects_valid _ _ _ INPUT)|].
  assert(CG_VALID:Mem.valid_block prepared(namespace_symbol _admission_cgroup)).
  { rewrite namespace_handoff_symbol;eapply namespace_prepared_globals_exist;[exact INPUT|].
    apply in_or_app;right;cbn;auto. }
  assert(PF_VALID:Mem.valid_block prepared(namespace_symbol _preflight)).
  { rewrite namespace_handoff_symbol;eapply namespace_prepared_globals_exist;[exact INPUT|].
    apply in_or_app;right;cbn;auto. }
  pose proof(namespace_useful_separate _ _ _ _ _ _ _ _ _ _ _ _ _ CALLBACKS)as[S0[S1[S2[S3 CG_TLS]]]].
  pose proof(namespace_useful_captures _ _ _ _ _ _ _ _ _ _ _ _ _ CALLBACKS)as[C0[C1[CG_LOAD C3]]].
  split;[exact CG_VALID|]. split;[exact PF_VALID|]. split;[exact CG_TLS|].
  split;[exact CG_LOAD|]. split;[exact BORROWED|exact PERMISSIONS].
Qed.

Theorem namespace_useful_prepared_scalars:
  namespace_useful_parent_temps!_error=Some(Vint Int.zero) /\
  namespace_useful_parent_temps!_input=Some(Vint(Int.repr 4)) /\
  namespace_useful_parent_temps!_output=Some(Vint(Int.repr 5)) /\
  namespace_useful_parent_temps!_errors=Some(Vint(Int.repr 6)) /\
  namespace_useful_parent_temps!_parentfd=Some(Vint(Int.repr 3)) /\
  namespace_useful_parent_temps!_report=Some(Vint(Int.repr 8)) /\
  namespace_useful_parent_temps!_sequence=Some(Vlong Int64.zero).
Proof. vm_compute;repeat split;reflexivity. Qed.

Lemma witness_word_distinct fd(number:nat):
  Z.leb(Z.of_nat(nat_of_Nat fd))Int.max_signed=true ->
  0<=Z.of_nat number<=Int.max_signed ->nat_of_Nat fd<>number ->
  Int.repr(Z.of_nat(nat_of_Nat fd))<>Int.repr(Z.of_nat number).
Proof.
  intros BOUND RANGE DIFFERENT SAME;apply DIFFERENT,Nat2Z.inj.
  apply(f_equal Int.signed)in SAME;rewrite !Int.signed_repr in SAME;
    try(apply Z.leb_le in BOUND;pose proof(Nat2Z.is_nonneg(nat_of_Nat fd));
      change Int.min_signed with(-2147483648);lia);exact SAME.
Qed.

Theorem witness_source_objects_exact fd:
  witness_table_objects fork_fixture_worker_table fd=LeanCage_Entry_CallerWitness_objects fd.
Proof.
  assert(NAT:forall value,nat_of_Nat fd=value ->fd=Nat_of_nat value).
  { intros value SAME;rewrite <-(Nat2natid fd);rewrite SAME;reflexivity. }
  destruct(Nat.eq_dec(nat_of_Nat fd)0)as[ZERO|ZERO];[apply NAT in ZERO;subst fd;vm_compute;reflexivity|].
  destruct(Nat.eq_dec(nat_of_Nat fd)2)as[TWO|TWO];[apply NAT in TWO;subst fd;vm_compute;reflexivity|].
  destruct(Nat.eq_dec(nat_of_Nat fd)4)as[FOUR|FOUR];[apply NAT in FOUR;subst fd;vm_compute;reflexivity|].
  destruct(Nat.eq_dec(nat_of_Nat fd)5)as[FIVE|FIVE];[apply NAT in FIVE;subst fd;vm_compute;reflexivity|].
  destruct(Nat.eq_dec(nat_of_Nat fd)6)as[SIX|SIX];[apply NAT in SIX;subst fd;vm_compute;reflexivity|].
  destruct(Nat.eq_dec(nat_of_Nat fd)60)as[SIXTY|SIXTY];[apply NAT in SIXTY;subst fd;vm_compute;reflexivity|].
  rewrite(witness_consumer_objects_absent fd ZERO TWO FOUR FIVE SIX SIXTY).
  unfold witness_table_objects;destruct(Z.leb(Z.of_nat(nat_of_Nat fd))Int.max_signed)eqn:BOUND;[|reflexivity].
  rewrite namespace_useful_worker_table_exact;unfold fork_fixture_worker_slot.
  assert(DIFFERENT:forall(number:nat)(word:int),Int.signed word=Z.of_nat number ->nat_of_Nat fd<>number ->
    Int.eq(Int.repr(Z.of_nat(nat_of_Nat fd)))word=false).
  { intros number word VALUE NE;apply Int.eq_false;intro SAME;apply NE,Nat2Z.inj.
    apply(f_equal Int.signed)in SAME.
    rewrite Int.signed_repr in SAME.
    - rewrite VALUE in SAME;exact SAME.
    - apply Z.leb_le in BOUND;change Int.min_signed with(-2147483648);lia. }
  rewrite(DIFFERENT 0%nat Int.zero Logic.eq_refl ZERO),
    (DIFFERENT 2%nat(Int.repr 2)Logic.eq_refl TWO),(DIFFERENT 4%nat(Int.repr 4)Logic.eq_refl FOUR),
    (DIFFERENT 5%nat(Int.repr 5)Logic.eq_refl FIVE),(DIFFERENT 6%nat(Int.repr 6)Logic.eq_refl SIX),
    (DIFFERENT 60%nat(Int.repr 60)Logic.eq_refl SIXTY);reflexivity.
Qed.

Theorem witness_source_cloexec_exact fd:
  witness_table_cloexec fork_fixture_worker_table fd=LeanCage_Entry_CallerWitness_cloexec fd.
Proof.
  unfold witness_table_cloexec,LeanCage_Entry_CallerWitness_cloexec.
  destruct(Z.leb(Z.of_nat(nat_of_Nat fd))Int.max_signed);[|reflexivity].
  rewrite namespace_useful_worker_table_exact;unfold fork_fixture_worker_slot.
  repeat match goal with|-context[Int.eq ?left ?right]=>destruct(Int.eq left right)end;reflexivity.
Qed.

Fixpoint witness_bytes(bytes:list Byte.int):NamespaceWitnessImport.List_inst1 NamespaceWitnessImport.UInt8:=
  match bytes with
  |[]=>NamespaceWitnessImport.List_nil_inst1 NamespaceWitnessImport.UInt8
  |byte::rest=>NamespaceWitnessImport.List_cons_inst1 NamespaceWitnessImport.UInt8
    (NamespaceWitnessImport.OfNat_ofNat_inst1 NamespaceWitnessImport.UInt8(Nat_of_nat(Z.to_nat(Byte.unsigned byte)))
      (NamespaceWitnessImport.UInt8_instOfNat(Nat_of_nat(Z.to_nat(Byte.unsigned byte)))))(witness_bytes rest) end.
Fixpoint witness_arguments(strings:list(list Byte.int)):
    NamespaceWitnessImport.List_inst1(NamespaceWitnessImport.List_inst1 NamespaceWitnessImport.UInt8):=
  match strings with
  |[]=>NamespaceWitnessImport.List_nil_inst1 _
  |bytes::rest=>NamespaceWitnessImport.List_cons_inst1 _(witness_bytes bytes)(witness_arguments rest) end.

Theorem witness_source_arguments_exact:
  witness_arguments[map Byte.repr[114;117;110];handoff_example_uid;handoff_fixture_root_bytes;
    [Byte.repr 52];[Byte.repr 53];[Byte.repr 54];map Byte.repr[54;48];handoff_normal_bytes;handoff_fixture_command_bytes]=
    LeanCage_Entry_CallerWitness_argumentBytes.
Proof. reflexivity. Qed.

Definition namespace_worker_ordinary_input b memory world:=exists strings,
  handoff_argv_bytes memory(handoff_arguments b)
    (map Byte.repr[47;108;101;97;110;99;97;103;101;45;101;110;116;114;121]::strings) /\
  handoff_argv_bytes memory(handoff_environment b)[map Byte.repr[76;67;95;65;76;76;61;67]] /\
  witness_arguments strings=LeanCage_Entry_CallerWitness_argumentBytes /\
  (forall fd,witness_table_objects(namespace_table world)fd=LeanCage_Entry_CallerWitness_objects fd) /\
  (forall fd,witness_table_cloexec(namespace_table world)fd=LeanCage_Entry_CallerWitness_cloexec fd).

Theorem namespace_canonical_image_supplies_ordinary b memory world:
  namespace_canonical_worker_bytes b memory ->namespace_table world=fork_fixture_worker_table ->
  namespace_worker_ordinary_input b memory world.
Proof.
  intros[ARGV ENV]TABLE.
  exists[map Byte.repr[114;117;110];handoff_example_uid;handoff_fixture_root_bytes;
    [Byte.repr 52];[Byte.repr 53];[Byte.repr 54];map Byte.repr[54;48];handoff_normal_bytes;handoff_fixture_command_bytes].
  split;[exact ARGV|]. split;[exact ENV|]. split;[exact witness_source_arguments_exact|].
  rewrite TABLE;split;[exact witness_source_objects_exact|exact witness_source_cloexec_exact].
Qed.

Definition namespace_useful_child_ordinary_replacement cell command source memory pair parameters k:=
  exists branch_memory b after caller prefix world,
    namespace_useful_child_image_fields cell command source memory pair parameters k
      branch_memory b after caller prefix world /\namespace_worker_ordinary_input b after world.

Theorem namespace_same_child_supplies_ordinary cell command source memory pair parameters k:
  namespace_useful_child_replacement cell command source memory pair parameters k ->
  namespace_useful_child_ordinary_replacement cell command source memory pair parameters k.
Proof.
  intros(branch_memory &b &after &caller &prefix &world &FIELDS).
  pose proof FIELDS as(BORROWED &SNAPSHOT &BYTES &CANONICAL &SOURCE &GUEST &KERNEL &TABLE &EXACT &CHLD &MASK).
  exists branch_memory,b,after,caller,prefix,world;split;[exact FIELDS|].
  apply namespace_canonical_image_supplies_ordinary;assumption.
Qed.

Theorem namespace_actual_source_ordinary_entry_shaped_prepared:
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
    namespace_useful_child_ordinary_replacement cell command source fork_memory pair parameters
      (namespace_creation_cont e namespace_useful_parent_temps Kstop) /\
    inhabited(NamespaceUsefulParentShape cell e pair parameters fork_memory suffix final request) /\
    namespace_useful_preparation cell command source prepared e memory Int64.one.
Proof.
  destruct namespace_actual_parent_and_child_entry_shaped_prepared as(initial &cell &command &source &prepared &e &memory &pair &fork_memory
    &parameters &suffix &final &request &INITIAL &INPUT &CANONICAL &RUN_VALUE &STARTED &COMMON &QUEUES &EMPTY
    &MATCH &COPY &BORROWED &ARGUMENTS &PARENT &PARENT_EFFECT &CHILD &CHILD_EFFECT &GRANT &DESCRIPTOR &WRITE &CHILD_IMAGE &SHAPE &PREPARATION).
  pose proof(namespace_same_child_supplies_ordinary cell command source fork_memory pair parameters
    (namespace_creation_cont e namespace_useful_parent_temps Kstop)CHILD_IMAGE)as ORDINARY.
  exists initial,cell,command,source,prepared,e,memory,pair,fork_memory,parameters,suffix,final,request.
  repeat match goal with H:?P|-?P /\_=>split;[exact H|]end.
  exact PREPARATION.
Qed.

Theorem namespace_actual_source_ordinary_entry_shaped:
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
    namespace_useful_child_ordinary_replacement cell command source fork_memory pair parameters
      (namespace_creation_cont e namespace_useful_parent_temps Kstop) /\
    inhabited(NamespaceUsefulParentShape cell e pair parameters fork_memory suffix final request).
Proof.
  destruct namespace_actual_source_ordinary_entry_shaped_prepared as(initial &cell &command &source &prepared &e &memory &pair &fork_memory
    &parameters &suffix &final &request &INITIAL &INPUT &CANONICAL &RUN_VALUE &STARTED &COMMON &QUEUES &EMPTY
    &MATCH &COPY &BORROWED &ARGUMENTS &PARENT &PARENT_EFFECT &CHILD &CHILD_EFFECT &GRANT &DESCRIPTOR &WRITE &CHILD_IMAGE &SHAPE &PREPARATION).
  exists initial,cell,command,source,prepared,e,memory,pair,fork_memory,parameters,suffix,final,request.
  repeat match goal with H:?P|-?P /\_=>split;[exact H|]end.
  exact SHAPE.
Qed.

Theorem namespace_actual_source_ordinary_entry:
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
    namespace_useful_child_ordinary_replacement cell command source fork_memory pair parameters
      (namespace_creation_cont e namespace_useful_parent_temps Kstop).
Proof.
  destruct namespace_actual_source_ordinary_entry_shaped as(initial &cell &command &source &prepared &e &memory &pair &fork_memory
    &parameters &suffix &final &request &INITIAL &INPUT &CANONICAL &RUN_VALUE &STARTED &COMMON &QUEUES &EMPTY
    &MATCH &COPY &BORROWED &ARGUMENTS &PARENT &PARENT_EFFECT &CHILD &CHILD_EFFECT &GRANT &DESCRIPTOR &WRITE &CHILD_IMAGE &SHAPE).
  exists initial,cell,command,source,prepared,e,memory,pair,fork_memory,parameters,suffix,final,request.
  repeat match goal with H:?P|-?P /\_=>split;[exact H|]end.
  exact CHILD_IMAGE.
Qed.
