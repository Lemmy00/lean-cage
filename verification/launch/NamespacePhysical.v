(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.origin: Interpret the exact shared physical tick, without a second journal. *)
From Stdlib Require Import ZArith Arith List Lia Bool.
From compcert Require Import Integers Values.
From LeanImport Require Import Lean.
Require Import ArgumentsImport ArgumentValues.
From EntryProcess Require Import ProcessImport.
From EntryNamespace Require Import NamespaceObjects NamespaceHandles NamespaceChannel NamespaceGrant.
Import ListNotations.
Local Close Scope lean_scope.
Local Open Scope nat_scope.

Lemma physical_double_exact value:nat_of_Nat(double value)=2*nat_of_Nat value.
Proof. induction value;cbn[double nat_of_Nat];lia. Qed.
Lemma physical_succ_exact value:nat_of_Nat(Nat_succ value)=S(nat_of_Nat value).
Proof. reflexivity. Qed.
Lemma physical_ofnat_exact value:
  ProcessImport.OfNat_ofNat_inst1 Lean.Nat value(ProcessImport.instOfNatNat value)=value.
Proof. reflexivity. Qed.
Lemma physical_add_exact a b:
  nat_of_Nat(ProcessImport.Nat_add a b)=nat_of_Nat a+nat_of_Nat b.
Proof.
  induction b as[|b IH].
  - change(nat_of_Nat a=nat_of_Nat a+0);lia.
  - change(S(nat_of_Nat(ProcessImport.Nat_add a b))=nat_of_Nat a+S(nat_of_Nat b));rewrite IH;lia.
Qed.
Lemma physical_mul_exact a b:
  nat_of_Nat(ProcessImport.Nat_mul a b)=nat_of_Nat a*nat_of_Nat b.
Proof.
  induction b as[|b IH].
  - change(0=nat_of_Nat a*0);lia.
  - change(nat_of_Nat(ProcessImport.Nat_add(ProcessImport.Nat_mul a b)a)=
      nat_of_Nat a*S(nat_of_Nat b));rewrite physical_add_exact,IH;lia.
Qed.

Definition physical_task_key task:=
  task_incarnation task*Z.to_nat 2147483648+Z.to_nat(Int.unsigned(task_pid task)).

Definition physical_identity_pid task:=nat_of_Nat(LeanCage_Entry_ProcessIdentity_pid task).
Definition physical_identity_incarnation task:=nat_of_Nat(LeanCage_Entry_ProcessIdentity_incarnation task).
Definition physical_identity_task task:=
  {|task_pid:=Int.repr(Z.of_nat(physical_identity_pid task));
    task_incarnation:=physical_identity_incarnation task|}.

Theorem physical_identity_key_exact task:
  nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey task)=
    physical_identity_incarnation task*Z.to_nat 2147483648+physical_identity_pid task.
Proof.
  unfold LeanCage_Entry_CallerPhysical_taskKey,physical_identity_incarnation,physical_identity_pid.
  cbn[ProcessImport.HAdd_hAdd_inst7 ProcessImport.HMul_hMul_inst7 ProcessImport.instHAdd_inst1
    ProcessImport.instHMul_inst1 ProcessImport.instAddNat ProcessImport.instMulNat
    ProcessImport.OfNat_ofNat_inst1 ProcessImport.instOfNatNat].
  rewrite physical_add_exact,physical_mul_exact.
  rewrite physical_ofnat_exact.
  repeat first[rewrite physical_double_exact|rewrite physical_succ_exact];cbn[nat_of_Nat];lia.
Qed.

Theorem physical_identity_pid_range task:
  (1<=Z.of_nat(physical_identity_pid task)<=Int.max_signed)%Z.
Proof.
  pose proof(Nat_le_nat_le' _ _(ProcessImport.positive task))as POSITIVE.
  pose proof(Nat_le_nat_le' _ _(ProcessImport.bounded task))as BOUNDED.
  rewrite physical_ofnat_exact in POSITIVE,BOUNDED.
  repeat first[rewrite physical_double_exact in BOUNDED|rewrite physical_succ_exact in BOUNDED].
  cbn[nat_of_Nat]in POSITIVE,BOUNDED.
  unfold physical_identity_pid;change(1<=Z.of_nat(nat_of_Nat(LeanCage_Entry_ProcessIdentity_pid task))<=2147483647)%Z.
  unfold LeanCage_Entry_ProcessIdentity_pid;lia.
Qed.

Theorem physical_identity_task_pid task:
  Int.signed(task_pid(physical_identity_task task))=Z.of_nat(physical_identity_pid task).
Proof.
  pose proof(physical_identity_pid_range task)as RANGE.
  unfold physical_identity_task;cbn;rewrite Int.signed_repr;[reflexivity|].
  pose proof Int.min_signed_neg;lia.
Qed.

Theorem physical_identity_task_key task:
  physical_task_key(physical_identity_task task)=nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey task).
Proof.
  pose proof(physical_identity_pid_range task)as RANGE.
  change(1<=Z.of_nat(physical_identity_pid task)<=2147483647)%Z in RANGE.
  unfold physical_task_key,physical_identity_task;cbn[task_incarnation task_pid].
  rewrite Int.unsigned_repr by(change(0<=Z.of_nat(physical_identity_pid task)<=4294967295)%Z;lia).
  rewrite Nat2Z.id;symmetry;apply physical_identity_key_exact.
Qed.

Definition source_task_identity(task:TaskIdentity)(positive:(1<=Int.signed(task_pid task))%Z):
    LeanCage_Entry_ProcessIdentity.
Proof.
  refine(LeanCage_Entry_ProcessIdentity_mk(Nat_of_nat(Z.to_nat(Int.signed(task_pid task))))
    (Nat_of_nat(task_incarnation task)) _ _).
  - apply nat_le_Nat_le;rewrite physical_ofnat_exact,nat2Natid;cbn[nat_of_Nat];lia.
  - apply nat_le_Nat_le;rewrite physical_ofnat_exact,nat2Natid.
    repeat first[rewrite physical_double_exact|rewrite physical_succ_exact];cbn[nat_of_Nat].
    pose proof(Int.signed_range(task_pid task))as RANGE.
    change(-2147483648<=Int.signed(task_pid task)<=2147483647)%Z in RANGE;lia.
Defined.

Theorem source_task_identity_is_same task positive:
  physical_identity_task(source_task_identity task positive)=task.
Proof.
  change({|task_pid:=Int.repr(Z.of_nat(nat_of_Nat(Nat_of_nat(Z.to_nat(Int.signed(task_pid task))))));
    task_incarnation:=nat_of_Nat(Nat_of_nat(task_incarnation task))|}=task).
  rewrite !nat2Natid,Z2Nat.id by lia.
  rewrite Int.repr_signed;destruct task;reflexivity.
Qed.

Theorem source_task_identity_key_is_same task positive:
  nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey(source_task_identity task positive))=physical_task_key task.
Proof.
  rewrite <-physical_identity_task_key,source_task_identity_is_same;reflexivity.
Qed.

Definition physical_object(code:nat):DescriptorObject:=
  if Nat.eqb(code mod 3)0 then ordinary_object(code/3)
  else release_endpoint(code/3)(if Nat.eqb(code mod 3)1 then parent_endpoint else child_endpoint).

Theorem physical_object_code_exact object:
  physical_object(descriptor_object_code object)=object.
Proof.
  destruct object as[identity|channel side];[|destruct side];
    unfold physical_object,descriptor_object_code.
  - replace(identity*3)with(identity*3+0)by lia.
    rewrite Nat.div_add_l by lia.
    replace((identity*3+0)mod 3)with 0 by(apply Nat.mod_unique with(q:=identity);lia).
    cbn;rewrite Nat.add_0_r;reflexivity.
  - rewrite Nat.div_add_l by lia.
    replace((channel*3+1)mod 3)with 1 by(apply Nat.mod_unique with(q:=channel);lia).
    cbn;rewrite Nat.add_0_r;reflexivity.
  - rewrite Nat.div_add_l by lia.
    replace((channel*3+2)mod 3)with 2 by(apply Nat.mod_unique with(q:=channel);lia).
    cbn;rewrite Nat.add_0_r;reflexivity.
Qed.

Definition physical_bool(value:ProcessImport.Bool):bool:=match value with
  |ProcessImport.Bool_false=>false|ProcessImport.Bool_true=>true end.
Definition physical_flag(value:bool):ProcessImport.Bool:=if value then
  ProcessImport.Bool_true else ProcessImport.Bool_false.
Definition physical_objects(table:DescriptorTable)(fd:Lean.Nat):ProcessImport.Option_inst1 Lean.Nat:=
  if Z.leb(Z.of_nat(nat_of_Nat fd))Int.max_signed then
    match table(Int.repr(Z.of_nat(nat_of_Nat fd)))with
    |Some binding=>ProcessImport.Option_some_inst1 Lean.Nat(native_descriptor_object(descriptor_object binding))
    |None=>ProcessImport.Option_none_inst1 Lean.Nat end
  else ProcessImport.Option_none_inst1 Lean.Nat.
Definition physical_cloexec(table:DescriptorTable)(fd:Lean.Nat):ProcessImport.Bool:=
  if Z.leb(Z.of_nat(nat_of_Nat fd))Int.max_signed then
    match table(Int.repr(Z.of_nat(nat_of_Nat fd)))with
    |Some binding=>physical_flag(descriptor_cloexec binding)|None=>ProcessImport.Bool_false end
  else ProcessImport.Bool_false.

Definition physical_tick_table(tick:LeanCage_Entry_CallerPhysical_Tick)(actor:nat):DescriptorTable:=
  fun fd=>if Z.leb 0(Int.signed fd)then
    match ProcessImport.objects tick(Nat_of_nat actor)(native_descriptor_number fd)with
    |ProcessImport.Option_none_inst1 _=>None
    |ProcessImport.Option_some_inst1 _ object=>Some
      {|descriptor_object:=physical_object(nat_of_Nat object);
        descriptor_cloexec:=physical_bool
          (ProcessImport.cloexec tick(Nat_of_nat actor)(native_descriptor_number fd))|}
    end else None.

Theorem physical_tick_has_actual_binding tick actor table fd binding:
  (0<=Int.signed fd)%Z ->table fd=Some binding ->
  ProcessImport.objects tick(Nat_of_nat actor)(native_descriptor_number fd)=
    physical_objects table(native_descriptor_number fd) ->
  ProcessImport.cloexec tick(Nat_of_nat actor)(native_descriptor_number fd)=
    physical_cloexec table(native_descriptor_number fd) ->
  physical_tick_table tick actor fd=Some binding.
Proof.
  intros NONNEGATIVE PRESENT OBJECTS FLAGS.
  destruct(native_descriptor_number_valid fd NONNEGATIVE)as[BOUND NUMBER].
  assert(VALID:Z.leb 0(Int.signed fd)=true)by(apply Z.leb_le;exact NONNEGATIVE).
  unfold physical_tick_table;rewrite VALID,OBJECTS,FLAGS.
  unfold physical_objects,physical_cloexec;rewrite BOUND,NUMBER,PRESENT.
  cbn[physical_bool];rewrite native_descriptor_object_exact,physical_object_code_exact.
  destruct binding as[object flag];cbn;destruct flag;reflexivity.
Qed.

Theorem actual_source_produces_tick_binding tick actor table fd binding:
  (0<=Int.signed fd)%Z ->table fd=Some binding ->
  ProcessImport.objects tick actor(native_descriptor_number fd)=physical_objects table(native_descriptor_number fd) ->
  ProcessImport.cloexec tick actor(native_descriptor_number fd)=physical_cloexec table(native_descriptor_number fd) ->
  LeanCage_Entry_CallerPhysical_TickBinding tick actor(native_descriptor_number fd)
    (native_descriptor_object(descriptor_object binding))(physical_flag(descriptor_cloexec binding)).
Proof.
  intros NONNEGATIVE PRESENT OBJECTS FLAGS.
  destruct(native_descriptor_number_valid fd NONNEGATIVE)as[BOUND NUMBER].
  unfold physical_objects in OBJECTS;unfold physical_cloexec in FLAGS.
  rewrite BOUND,NUMBER,PRESENT in OBJECTS,FLAGS.
  unfold LeanCage_Entry_CallerPhysical_TickBinding,LeanCage_Entry_CallerPhysical_Tick_objects,
    LeanCage_Entry_CallerPhysical_Tick_cloexec;constructor;
    [rewrite OBJECTS|rewrite FLAGS];constructor.
Qed.

Theorem strict_tick_binding_is_actual tick actor fd object flag:
  (0<=Int.signed fd)%Z ->
  LeanCage_Entry_CallerPhysical_TickBinding tick actor(native_descriptor_number fd)
    (native_descriptor_object object)(physical_flag flag) ->
  physical_tick_table tick(nat_of_Nat actor)fd=
    Some{|descriptor_object:=object;descriptor_cloexec:=flag|}.
Proof.
  intros NONNEGATIVE BINDING;unfold LeanCage_Entry_CallerPhysical_TickBinding,
    LeanCage_Entry_CallerPhysical_Tick_objects,LeanCage_Entry_CallerPhysical_Tick_cloexec in BINDING.
  destruct BINDING as[OBJECT FLAG].
  assert(OBJECT':ProcessImport.objects tick actor(native_descriptor_number fd)=
      ProcessImport.Option_some_inst1 Lean.Nat(native_descriptor_object object)).
  { destruct OBJECT;reflexivity. }
  assert(FLAG':ProcessImport.cloexec tick actor(native_descriptor_number fd)=physical_flag flag).
  { destruct FLAG;reflexivity. }
  assert(VALID:Z.leb 0(Int.signed fd)=true)by(apply Z.leb_le;exact NONNEGATIVE).
  unfold physical_tick_table;rewrite VALID,Nat2natid,OBJECT',FLAG'.
  rewrite native_descriptor_object_exact,physical_object_code_exact.
  destruct flag;reflexivity.
Qed.

Fixpoint physical_bytes(bytes:ProcessImport.List_inst1 Lean.Nat):list Byte.int:=match bytes with
  |ProcessImport.List_nil_inst1 _=>[]
  |ProcessImport.List_cons_inst1 _ byte rest=>Byte.repr(Z.of_nat(nat_of_Nat byte))::physical_bytes rest end.
Fixpoint physical_bytes_valid(bytes:ProcessImport.List_inst1 Lean.Nat):bool:=match bytes with
  |ProcessImport.List_nil_inst1 _=>true
  |ProcessImport.List_cons_inst1 _ byte rest=>Nat.leb(nat_of_Nat byte)255&&physical_bytes_valid rest end.

Definition physical_descriptor(number:Lean.Nat):option int:=
  if Z.leb(Z.of_nat(nat_of_Nat number))Int.max_signed then
    Some(Int.repr(Z.of_nat(nat_of_Nat number)))else None.
Definition physical_select(tables:nat->DescriptorTable)actor channel number(event:int->ChannelEvent):=
  match physical_descriptor number with
  |None=>channel_passed
  |Some fd=>match tables actor fd with
    |None=>channel_passed
    |Some binding=>match descriptor_object binding with
      |ordinary_object _=>channel_passed
      |release_endpoint actual _=>if Nat.eqb actual channel then event fd else channel_passed
      end end end.

Definition physical_tick_projection channel(tick:LeanCage_Entry_CallerPhysical_Tick):=
  let tables:=physical_tick_table tick in(tables,match ProcessImport.socket tick with
  |LeanCage_Entry_CallerPhysical_SocketObservation_none=>channel_passed
  |LeanCage_Entry_CallerPhysical_SocketObservation_interrupted _ _=>channel_interrupted
  |LeanCage_Entry_CallerPhysical_SocketObservation_read actor fd wanted bytes=>
    if physical_bytes_valid bytes then
      physical_select tables(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor))channel fd
        (fun descriptor=>channel_read(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor))
          descriptor(nat_of_Nat wanted)(physical_bytes bytes))
    else channel_passed
  |LeanCage_Entry_CallerPhysical_SocketObservation_wrote actor fd bytes lost=>
    if physical_bytes_valid bytes then
      physical_select tables(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor))channel fd
        (fun descriptor=>channel_sent(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor))
          descriptor(physical_bytes bytes)(physical_bool lost))
    else channel_passed end).

Theorem physical_select_endpoint tables actor channel fd event binding side:
  (0<=Int.signed fd)%Z ->tables actor fd=Some binding ->
  descriptor_object binding=release_endpoint channel side ->
  physical_select tables actor channel(native_descriptor_number fd)event=event fd.
Proof.
  intros NONNEGATIVE PRESENT OBJECT.
  destruct(native_descriptor_number_valid fd NONNEGATIVE)as[BOUND NUMBER].
  unfold physical_select,physical_descriptor;rewrite BOUND,NUMBER,PRESENT,OBJECT,Nat.eqb_refl;reflexivity.
Qed.

Theorem physical_tick_read_projection channel tick actor fd wanted bytes binding:
  ProcessImport.socket tick=LeanCage_Entry_CallerPhysical_SocketObservation_read actor
    (native_descriptor_number fd)(Nat_of_nat wanted)bytes ->
  physical_bytes_valid bytes=true ->(0<=Int.signed fd)%Z ->
  physical_tick_table tick(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor))fd=Some binding ->
  descriptor_object binding=release_endpoint channel child_endpoint ->
  physical_tick_projection channel tick=
    (physical_tick_table tick,channel_read(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor))
      fd wanted(physical_bytes bytes)).
Proof.
  intros SOCKET BYTES NONNEGATIVE PRESENT OBJECT.
  unfold physical_tick_projection;rewrite SOCKET,BYTES;cbn beta iota zeta;rewrite nat2Natid.
  rewrite(physical_select_endpoint _ _ _ _ _ _ _ NONNEGATIVE PRESENT OBJECT);reflexivity.
Qed.

Theorem physical_tick_write_projection channel tick actor fd bytes lost binding side:
  ProcessImport.socket tick=LeanCage_Entry_CallerPhysical_SocketObservation_wrote actor
    (native_descriptor_number fd)bytes lost ->
  physical_bytes_valid bytes=true ->(0<=Int.signed fd)%Z ->
  physical_tick_table tick(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor))fd=Some binding ->
  descriptor_object binding=release_endpoint channel side ->
  physical_tick_projection channel tick=
    (physical_tick_table tick,channel_sent(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor))
      fd(physical_bytes bytes)(physical_bool lost)).
Proof.
  intros SOCKET BYTES NONNEGATIVE PRESENT OBJECT.
  unfold physical_tick_projection;rewrite SOCKET,BYTES;cbn beta iota zeta.
  rewrite(physical_select_endpoint _ _ _ _ _ _ _ NONNEGATIVE PRESENT OBJECT);reflexivity.
Qed.

Definition physical_queue_operation channel tick before after:=
  channel_operation(physical_tick_table tick)channel before
    (Datatypes.snd(physical_tick_projection channel tick))after.

(* This relation interprets each tick of the one shared physical journal;
   uninteresting operations retain their positions as channel_passed. *)
Inductive physical_queue_execution channel:ChannelBuffers->
    list LeanCage_Entry_CallerPhysical_Tick->ChannelBuffers->Prop:=
| physical_queue_nil:forall state,physical_queue_execution channel state[]state
| physical_queue_cons:forall before tick middle rest after,
    physical_queue_operation channel tick before middle ->
    physical_queue_execution channel middle rest after ->
    physical_queue_execution channel before(tick::rest)after.

Theorem physical_queue_execution_projects channel before ticks after:
  physical_queue_execution channel before ticks after ->
  channel_execution channel before(map(physical_tick_projection channel)ticks)after.
Proof.
  intro RUN;induction RUN;[constructor|].
  cbn[map];destruct(physical_tick_projection channel tick)as[tables event]eqn:PROJECT.
  assert(TABLES:tables=physical_tick_table tick).
  { pose proof(f_equal(Datatypes.fst)PROJECT)as TABLES;exact(eq_sym TABLES). }
  unfold physical_queue_operation in H;rewrite PROJECT in H;cbn in H;subst tables.
  econstructor;eassumption.
Qed.

Theorem physical_queue_execution_split channel before prefix suffix after:
  physical_queue_execution channel before(prefix++suffix)after ->
  exists middle,physical_queue_execution channel before prefix middle /\
    physical_queue_execution channel middle suffix after.
Proof.
  revert before;induction prefix as[|tick rest IH];intros before RUN;cbn in RUN.
  - exists before;split;[constructor|exact RUN].
  - inversion RUN;subst;destruct(IH _ H4)as[boundary[FIRST LAST]].
    exists boundary;split;[econstructor;eassumption|exact LAST].
Qed.

Definition physical_grant_owned parent channel tick:=
  grant_write_owned(physical_tick_table tick)parent channel
    (Datatypes.snd(physical_tick_projection channel tick)).

Theorem actual_physical_read_has_prior_global_send start parent channel ticks after read_position tick
    actor fd wanted bytes binding:
  physical_queue_execution channel channel_empty ticks after ->
  Forall(physical_grant_owned parent channel)ticks ->nth_error ticks read_position=Some tick ->
  ProcessImport.socket tick=LeanCage_Entry_CallerPhysical_SocketObservation_read actor
    (native_descriptor_number fd)(Nat_of_nat wanted)bytes ->
  physical_bytes_valid bytes=true ->(0<=Int.signed fd)%Z ->
  physical_tick_table tick(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor))fd=Some binding ->
  descriptor_object binding=release_endpoint channel child_endpoint ->
  In(Byte.repr 165)(physical_bytes bytes) ->
  exists send_position sent_tick source_fd sent lost,
    nth_error ticks send_position=Some sent_tick /\send_position<read_position /\
    physical_tick_projection channel sent_tick=
      (physical_tick_table sent_tick,channel_sent parent source_fd sent lost) /\
    In(Byte.repr 165)sent /\checked_grant_order(start+send_position)(start+read_position).
Proof.
  intros RUN OWNED SELECTED SOCKET BYTES NONNEGATIVE PRESENT OBJECT BYTE.
  destruct(nth_error_split _ _ SELECTED)as[prefix[suffix[TICKS POSITION]]];subst ticks.
  destruct(physical_queue_execution_split _ _ _ _ _ RUN)as[before[PRIOR REMAINING]].
  inversion REMAINING;subst.
  pose proof(physical_tick_read_projection _ _ _ _ _ _ _ SOCKET BYTES NONNEGATIVE PRESENT OBJECT)as READ.
  match goal with OPERATION:physical_queue_operation _ _ _ _|-_=>
    unfold physical_queue_operation in OPERATION;rewrite READ in OPERATION;cbn beta iota zeta in OPERATION end.
  assert(PREFIX_OWNED:Forall(fun observation=>
    grant_write_owned(Datatypes.fst observation)parent channel(Datatypes.snd observation))
      (map(physical_tick_projection channel)prefix)).
  { apply Forall_map;apply Forall_app in OWNED as[OWNED _].
    eapply Forall_impl;[|exact OWNED];intros current GOOD.
    unfold physical_grant_owned in GOOD.
    change(grant_write_owned(physical_tick_table current)parent channel
      (Datatypes.snd(physical_tick_projection channel current))).
    exact GOOD. }
  destruct(actual_private_read_has_prior_global_send _ (physical_tick_projection channel)
    parent channel prefix before(physical_tick_table tick)
    (nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor))fd wanted(physical_bytes bytes)
    _ (Byte.repr 165) PREFIX_OWNED(physical_queue_execution_projects _ _ _ _ PRIOR)
      ltac:(exists binding;auto)ltac:(eassumption)BYTE)
    as[raw[tables[source_fd[sent[lost[position[SELECT[SOURCE[SENT[BEFORE ORDER]]]]]]]]]].
  assert(TABLES:tables=physical_tick_table raw).
  { pose proof(f_equal(Datatypes.fst)SOURCE)as TABLES;exact(eq_sym TABLES). }
  subst tables;exists position,raw,source_fd,sent,lost.
  split;[rewrite nth_error_app1 by exact BEFORE;exact SELECT|].
  split;[exact BEFORE|]. split;[exact SOURCE|]. split;[exact SENT|].
  constructor;apply physical_order_is_ordinary;lia.
Qed.

Definition physical_grant_bytes:=ProcessImport.List_cons_inst1 Lean.Nat(Nat_of_nat 165)
  (ProcessImport.List_nil_inst1 Lean.Nat).

Theorem actual_bound_read_has_prior_global_send start parent channel ticks after read_position tick actor fd flag:
  physical_queue_execution channel channel_empty ticks after ->
  Forall(physical_grant_owned parent channel)ticks ->nth_error ticks read_position=Some tick ->
  Lean.eq(ProcessImport.socket tick)(LeanCage_Entry_CallerPhysical_SocketObservation_read actor
    (native_descriptor_number fd)(Nat_of_nat 1)physical_grant_bytes) ->
  (0<=Int.signed fd)%Z ->
  LeanCage_Entry_CallerPhysical_TickBinding tick(LeanCage_Entry_CallerPhysical_taskKey actor)
    (native_descriptor_number fd)(native_descriptor_object(release_endpoint channel child_endpoint))
    (physical_flag flag) ->
  exists send_position sent_tick source_fd sent lost,
    nth_error ticks send_position=Some sent_tick /\send_position<read_position /\
    physical_tick_projection channel sent_tick=
      (physical_tick_table sent_tick,channel_sent parent source_fd sent lost) /\
    In(Byte.repr 165)sent /\checked_grant_order(start+send_position)(start+read_position).
Proof.
  intros RUN OWNED SELECTED SOCKET NONNEGATIVE BINDING.
  assert(SOCKET':ProcessImport.socket tick=LeanCage_Entry_CallerPhysical_SocketObservation_read actor
      (native_descriptor_number fd)(Nat_of_nat 1)physical_grant_bytes).
  { destruct SOCKET;reflexivity. }
  eapply actual_physical_read_has_prior_global_send with(actor:=actor)(fd:=fd)
    (binding:={|descriptor_object:=release_endpoint channel child_endpoint;descriptor_cloexec:=flag|}).
  - exact RUN.
  - exact OWNED.
  - exact SELECTED.
  - exact SOCKET'.
  - reflexivity.
  - exact NONNEGATIVE.
  - apply strict_tick_binding_is_actual;assumption.
  - reflexivity.
  - left;reflexivity.
Qed.
