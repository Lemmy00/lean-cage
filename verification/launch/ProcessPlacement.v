(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.pid: The actual stopped child and validated bytes select placement and options. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Globalenvs
  Ctypes Ctypesdefs Cop Clight.
Require Import IO Machine Deterministic ClightSteps StoreSteps LocalAccess CallAccess WriteAll WriteMemory ErrorNumber.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffArguments NativeHandoffNumeric.
From EntryProcess Require Import ProcessMachine ProcessAllocation ProcessStructure ProcessPaths ProcessCalls ProcessContexts.
From LeanCageMainNumber Require Import NumberMemory NumberControl.
Import ListNotations.
Open Scope Z_scope.

Lemma admission_placement_actual :
  admission_place=Ssequence
    (Scall (Some _t'6) (Evar _write_all(Tfunction [tint;tptr tvoid;tulong] tint cc_default))
      [Etempvar _cgfd tint;Evar _pidtext(tarray tschar 32);Ecast(Etempvar _pidlength tint)tulong])
    (Sifthenelse(Etempvar _t'6 tint)admission_failure Sskip) /\
  admission_options=Ssequence
    (Scall (Some _t'7) (Evar _entry_ptrace4(Tfunction [tint;tint;tptr tvoid;tptr tvoid] tlong cc_default))
      [Econst_int(Int.repr 16896)tint;Etempvar _child tint;
       Ecast(Econst_int Int.zero tint)(tptr tvoid);
       Ecast(Ecast(Ebinop Oor(Econst_int(Int.repr 16)tint)
         (Econst_int(Int.repr 1048576)tint)tint)tulong)(tptr tvoid)])
    (Sifthenelse(Etempvar _t'7 tlong)admission_failure Sskip).
Proof. split; reflexivity. Qed.

Lemma admission_write_binding :
  Genv.find_symbol admission_ge _write_all=Some(handoff_symbol _write_all) /\
  Genv.find_funct admission_ge(Vptr(handoff_symbol _write_all)Ptrofs.zero)=Some(Internal f_write_all).
Proof. split; reflexivity. Qed.

Lemma admission_options_binding :
  Genv.find_symbol admission_ge _entry_ptrace4=Some(handoff_symbol _entry_ptrace4) /\
  Genv.find_funct admission_ge(Vptr(handoff_symbol _entry_ptrace4)Ptrofs.zero)=Some process_ptrace_definition.
Proof. split; reflexivity. Qed.

Definition admission_write_cont locals le k :=
  Kcall (Some _t'6) f_admit_child (admission_env locals) le
    (Kseq(Sifthenelse(Etempvar _t'6 tint)admission_failure Sskip)k).

Theorem admission_write_call_source locals le m count cgroup k :
  le!_cgfd=Some(Vint cgroup) -> le!_pidlength=Some(Vint count) ->
  store_path admission_ge (fun after=>after=m)
    (State f_admit_child admission_place k (admission_env locals) le m) 2
    (Callstate(Internal f_write_all)
      [Vint cgroup;Vptr(admission_text locals)Ptrofs.zero;Vlong(Int64.repr(Int.signed count))]
      (admission_write_cont locals le k)m).
Proof.
  intros CGROUP COUNT; rewrite(proj1 admission_placement_actual); unfold admission_write_cont.
  handoff_route; eapply store_next; [reflexivity| |].
  - eapply certified_call_edge.
    + reflexivity.
    + apply old_expression_value; eapply value_function;
        [apply admission_nonlocal_binding;discriminate|exact(proj1 admission_write_binding)|reflexivity].
    + eapply cons_argument_values.
      * apply old_expression_value,value_temp; exact CGROUP.
      * reflexivity.
      * eapply cons_argument_values.
        -- apply handoff_array_value; apply(proj1(admission_local_bindings locals)).
        -- reflexivity.
        -- eapply cons_argument_values.
           ++ eapply cast_expression_value; [apply old_expression_value,value_temp;exact COUNT|reflexivity].
           ++ reflexivity.
           ++ apply no_argument_values.
    + exact(proj2 admission_write_binding).
    + reflexivity.
  - apply store_done; reflexivity.
Qed.


Theorem admission_write_return_source locals le m returned k :
  store_path admission_ge (fun after=>after=m)
    (Returnstate(Vint returned)(admission_write_cont locals le k)m) 3
    (State f_admit_child (if Int.eq returned Int.zero then Sskip else admission_failure)
      k (admission_env locals)(PTree.set _t'6(Vint returned)le)m).
Proof.
  unfold admission_write_cont.
  replace(if Int.eq returned Int.zero then Sskip else admission_failure)
    with(if negb(Int.eq returned Int.zero)then admission_failure else Sskip)
    by(destruct(Int.eq returned Int.zero);reflexivity).
  handoff_route; handoff_route; eapply store_next; [reflexivity|apply certified_if_edge with
    (v:=Vint returned)(b:=negb(Int.eq returned Int.zero))|].
  - apply old_expression_value,value_temp; apply PTree.gss.
  - reflexivity.
  - apply store_done; reflexivity.
Qed.

Definition admission_options_cont locals le k :=
  Kcall (Some _t'7) f_admit_child (admission_env locals) le
    (Kseq(Sifthenelse(Etempvar _t'7 tlong)admission_failure Sskip)k).

Theorem admission_options_call_source locals le m child k :
  le!_child=Some(Vint child) ->
  store_path admission_ge (fun after=>after=m)
    (State f_admit_child admission_options k (admission_env locals) le m) 2
    (Callstate process_ptrace_definition
      [Vint(Int.repr 16896);Vint child;Vlong Int64.zero;Vlong(Int64.repr 1048592)]
      (admission_options_cont locals le k)m).
Proof.
  intros CHILD; rewrite(proj2 admission_placement_actual); unfold admission_options_cont.
  handoff_route; eapply store_next; [reflexivity| |].
  - eapply certified_call_edge.
    + reflexivity.
    + apply old_expression_value; eapply value_function;
        [apply admission_nonlocal_binding;discriminate|exact(proj1 admission_options_binding)|reflexivity].
    + eapply cons_argument_values.
      * apply old_expression_value,value_int.
      * reflexivity.
      * eapply cons_argument_values.
        -- apply old_expression_value,value_temp; exact CHILD.
        -- reflexivity.
        -- eapply cons_argument_values.
           ++ eapply cast_expression_value; [apply old_expression_value,value_int|reflexivity].
           ++ reflexivity.
           ++ eapply cons_argument_values.
              ** eapply cast_expression_value.
                 --- eapply cast_expression_value.
                     +++ eapply binary_expression_value;
                           [apply old_expression_value,value_int|apply old_expression_value,value_int|reflexivity].
                     +++ reflexivity.
                 --- reflexivity.
              ** reflexivity.
              ** apply no_argument_values.
    + exact(proj2 admission_options_binding).
    + reflexivity.
  - apply store_done; reflexivity.
Qed.

Theorem admission_options_return_source locals le m returned k :
  store_path admission_ge (fun after=>after=m)
    (Returnstate(Vlong returned)(admission_options_cont locals le k)m) 3
    (State f_admit_child (if Int64.eq returned Int64.zero then Sskip else admission_failure)
      k (admission_env locals)(PTree.set _t'7(Vlong returned)le)m).
Proof.
  unfold admission_options_cont.
  replace(if Int64.eq returned Int64.zero then Sskip else admission_failure)
    with(if negb(Int64.eq returned Int64.zero)then admission_failure else Sskip)
    by(destruct(Int64.eq returned Int64.zero);reflexivity).
  handoff_route; handoff_route; eapply store_next; [reflexivity|apply certified_if_edge with
    (v:=Vlong returned)(b:=negb(Int64.eq returned Int64.zero))|].
  - apply old_expression_value,value_temp; apply PTree.gss.
  - reflexivity.
  - apply store_done; reflexivity.
Qed.

Definition admission_write_request cell locals cgroup count :=
  {|operation:=writing;descriptor:=cgroup;buffer_block:=admission_text locals;buffer_offset:=0;
    requested:=Int.signed count;errno_block:=tls_block cell;errno_offset:=tls_offset cell|}.

Theorem admission_write_owned cell locals m count cgroup bytes error :
  number_input m (admission_text locals) Ptrofs.zero bytes ->
  Z.of_nat(length bytes)=Int.signed count -> 1<=Int.signed count<=31 ->
  initialized_errno cell m error -> admission_text locals<>tls_block cell ->
  write_owned(admission_write_request cell locals cgroup count)bytes m.
Proof.
  intros [BOUND [NONZERO LOAD]] LENGTH EXTENT [LOW [HIGH [ACCESS ERROR]]] SEPARATE.
  assert (BYTES:Mem.loadbytes m (admission_text locals)0(Int.signed count)=Some(map Byte bytes)).
  { rewrite <-LENGTH; eapply load_first with(rest:=[Byte.zero]); exact LOAD. }
  unfold write_owned,admission_write_request; cbn; split; [reflexivity|].
  split.
  - unfold owned; cbn; split; [lia|]. split; [change Ptrofs.modulus with 18446744073709551616;lia|].
    split; [change (Int.signed count<=18446744073709551616);lia|].
    split; [exact LOW|]. split; [exact HIGH|]. split; [exact ACCESS|].
    split; [left;exact SEPARATE|]. exists bytes; auto.
  - split; assumption.
Qed.

Lemma placement_suffix_zero q : operation q=writing -> suffix q 0=q.
Proof.
  destruct q; cbn; intros OP; subst; unfold suffix; cbn.
  rewrite Z.add_0_r,Z.sub_0_r; reflexivity.
Qed.

(* The first positive write is a real source-selected syscall, including after
   any number of failed EINTR attempts. No caller-success premise selects it. *)
Lemma placement_first_request ge q input last state actual bytes error target :
  WriteAll.invariant ge q input [] last (live state) ->
  Machine.step ge (cell_of q) (live state) (io_step actual (transfer bytes error)) target ->
  actual=q /\ exists before after, write_owned q input before /\
    io_return q before (transfer bytes error) after.
Proof.
  intros INV STEP; inversion INV as [s ROUTED|]; subst.
  destruct ROUTED as [endpoint [PATH END]].
  inversion PATH as [|s middle final_state EDGE REST]; subst.
  - inversion END as [rest le m EQ NE OWN REGS|rest le m err EQ NE OWN REGS N LAST LOAD|
      m EQ OWN|rest m EQ NE OWN FAIL]; subst.
    + assert (SUFFIX:owned(suffix q 0)m).
      { exact(suffix_owned q [] rest m OWN NE). }
      destruct(write_machine_cases _ _ _ _ _ _ _ SUFFIX STEP)
        as [[reply [after [EFFECT [EVENT TARGET]]]]|[[EVENT TARGET]|[[EVENT TARGET]|
          [part [err [after [EFFECT [EVENT TARGET]]]]]]]];
        try discriminate EVENT.
      inversion EVENT; subst actual reply.
      assert (SAME:suffix q 0=q) by (apply placement_suffix_zero;exact(proj1 OWN)).
      rewrite SAME in EFFECT|-*; split; [reflexivity|]. exists m,after; auto.
    + destruct(errno_machine_cases _ _ _ _ _ _ STEP) as [[EVENT TARGET]|[EVENT TARGET]]; discriminate.
    + destruct(terminal_machine_cases _ _ _ _ _ _ STEP) as [EVENT TARGET]; discriminate.
    + destruct(terminal_machine_cases _ _ _ _ _ _ STEP) as [EVENT TARGET]; discriminate.
  - destruct(machine_edge_cases _ _ _ _ _ _ EDGE STEP) as [[EVENT TARGET]|[EVENT TARGET]]; discriminate.
Qed.

Definition cgroup_whole_returns (fd:int) (events:list Machine.event) :=
  forall actual bytes error,
    In(io_step actual(transfer bytes error))events -> IO.descriptor actual=fd ->
    IO.operation actual=writing ->
    Z.of_nat(length bytes)=requested actual.

Lemma placement_full_bytes q input before bytes error after :
  write_owned q input before -> io_return q before (transfer bytes error) after ->
  Z.of_nat(length bytes)=requested q -> bytes=input.
Proof.
  intros [OP [OWN [LENGTH LOAD]]] EFFECT WHOLE; inversion EFFECT; subst; try congruence.
  match goal with PART:Mem.loadbytes _ _ _ _=Some(map Byte bytes) |- _ =>
    rewrite WHOLE in PART end.
  apply map_byte_injective; congruence.
Qed.

Theorem placement_first_full_transfer ge q input start events final last :
  WriteAll.symbols ge -> WriteAll.invariant ge q input [] last start ->
  Machine.steps ge (cell_of q) start events (live final) ->
  cgroup_whole_returns (IO.descriptor q) events -> emitted_trace events<>[] ->
  exists error, In(io_step q(transfer input error))events.
Proof.
  intros SYMBOLS INV RUN; remember(live final)as target eqn:TARGET.
  revert last final TARGET INV.
  induction RUN as [start|start event middle events target STEP RUN IH];
    intros last final TARGET INV WHOLE NONEMPTY; unfold cgroup_whole_returns in WHOLE.
  - exfalso; apply NONEMPTY; reflexivity.
  - destruct (emitted event) as [|byte bytes] eqn:EMITTED.
    + assert (NEXT:WriteAll.invariant ge q input [] (last_update last event) middle).
      { pose proof(write_all_invariant_step _ _ _ _ _ _ _ _ SYMBOLS INV STEP)as NEXT.
        rewrite EMITTED in NEXT; cbn in NEXT; exact NEXT. }
      destruct(IH _ _ TARGET NEXT)as[error MEMBER].
      * intros actual bytes0 error0 MEMBER DESCRIPTOR WRITING;
          eapply WHOLE;[right;exact MEMBER|exact DESCRIPTOR|exact WRITING].
      * unfold emitted_trace in *; cbn in NONEMPTY; rewrite EMITTED in NONEMPTY; exact NONEMPTY.
      * exists error; right; exact MEMBER.
    + destruct start as[state|memory].
      2:{ inversion STEP. }
      destruct event; cbn [emitted] in EMITTED; try discriminate.
      * destruct r; cbn [emitted] in EMITTED; try discriminate.
        destruct(placement_first_request _ _ _ _ _ _ _ _ _ INV STEP)
          as[SAME[before[after[OWN EFFECT]]]]; subst q0.
        assert(FULL:Z.of_nat(length bytes0)=requested q).
        { eapply WHOLE; [left;reflexivity|reflexivity|exact(proj1 OWN)]. }
        assert(SAME:bytes0=input)by(eapply placement_full_bytes;eassumption).
        subst bytes0; exists errno; left; now rewrite SAME.
      * destruct(Machine.partial_loss_never_returns _ _ _ _ _ _ _ STEP)as[memory DEAD].
        subst middle; destruct(Deterministic.dead_steps _ _ _ _ _ RUN)as[EVENTS TERMINAL]; congruence.
Qed.

Definition placement_lift event := process_entry(entry_library(LibraryMachine.original_event event)).
Definition process_cgroup_whole_returns (fd:int) (events:list process_event) :=
  forall actual bytes error,
    In(placement_lift(io_step actual(transfer bytes error)))events -> IO.descriptor actual=fd ->
    IO.operation actual=writing ->
    Z.of_nat(length bytes)=requested actual.

Lemma placement_lift_injective left right : map placement_lift left=map placement_lift right -> left=right.
Proof.
  revert right; induction left as[|a left IH]; destruct right as[|b right];cbn;intros SAME;try discriminate.
  - reflexivity.
  - inversion SAME; subst; f_equal; auto.
Qed.

(* This law constrains positive returns at the owned cgroup object. Terminal
   partial-copy/loss events remain permitted; they cannot reach a live return. *)
Theorem current_cgroup_process_return q input before events after :
  write_owned q input before -> input<>[] ->
  process_steps admission_ge (cell_of q)
    (live(Callstate(Internal f_write_all)
      [Vint(IO.descriptor q);Vptr(buffer_block q)(Ptrofs.repr(buffer_offset q));
       Vlong(Int64.repr(requested q))]Kstop before))events
    (live(Returnstate(Vint Int.zero)Kstop after)) ->
  process_cgroup_whole_returns (IO.descriptor q) events ->
  write_owned q input after /\
    exists error,In(placement_lift(io_step q(transfer input error)))events.
Proof.
  intros OWN NONEMPTY RUN WHOLE.
  destruct(current_write_process_return q input before events (Vint Int.zero) after OWN RUN)
    as[original[EVENTS[PRESERVED[RESULT|[IMPOSSIBLE REST]]]]];[|discriminate].
  destruct RESULT as[VALUE EMITTED].
  pose proof RUN as REAL.
  rewrite NativeHandoffBindings.current_entry_write_all_exact in REAL.
  change(process_steps admission_ge(cell_of q)(live(WriteAll.initial_state q before))events
    (live(Returnstate(Vint Int.zero)Kstop after)))in REAL.
  destruct(process_write_invariant_projection _ _ _ _ _ _ REAL current_write_symbols [] None
    (invariant_initial _ _ _ _ current_write_symbols OWN))as[replayed[SAME SOURCE]].
  assert(IDENTICAL:replayed=original).
  { apply placement_lift_injective; unfold placement_lift; congruence. }
  subst replayed.
  assert(CGROUP:cgroup_whole_returns (IO.descriptor q) original).
  { intros actual bytes error MEMBER DESCRIPTOR WRITING.
    eapply WHOLE; [rewrite EVENTS;apply in_map;exact MEMBER|exact DESCRIPTOR|exact WRITING]. }
  destruct(placement_first_full_transfer _ _ _ _ _ _ _ current_write_symbols
    (invariant_initial _ _ _ _ current_write_symbols OWN) SOURCE CGROUP
    ltac:(rewrite EMITTED;exact NONEMPTY))as[error MEMBER].
  assert(PRESENT:In(placement_lift(io_step q(transfer input error)))events).
  { rewrite EVENTS; apply in_map; exact MEMBER. }
  split; [exact PRESERVED|exists error;exact PRESENT].
Qed.

Lemma placement_path_live_events ge cell start finish :
  path ge start finish ->forall value memory,finish=Returnstate value Kstop memory ->
  forall events final,Machine.steps ge cell(live start)events(live final) ->
    Forall(fun event=>event=source_step E0)events.
Proof.
  intros PATH;induction PATH;intros value memory TERMINAL events final RUN.
  - subst s;inversion RUN as[|first event next rest endpoint STEP TAIL];subst;[constructor|].
    destruct(Deterministic.returned_step _ _ _ _ _ _ STEP)as[EVENT TARGET];subst.
    destruct(Deterministic.dead_steps _ _ _ _ _ TAIL)as[EVENTS TERMINAL];discriminate.
  - inversion RUN as[|first event next rest endpoint STEP TAIL];subst;[constructor|].
    destruct(machine_edge_cases _ _ _ _ _ _ H STEP)as[[EVENT TARGET]|[EVENT TARGET]];subst.
    + constructor;[reflexivity|eapply IHPATH;[reflexivity|exact TAIL]].
    + destruct(Deterministic.dead_steps _ _ _ _ _ TAIL)as[EVENTS TERMINAL];discriminate.
Qed.

Lemma placement_completed_path ge q input last state :
  WriteAll.invariant ge q input input last(live state) ->
  exists memory,path ge state(Returnstate(Vint Int.zero)Kstop memory).
Proof.
  intros INV;inversion INV as[s ROUTED|];subst.
  destruct ROUTED as[endpoint[PATH END]].
  inversion END as[rest le memory EQ NONEMPTY OWN REGS|
    rest le memory error EQ NONEMPTY OWN REGS N LAST LOAD|memory EQ OWN|
    rest memory EQ NONEMPTY OWN FAILED];subst.
  all:try(assert(EMPTY:rest=[])
    by(apply app_inv_head with(l:=input);rewrite app_nil_r;symmetry;exact EQ);
    contradiction).
  eauto.
Qed.

Lemma placement_machine_split ge cell start prefix suffix final :
  Machine.steps ge cell start(prefix++suffix)final ->
  exists middle,Machine.steps ge cell start prefix middle /\Machine.steps ge cell middle suffix final.
Proof.
  revert start;induction prefix as[|event rest IH];intros start RUN;cbn in RUN.
  - exists start;split;[constructor|exact RUN].
  - inversion RUN as[|first current next tail last STEP TAIL];subst.
    destruct(IH _ TAIL)as[middle[PREFIX SUFFIX]].
    exists middle;split;[econstructor;eassumption|exact SUFFIX].
Qed.

Theorem placement_transfer_source_suffix ge q input before events after error :
  WriteAll.symbols ge ->write_owned q input before ->
  Machine.steps ge(cell_of q)(live(WriteAll.initial_state q before))events
    (live(Returnstate(Vint Int.zero)Kstop after)) ->
  emitted_trace events=input ->In(io_step q(transfer input error))events ->
  exists prefix suffix,events=prefix++io_step q(transfer input error)::suffix /\
    Forall(fun event=>event=source_step E0)suffix.
Proof.
  intros SYMBOLS OWN RUN EMITTED MEMBER.
  apply in_split in MEMBER as[prefix[suffix ORDER]].
  assert(EMPTY:emitted_trace prefix=[]).
  { apply length_zero_iff_nil.
    unfold emitted_trace.
    rewrite ORDER in EMITTED;unfold emitted_trace in EMITTED;rewrite flat_map_app in EMITTED.
    cbn[flat_map emitted]in EMITTED;pose proof(f_equal (@length Byte.int)EMITTED)as LENGTH.
    rewrite !length_app in LENGTH;lia. }
  rewrite ORDER in RUN.
  destruct(placement_machine_split _ _ _ _ _ _ RUN)as[frontier[PREFIX REST]].
  inversion REST as[|first event next tail last STEP TAIL];subst.
  pose proof(write_all_invariant_runs _ _ _ _ _ _ PREFIX SYMBOLS [] None
    (invariant_initial _ _ _ _ SYMBOLS OWN))as INV.
  rewrite app_nil_l,EMPTY in INV.
  pose proof(write_all_invariant_step _ _ _ _ _ _ _ _ SYMBOLS INV STEP)as NEXT.
  cbn[emitted app]in NEXT.
  destruct next as[state|memory].
  - destruct(placement_completed_path _ _ _ _ _ NEXT)as[final PATH].
    exists prefix,suffix;split;[exact ORDER|].
    eapply placement_path_live_events;[exact PATH|reflexivity|exact TAIL].
  - destruct(Deterministic.dead_steps _ _ _ _ _ TAIL)as[EVENTS TERMINAL];discriminate.
Qed.

Theorem current_cgroup_process_return_split q input before events after :
  write_owned q input before ->input<>[] ->
  process_steps admission_ge(cell_of q)
    (live(Callstate(Internal f_write_all)
      [Vint(IO.descriptor q);Vptr(buffer_block q)(Ptrofs.repr(buffer_offset q));
       Vlong(Int64.repr(requested q))]Kstop before))events
    (live(Returnstate(Vint Int.zero)Kstop after)) ->
  process_cgroup_whole_returns(IO.descriptor q)events ->
  write_owned q input after /\exists error prefix suffix,
    events=prefix++placement_lift(io_step q(transfer input error))::suffix /\
    Forall(fun event=>event=process_source_event)suffix.
Proof.
  intros OWN NONEMPTY RUN WHOLE.
  destruct(current_cgroup_process_return _ _ _ _ _ OWN NONEMPTY RUN WHOLE)
    as[PRESERVED[error MEMBER]].
  destruct(current_write_process_return q input before events(Vint Int.zero)after OWN RUN)
    as[original[EVENTS[FRAME[[VALUE EMITTED]|[IMPOSSIBLE REST]]]]];[|discriminate].
  rewrite EVENTS in MEMBER;apply in_map_iff in MEMBER.
  destruct MEMBER as[event[SAME MEMBER]].
  change(placement_lift event=placement_lift(io_step q(transfer input error)))in SAME.
  assert(IDENTICAL:event=io_step q(transfer input error))by(inversion SAME;reflexivity);subst event.
  pose proof RUN as REAL;rewrite NativeHandoffBindings.current_entry_write_all_exact in REAL.
  change(process_steps admission_ge(cell_of q)(live(WriteAll.initial_state q before))events
    (live(Returnstate(Vint Int.zero)Kstop after)))in REAL.
  destruct(process_write_invariant_projection _ _ _ _ _ _ REAL current_write_symbols [] None
    (invariant_initial _ _ _ _ current_write_symbols OWN))as[replayed[REPLAYED SOURCE]].
  assert(IDENTICAL:replayed=original)
    by(apply placement_lift_injective;unfold placement_lift;congruence);subst replayed.
  destruct(placement_transfer_source_suffix _ _ _ _ _ _ _ current_write_symbols OWN SOURCE EMITTED MEMBER)
    as[prefix[suffix[ORDER PURE]]].
  split;[exact PRESERVED|]. exists error,(map placement_lift prefix),(map placement_lift suffix).
  split.
  - rewrite EVENTS,ORDER,map_app;reflexivity.
  - rewrite Forall_forall in PURE|-*;intros selected SELECTED.
    apply in_map_iff in SELECTED as[item[BOUND MEMBER']];subst selected.
    rewrite(PURE item MEMBER');reflexivity.
Qed.
