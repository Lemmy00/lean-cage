(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.acceptance: Construct useful admission with actual owned local storage. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Ctypes Ctypesdefs Clight.
Require Import IO Machine ClightSteps StoreSteps ErrorNumber WriteAll WriteMemory FreshMemory ReceiverAllocation.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffWitness.
From EntryProcess Require Import ProcessMachine ProcessAllocation ProcessStructure ProcessReturns
  ProcessPaths ProcessWait ProcessStatus ProcessAdmissionWait ProcessAdmissionFormat ProcessNumeric
  ProcessNumericWitness ProcessWriteWitness ProcessPlacement ProcessAdmissionTail ProcessAdmissionNumeric
  ProcessContexts.
From LeanCageMainNumber Require Import NumberMath NumberMemory NumberStorage.
Import ListNotations.
Open Scope Z_scope.
Local Opaque admission_ge.

Lemma admission_allocated_errno cell before locals after error :
  initialized_errno cell before error ->admission_allocations before locals after ->
  initialized_errno cell after error.
Proof.
  intros[LOW[HIGH[ACCESS LOAD]]]ALLOC.
  pose proof(local_allocations_unchanged _ _ _ ALLOC(fun _ _=>True))as OLD.
  unfold initialized_errno;split;[exact LOW|]. split;[exact HIGH|]. split.
  - destruct ACCESS as[RANGE ALIGN];split;[|exact ALIGN].
    intros position BOUND;eapply Mem.perm_unchanged_on;[exact OLD|exact I|apply RANGE;exact BOUND].
  - eapply Mem.load_unchanged_on;[exact OLD|intros;exact I|exact LOAD].
Qed.

Lemma admission_useful_status_store cell before locals allocated status error :
  initialized_errno cell before error ->Mem.valid_access before Mint32 status 0 Writable ->
  status<>tls_block cell ->admission_allocations before locals allocated ->
  exists stopped,
    process_wait_effect cell status Ptrofs.zero allocated(wait_status(Int.repr 2)(Int.repr 4991))stopped /\
    initialized_errno cell stopped error /\
    Mem.loadv Mint32 stopped(Vptr status Ptrofs.zero)=Some(Vint(Int.repr 4991)) /\
    (forall object position kind permission,
      Mem.perm stopped object position kind permission<->Mem.perm allocated object position kind permission).
Proof.
  intros ERRNO ACCESS SEPARATE ALLOC.
  assert(ACCESS':Mem.valid_access allocated Mint32 status 0 Writable).
  { destruct ACCESS as[RANGE ALIGN];split;[|exact ALIGN].
    intros position BOUND;eapply local_allocations_perms;[exact ALLOC|apply RANGE;exact BOUND]. }
  destruct(Mem.valid_access_store _ _ _ _(Vint(Int.repr 4991))ACCESS')as[stopped STORE].
  pose proof(admission_allocated_errno _ _ _ _ _ ERRNO ALLOC)as[LOW[HIGH[ERR_ACCESS ERR_LOAD]]].
  assert(READY:initialized_errno cell stopped error).
  { unfold initialized_errno;split;[exact LOW|]. split;[exact HIGH|]. split.
    - eapply Mem.store_valid_access_1;eassumption.
    - erewrite Mem.load_store_other;[exact ERR_LOAD|exact STORE|left;congruence]. }
  assert(STOREV:Mem.storev Mint32 allocated(Vptr status Ptrofs.zero)(Vint(Int.repr 4991))=Some stopped).
  { unfold Mem.storev;change(Ptrofs.unsigned Ptrofs.zero)with 0;exact STORE. }
  exists stopped;split.
  - eapply process_wait_status with(written:=stopped)(error:=None).
    + change(1<=2<=2147483647);lia.
    + exact STOREV.
    + constructor.
  - split;[exact READY|]. split.
    + unfold Mem.loadv;change(Ptrofs.unsigned Ptrofs.zero)with 0.
      destruct(zle (0+size_chunk Mint32) Ptrofs.modulus)as[BOUND|OUTSIDE].
      * erewrite Mem.load_store_same by exact STORE;reflexivity.
      * change(0+4>18446744073709551616)in OUTSIDE;lia.
    + intros object position kind permission;split;
        [eapply Mem.perm_store_2|eapply Mem.perm_store_1];eassumption.
Qed.

Lemma admission_useful_local_free locals memory :
  admission_text locals<>admission_encoded locals ->
  Mem.range_perm memory(admission_text locals)0 32 Cur Freeable ->
  Mem.range_perm memory(admission_encoded locals)0 8 Cur Freeable ->
  exists after,Mem.free_list memory(blocks_of_env admission_ge(admission_env locals))=Some after.
Proof.
  intros SEPARATE TEXT ENCODED.
  destruct(Mem.range_perm_free _ _ _ _ ENCODED)as[middle FREE_ENCODED].
  assert(TEXT':Mem.range_perm middle(admission_text locals)0 32 Cur Freeable).
  { intros position BOUND;eapply Mem.perm_free_1;[exact FREE_ENCODED|left;exact SEPARATE|apply TEXT;exact BOUND]. }
  destruct(Mem.range_perm_free _ _ _ _ TEXT')as[after FREE_TEXT].
  exists after.
  change(match Mem.free memory(admission_encoded locals)0 8 with
    Some next=>match Mem.free next(admission_text locals)0 32 with
      Some final=>Some final|None=>None end|None=>None end=Some after).
  rewrite FREE_ENCODED,FREE_TEXT;reflexivity.
Qed.

Definition admission_old_locations cell base status object (_position:Z):=
  Mem.valid_block base object /\object<>status /\object<>tls_block cell.

Lemma admission_useful_wait_frame cell status before observation after:
  process_wait_effect cell status Ptrofs.zero before observation after ->
  Mem.unchanged_on(fun object _=>object<>status /\object<>tls_block cell)before after.
Proof.
  intro EFFECT;inversion EFFECT;subst.
  - eapply Mem.store_unchanged_on;[eassumption|]. intros position RANGE[STATUS TLS];cbn in *;congruence.
  - match goal with STORE:Mem.storev _ _ _ _=Some _|-_=>
      change(Mem.store Mint32 before status 0(Vint word)=Some written)in STORE end.
    eapply Mem.unchanged_on_trans.
    + eapply Mem.store_unchanged_on;[eassumption|]. intros position RANGE[STATUS TLS];cbn in *;congruence.
    + match goal with ERRNO:errno_change _ _ _ _|-_=>inversion ERRNO;subst end.
      * apply Mem.unchanged_on_refl.
      * eapply Mem.store_unchanged_on;[eassumption|]. intros position RANGE[STATUS TLS];cbn in *;congruence.
Qed.

Lemma admission_useful_free_frame base locals memory after:
  ~Mem.valid_block base(admission_text locals) ->~Mem.valid_block base(admission_encoded locals) ->
  Mem.free_list memory(blocks_of_env admission_ge(admission_env locals))=Some after ->
  Mem.unchanged_on(fun object _=>Mem.valid_block base object)memory after.
Proof.
  intros TEXT_FRESH ENCODED_FRESH FREE.
  change(match Mem.free memory(admission_encoded locals)0 8 with
    Some next=>match Mem.free next(admission_text locals)0 32 with
      Some final=>Some final|None=>None end|None=>None end=Some after)in FREE.
  destruct(Mem.free memory(admission_encoded locals)0 8)as[middle|]eqn:ENCODED;[|discriminate].
  destruct(Mem.free middle(admission_text locals)0 32)as[final|]eqn:TEXT;inversion FREE;subst final.
  eapply Mem.unchanged_on_trans.
  - eapply Mem.free_unchanged_on;[exact ENCODED|]. intros position RANGE VALID;contradiction.
  - eapply Mem.free_unchanged_on;[exact TEXT|]. intros position RANGE VALID;contradiction.
Qed.

Theorem admission_useful_source_execution_owned cell before cgroup status error :
  initialized_errno cell before error ->Mem.valid_access before Mint32 status 0 Writable ->
  status<>tls_block cell ->
  exists locals first second after,
    process_steps admission_ge cell
      (live(Callstate(Internal f_admit_child)[Vint(Int.repr 2);Vint cgroup;Vptr status Ptrofs.zero]Kstop before))
      (repeat process_source_event 5++
        process_waited(Int.repr 2)status Ptrofs.zero Int.zero(wait_status(Int.repr 2)(Int.repr 4991))::
        (repeat process_source_event 29++
          process_entry(entry_formatted(admission_text locals)Ptrofs.zero(Int64.repr 2)Int.one)::
          (repeat process_source_event first++
            placement_lift(io_step(admission_write_request cell locals cgroup Int.one)
              (transfer[Byte.repr 50]None))::
            (repeat process_source_event second++
              process_traced(Int.repr 16896)(Int.repr 2)(Vlong Int64.zero)
                (Vlong(Int64.repr 1048592))Int64.zero::repeat process_source_event 5))))
      (live(Returnstate(Vint Int.zero)Kstop after)) /\
    initialized_errno cell after error /\
    Mem.unchanged_on(admission_old_locations cell before status)before after /\
    (forall object position kind permission,Mem.perm before object position kind permission ->
      Mem.perm after object position kind permission).
Proof.
  intros ERRNO ACCESS SEPARATE.
  destruct(admission_allocate before)as[locals[allocated[ALLOC OBJECTS]]].
  destruct(admission_allocation_objects _ _ _ OBJECTS)as[OLD[DISTINCT PERMS]].
  assert(READY:entry_errno_ready cell before)by(exists error;exact ERRNO).
  destruct(admission_fresh_storage _ _ _ _ READY OBJECTS)
    as[TEXT_ENCODED[TEXT_TLS[ENCODED_TLS OUTPUT]]].
  inversion PERMS as[|text rest[TEXT_FRESH TEXT_FREE]MORE];subst.
  inversion MORE as[|encoded none[ENCODED_FRESH ENCODED_FREE]NIL];subst;cbn in TEXT_FREE,ENCODED_FREE.
  destruct(admission_useful_status_store _ _ _ _ _ _ ERRNO ACCESS SEPARATE OBJECTS)
    as[stopped[WAIT_EFFECT[STOPPED_ERRNO[STATUS_LOAD STATUS_PERMS]]]].
  assert(FORMAT_OWN:entry_format_owned stopped(admission_text locals)Ptrofs.zero).
  { split;[change(0+32<=18446744073709551616);lia|].
    intros position BOUND;apply(STATUS_PERMS _ _ _ _).
    eapply Mem.perm_implies;[apply TEXT_FREE;exact BOUND|constructor]. }
  destruct(handoff_format_bytes_witness cell stopped(admission_text locals)Ptrofs.zero error
    [Byte.repr 50]FORMAT_OWN STOPPED_ERRNO TEXT_TLS ltac:(cbn;lia)
    ltac:(constructor;[vm_compute;discriminate|constructor]))
    as[formatted[FORMAT_STORE[INPUT[FORMATTED_ERRNO FORMAT_RESULT]]]].
  change(Int.repr(Z.of_nat(length[Byte.repr 50])))with Int.one in FORMAT_RESULT.
  set(parameters:=admission_parameters(Int.repr 2)cgroup(Vptr status Ptrofs.zero)).
  set(stopped_parameters:=admission_stopped_parameters parameters(Int.repr 2)(Int.repr 4991)).
  set(formatted_parameters:=admission_format_returned stopped_parameters Int.one).
  assert(CHILD:formatted_parameters!_child=Some(Vint(Int.repr 2))).
  { unfold formatted_parameters,stopped_parameters,admission_format_returned,
      admission_stopped_parameters,admission_stopsig_env,admission_stopped_env,admission_wait_return_env,
      parameters,admission_parameters;WriteAll.lookup. }
  assert(COUNT:formatted_parameters!_pidlength=Some(Vint Int.one)).
  { unfold formatted_parameters,admission_format_returned;apply PTree.gss. }
  assert(OUTPUT_FORMATTED:number_output formatted(admission_encoded locals)Ptrofs.zero).
  { eapply admission_format_preserves_output;[|exact FORMAT_RESULT].
    destruct OUTPUT as[BOUND[RANGE ALIGN]];split;[exact BOUND|]. split;[|exact ALIGN].
    intros position INTERVAL;apply(STATUS_PERMS _ _ _ _);apply RANGE;exact INTERVAL. }
  destruct(admission_useful_numeric_source locals formatted formatted_parameters Kstop
    CHILD COUNT INPUT OUTPUT_FORMATTED TEXT_ENCODED)
    as[numeric_count[numbered[NUMBER[NUMBER_INPUT NUMERIC]]]].
  assert(NUMERIC_ERRNO:initialized_errno cell numbered error).
  { destruct FORMATTED_ERRNO as[LOW[HIGH[TLS_ACCESS TLS_LOAD]]].
    unfold number_post,Mem.storev in NUMBER.
    destruct(zle _ _);[|discriminate].
    unfold initialized_errno;split;[exact LOW|]. split;[exact HIGH|]. split.
    - eapply Mem.store_valid_access_1;eassumption.
    - erewrite Mem.load_store_other;[exact TLS_LOAD|exact NUMBER|left;congruence]. }
  set(q:=admission_write_request cell locals cgroup Int.one).
  assert(WRITE_OWN:write_owned q[Byte.repr 50]numbered).
  { unfold q;eapply admission_write_owned;
      [exact NUMBER_INPUT|reflexivity|change(1<=1<=31);lia|exact NUMERIC_ERRNO|exact TEXT_TLS]. }
  destruct(current_write_useful_full_execution q[Byte.repr 50]numbered WRITE_OWN ltac:(discriminate))
    as[write_first[write_last WRITE]].
  assert(FREE_TEXT:Mem.range_perm numbered(admission_text locals)0 32 Cur Freeable).
  { unfold number_post,Mem.storev in NUMBER;destruct(zle _ _);[|discriminate].
    intros position BOUND;eapply Mem.perm_store_1;[exact NUMBER|].
    apply(entry_format_permissions _ _ _ _ _ _ FORMAT_RESULT);apply(STATUS_PERMS _ _ _ _);apply TEXT_FREE;exact BOUND. }
  assert(FREE_ENCODED:Mem.range_perm numbered(admission_encoded locals)0 8 Cur Freeable).
  { unfold number_post,Mem.storev in NUMBER;destruct(zle _ _);[|discriminate].
    intros position BOUND;eapply Mem.perm_store_1;[exact NUMBER|].
    apply(entry_format_permissions _ _ _ _ _ _ FORMAT_RESULT);apply(STATUS_PERMS _ _ _ _);apply ENCODED_FREE;exact BOUND. }
  destruct(admission_useful_local_free _ _ TEXT_ENCODED FREE_TEXT FREE_ENCODED)as[after FREE].
  set(numeric_parameters:=admission_useful_numeric_env formatted_parameters).
  assert(CHILD_NUMBERED:numeric_parameters!_child=Some(Vint(Int.repr 2))).
  { unfold numeric_parameters,admission_useful_numeric_env;repeat rewrite PTree.gso by discriminate;exact CHILD. }
  assert(CGROUP_NUMBERED:numeric_parameters!_cgfd=Some(Vint cgroup)).
  { unfold numeric_parameters,admission_useful_numeric_env,formatted_parameters,stopped_parameters,
      admission_format_returned,admission_stopped_parameters,admission_stopsig_env,admission_stopped_env,
      admission_wait_return_env,parameters,admission_parameters;WriteAll.lookup. }
  assert(COUNT_NUMBERED:numeric_parameters!_pidlength=Some(Vint Int.one)).
  { unfold numeric_parameters,admission_useful_numeric_env;repeat rewrite PTree.gso by discriminate;exact COUNT. }
  assert(PLUGGED:process_steps admission_ge cell
    (live(Callstate(Internal f_write_all)
      [Vint cgroup;Vptr(admission_text locals)Ptrofs.zero;Vlong(Int64.repr 1)]
      (admission_placement_cont locals numeric_parameters)numbered))
    (repeat process_source_event write_first++placement_lift(io_step q(transfer[Byte.repr 50]None))::
      repeat process_source_event write_last)
    (live(Returnstate(Vint Int.zero)(admission_placement_cont locals numeric_parameters)numbered))).
  { pose proof(plug_process_steps admission_ge(cell_of q)_ _ _
      (admission_placement_cont locals numeric_parameters)ltac:(exact I)WRITE)as RUN.
    unfold q in RUN;rewrite admission_request_cell in RUN;exact RUN. }
  assert(FREE_FRAME:Mem.unchanged_on(fun object _=>Mem.valid_block before object)numbered after).
  { eapply admission_useful_free_frame;eassumption. }
  assert(TLS_VALID:Mem.valid_block before(tls_block cell)).
  { destruct ERRNO as[LOW[HIGH[ACCESS' LOAD]]];eapply Mem.valid_access_valid_block;
      eapply Mem.valid_access_implies;[exact ACCESS'|constructor]. }
  assert(FINAL_ERRNO:initialized_errno cell after error).
  { destruct NUMERIC_ERRNO as[LOW[HIGH[[PERMISSION ALIGN]LOAD]]].
    unfold initialized_errno;split;[exact LOW|]. split;[exact HIGH|]. split.
    - split;[intros position RANGE;eapply Mem.perm_unchanged_on;
        [exact FREE_FRAME|exact TLS_VALID|apply PERMISSION;exact RANGE]|exact ALIGN].
    - eapply Mem.load_unchanged_on;[exact FREE_FRAME|intros;exact TLS_VALID|exact LOAD]. }
  assert(FINAL_FRAME:Mem.unchanged_on(admission_old_locations cell before status)before after).
  { eapply Mem.unchanged_on_trans with(m2:=allocated).
    - eapply local_allocations_unchanged;exact OBJECTS.
    - eapply Mem.unchanged_on_trans with(m2:=stopped).
      + eapply Mem.unchanged_on_implies;[eapply admission_useful_wait_frame;exact WAIT_EFFECT|].
        intros object position[VALID[STATUS TLS]]CURRENT;auto.
      + eapply Mem.unchanged_on_trans with(m2:=formatted).
        * eapply Mem.storebytes_unchanged_on;[exact FORMAT_STORE|].
          intros position RANGE[VALID[STATUS TLS]];contradiction.
        * eapply Mem.unchanged_on_trans with(m2:=numbered).
          -- unfold number_post,Mem.storev in NUMBER;destruct(zle _ _);[|discriminate].
             eapply Mem.store_unchanged_on;[exact NUMBER|].
             intros position RANGE[VALID[STATUS TLS]];contradiction.
          -- eapply Mem.unchanged_on_implies;[exact FREE_FRAME|].
             intros object position[VALID[STATUS TLS]]CURRENT;exact VALID. }
  assert(FINAL_PERMISSIONS:forall object position kind permission,
    Mem.perm before object position kind permission ->Mem.perm after object position kind permission).
  { intros object position kind permission PERMISSION.
    eapply Mem.perm_unchanged_on;[exact FREE_FRAME|eapply Mem.perm_valid_block;exact PERMISSION|].
    unfold number_post,Mem.storev in NUMBER;destruct(zle _ _);[|discriminate].
    eapply Mem.perm_store_1;[exact NUMBER|].
    apply(entry_format_permissions _ _ _ _ _ _ FORMAT_RESULT);apply(STATUS_PERMS _ _ _ _).
    eapply local_allocations_perms;[exact OBJECTS|exact PERMISSION]. }
  exists locals,(4+numeric_count+3+write_first)%nat,(write_last+7)%nat,after.
  split;[|split;[exact FINAL_ERRNO|split;[exact FINAL_FRAME|exact FINAL_PERMISSIONS]]].
  replace(repeat process_source_event 29)with
    (repeat process_source_event 26++repeat process_source_event 3)
    by(rewrite <-repeat_app;reflexivity).
  rewrite !repeat_app;repeat rewrite <-app_assoc.
  eapply process_steps_append.
  - eapply process_store_path_actual;apply admission_start_to_wait;exact ALLOC.
  - econstructor.
    + apply process_wait_step;[exact WAIT_EFFECT|exists error;exact STOPPED_ERRNO].
    + eapply process_steps_append.
      * eapply process_store_path_actual.
        apply(admission_matching_stop_source locals parameters stopped(Int.repr 2)status Ptrofs.zero(Int.repr 4991)).
        -- change(1<=2);lia.
        -- unfold parameters,admission_parameters;WriteAll.lookup.
        -- unfold parameters,admission_parameters;WriteAll.lookup.
        -- exact STATUS_LOAD.
        -- vm_compute;reflexivity.
        -- vm_compute;reflexivity.
      * eapply process_steps_append.
        -- eapply process_store_path_actual;apply admission_format_call_source.
           unfold stopped_parameters,admission_stopped_parameters,admission_stopsig_env,
             admission_stopped_env,admission_wait_return_env,parameters,admission_parameters;WriteAll.lookup.
        -- econstructor.
           ++ apply process_entry_step,entry_format_step;[exact FORMAT_OWN|exact FORMAT_RESULT].
           ++ eapply process_steps_append.
              ** eapply process_store_path_actual;apply admission_format_return_source.
              ** eapply process_steps_append.
                 --- eapply process_store_path_actual;exact NUMERIC.
                 --- eapply process_steps_append.
                     +++ eapply process_store_path_actual;apply admission_tail_write_source;
                           [exact CGROUP_NUMBERED|exact COUNT_NUMBERED].
                     +++ match goal with |-process_steps _ _ _ ?events _=>
                           replace events with
                             ((repeat process_source_event write_first++
                               placement_lift(io_step q(transfer[Byte.repr 50]None))::
                               repeat process_source_event write_last)++
                              (repeat process_source_event 7++
                                process_traced(Int.repr 16896)(Int.repr 2)(Vlong Int64.zero)
                                  (Vlong(Int64.repr 1048592))Int64.zero::repeat process_source_event 5))
                             by(repeat rewrite <-app_assoc;reflexivity) end.
                         eapply process_steps_append;[exact PLUGGED|].
                         eapply process_steps_append.
                         *** eapply process_store_path_actual;apply admission_write_to_options_source;exact CHILD_NUMBERED.
                         *** econstructor.
                             ---- apply process_ptrace_step.
                                  ++++ unfold process_ptrace_frame;cbn;apply Mem.unchanged_on_refl.
                                  ++++ exists error;exact NUMERIC_ERRNO.
                             ---- replace(repeat process_source_event 5)with
                                    (repeat process_source_event 3++repeat process_source_event 2)
                                    by(rewrite <-repeat_app;reflexivity).
                                  eapply process_steps_append.
                                  ++++ eapply process_store_path_actual.
                                       pose proof(admission_options_return_source locals
                                         (PTree.set _t'6(Vint Int.zero)numeric_parameters)numbered Int64.zero
                                         (Kseq admission_return Kstop))as RETURN.
                                       change(Int64.eq Int64.zero Int64.zero)with true in RETURN;exact RETURN.
                                  ++++ eapply process_store_path_actual with(P:=fun _=>True).
                                       admission_route;apply admission_finish_path;exact FREE.
Qed.

Theorem admission_useful_source_execution cell before cgroup status error :
  initialized_errno cell before error ->Mem.valid_access before Mint32 status 0 Writable ->
  status<>tls_block cell ->
  exists locals first second after,
    process_steps admission_ge cell
      (live(Callstate(Internal f_admit_child)[Vint(Int.repr 2);Vint cgroup;Vptr status Ptrofs.zero]Kstop before))
      (repeat process_source_event 5++
        process_waited(Int.repr 2)status Ptrofs.zero Int.zero(wait_status(Int.repr 2)(Int.repr 4991))::
        (repeat process_source_event 29++
          process_entry(entry_formatted(admission_text locals)Ptrofs.zero(Int64.repr 2)Int.one)::
          (repeat process_source_event first++
            placement_lift(io_step(admission_write_request cell locals cgroup Int.one)
              (transfer[Byte.repr 50]None))::
            (repeat process_source_event second++
              process_traced(Int.repr 16896)(Int.repr 2)(Vlong Int64.zero)
                (Vlong(Int64.repr 1048592))Int64.zero::repeat process_source_event 5))))
      (live(Returnstate(Vint Int.zero)Kstop after)).
Proof.
  intros ERRNO STATUS SEPARATE.
  destruct(admission_useful_source_execution_owned cell before cgroup status error ERRNO STATUS SEPARATE)
    as[locals[first[second[after[RUN REST]]]]].
  exists locals,first,second,after;exact RUN.
Qed.
