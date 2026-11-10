(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: The actual clock retains caller arrays at the same explicit
   thread mode. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine StoreSteps ClightSteps.
From HostGateway Require Import GatewaySource GatewayMachine GatewayClock GatewayClockRuntime
  GatewayCallerBuffers GatewayCallerReadonly GatewayThreadRuntime GatewayStreamInterface
  GatewayLocalRuntime GatewayScopedMemory GatewayReadonly GatewayRuntimeCuts GatewayContexts
  GatewayRuntime GatewayOperations GatewayFrames GatewayPrimitiveCalls GatewayGuardObservation GatewayTransferMath
  GatewayClockModeInterface GatewayClockModeRuntime GatewayCallerModeReadonly.
Import ListNotations.
Open Scope Z_scope.

Section CallerModeClock.
Context {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)(io:Event->option gateway_native_io)
    (native_private:World->block->Prop)(stable_readonly:World->block->Z->Prop)
    (discipline:option val->mem->World->Prop)(thread_errno:World->int).
Context(runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).
Context(mode:option val)(clock_operation:gateway_clock_mode_operation backend io native_private stable_readonly discipline mode).
Context(readonly:block->Z->Prop)(target:block)(reference:mem)(owner:World).
Local Definition scope:=gateway_caller_scope readonly target reference.
Local Definition history:=gateway_caller_buffers native_private stable_readonly readonly target reference owner.
Local Definition held:=gateway_mode_caller_readonly_ready native_private stable_readonly discipline mode readonly target reference owner.

Definition gateway_caller_mode_clock_ready sample memory world:Prop:=
  mode_clock_sample_ready native_private discipline mode sample memory world /\history memory world /\
  (forall position,~scope sample position).

Lemma gateway_caller_mode_clock_ambient sample:gateway_runtime_discipline backend(gateway_caller_mode_clock_ready sample).
Proof.
  intros before world after next[SAMPLE[HISTORY SEPARATE]]INTERFERENCE;split.
  - eapply mode_clock_sample_ready_discipline;[exact runtime|exact SAMPLE|exact INTERFERENCE].
  - split;[|exact SEPARATE].
    destruct(gateway_thread_ambient _ _ _ _ _ _ runtime mode before world after next(proj1 SAMPLE)INTERFERENCE)
      as[SIDE[ACCESS FRAME]]. eapply gateway_caller_buffers_no_output;eassumption.
Qed.

Lemma gateway_caller_mode_clock_allocated sample before world allocated:
  held before world->Mem.alloc before 0 16=(allocated,sample)->
  gateway_caller_mode_clock_ready sample allocated world.
Proof.
  intros[SIDE HISTORY]ALLOC.
  assert(FRESH:~Mem.valid_block before sample)by(eapply Mem.fresh_block_alloc;exact ALLOC).
  split.
  - split;[eapply gateway_thread_native_alloc;[exact runtime|exact SIDE|exact ALLOC]|]. split.
    + eapply gateway_thread_fresh_native;[exact runtime|exact SIDE|exact FRESH].
    + intros position RANGE;eapply Mem.perm_alloc_2;eassumption.
  - split;[eapply gateway_caller_buffers_alloc;eassumption|].
    intros position HERE;apply FRESH;exact(gateway_caller_scope_live _ _ _ _ _ _ _ _ HISTORY sample position HERE).
Qed.

Lemma gateway_caller_mode_clock_environment_avoids sample memory world:
  gateway_caller_mode_clock_ready sample memory world->
  gateway_environment_avoids scope(clock_environment sample).
Proof.
  intros[SAMPLE[HISTORY SEPARATE]]identifier object ty position LOOK.
  unfold clock_environment in LOOK;destruct(peq identifier _sample)as[SAME|DIFFERENT].
  - subst identifier;rewrite PTree.gss in LOOK;inversion LOOK;subst;exact(SEPARATE position).
  - rewrite PTree.gso in LOOK by exact DIFFERENT;rewrite PTree.gempty in LOOK;discriminate.
Qed.

Theorem actual_caller_mode_clock_call before world events returned after next symbol descriptor:
  sizeof(genv_cenv ge)clock_sample_type=16->
  Genv.find_symbol ge _clock_gettime=Some symbol->
  Genv.find_funct_ptr ge symbol=Some clock_gettime_definition->held before world->
  gateway_steps backend ge(gateway_live(Callstate(Internal f_host_now)[]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next)->
  exists prefix suffix sample memory current,
    events=prefix++suffix /\gateway_received_bytes io descriptor prefix=[] /\
    gateway_caller_mode_clock_ready sample memory current /\
    gateway_steps backend ge(gateway_live(Callstate(Internal f_host_now)[]Kstop before)world)prefix
      (gateway_live(Callstate clock_gettime_definition[Vint Int.one;Vptr sample Ptrofs.zero]
        (clock_api_cont sample Kstop)memory)current) /\
    gateway_steps backend ge
      (gateway_live(Callstate clock_gettime_definition[Vint Int.one;Vptr sample Ptrofs.zero]
        (clock_api_cont sample Kstop)memory)current)suffix(gateway_live(Returnstate returned Kstop after)next).
Proof.
  intros SIZE SYMBOL FUNCTION READY RUN.
  destruct(gateway_actual_function_entry_side backend ge held
    (gateway_mode_caller_readonly_ambient backend io native_private stable_readonly discipline thread_errno runtime mode
      readonly target reference owner)f_host_now[]Kstop before world events returned Kstop after next READY RUN)
    as(entry_prefix&body_events&allocation_before&allocation_world&environment&temporaries&allocated&
      EVENTS&QUIET&PREFIX&ENTRY_CONTEXT&ENTRY&BODY).
  destruct(clock_actual_entry_canonical ge allocation_before environment temporaries allocated ENTRY)
    as(sample&ENV&TEMPS&ALLOC&FRESH&PERMISSION&FRAME);subst environment temporaries.
  rewrite SIZE in ALLOC.
  pose proof(gateway_caller_mode_clock_allocated sample allocation_before allocation_world allocated ENTRY_CONTEXT ALLOC)as ALLOCATED.
  destruct(gateway_retained_call_ready_cut backend ge(gateway_caller_mode_clock_ready sample)
    (gateway_caller_mode_clock_ambient sample)clock_gettime_definition[Vint Int.one;Vptr sample Ptrofs.zero]
    (clock_api_cont sample Kstop)
    (State f_host_now(fn_body f_host_now)Kstop(clock_environment sample)clock_temporaries allocated)
    allocation_world body_events returned after next
    (clock_body_first_call_retained ge sample allocated Kstop symbol SYMBOL FUNCTION)ALLOCATED BODY)
    as(body_prefix&suffix&memory&current&BODY_EVENTS&BODY_QUIET&CALL&CALLED&REST).
  exists(entry_prefix++gateway_source E0::body_prefix),suffix,sample,memory,current.
  split;[rewrite EVENTS,BODY_EVENTS;rewrite <-app_assoc;reflexivity|]. split.
  - rewrite gateway_received_bytes_append,gateway_received_source_cons,
      (gateway_quiet_received_empty io descriptor entry_prefix QUIET),
      (gateway_quiet_received_empty io descriptor body_prefix BODY_QUIET);reflexivity.
  - split;[exact CALLED|]. split;[|exact REST]. eapply gateway_steps_append;[exact PREFIX|].
    econstructor;[apply gateway_internal;[exact I|apply step_internal_function;exact ENTRY]|exact CALL].
Qed.

Local Lemma caller_mode_clock_output_dec sample:
  forall object position,{gateway_native_region sample Ptrofs.zero 16 object position}+
    {~gateway_native_region sample Ptrofs.zero 16 object position}.
Proof.
  intros object position;unfold gateway_native_region;destruct(peq object sample)as[SAME|DIFFERENT];
    [subst object|right;tauto].
  destruct(Z_le_dec(Ptrofs.unsigned Ptrofs.zero)position)as[LOW|LOW];[|right;tauto].
  destruct(Z_lt_dec position(Ptrofs.unsigned Ptrofs.zero+16))as[HIGH|HIGH];[left;auto|right;tauto].
Qed.

Theorem caller_mode_clock_primitive sample before world returned after next observed:
  gateway_caller_mode_clock_ready sample before world->
  gateway_runtime_operation backend clock_gettime_definition[Vint Int.one;Vptr sample Ptrofs.zero]
    before world returned after next observed->
  exists status,returned=Vint status /\gateway_caller_mode_clock_ready sample after next /\io observed=None.
Proof.
  intros[SAMPLE[HISTORY SEPARATE]]OPERATION.
  destruct(clock_operation before world sample Ptrofs.zero returned after next observed
    (proj1 SAMPLE)(proj1(proj2 SAMPLE))
    (mode_clock_sample_ready_pointer native_private discipline mode sample before world SAMPLE)OPERATION)
    as(status&RETURNED&VALUES&SIDE&ACCESS&PERMISSIONS&FRAME&IO).
  exists status;split;[exact RETURNED|]. split;[|exact IO]. split.
  - split;[exact SIDE|]. split.
    + apply(proj1 ACCESS);[eapply mode_clock_sample_ready_valid;exact SAMPLE|exact(proj1(proj2 SAMPLE))].
    + intros position RANGE;apply(proj1(PERMISSIONS position Cur Freeable ltac:(cbn;exact RANGE))).
      apply(proj2(proj2 SAMPLE));exact RANGE.
  - split;[|exact SEPARATE].
    eapply gateway_caller_buffers_operation;
      [exact HISTORY|exact ACCESS|exact FRAME|apply caller_mode_clock_output_dec| | |].
    + intros object position HERE[SAME RANGE];subst object;apply(SEPARATE position);right;left;exact HERE.
    + intros position kind permission[SAME RANGE].
      exfalso;apply(SEPARATE position);left;symmetry;exact SAME.
    + intros object position READABLE[SAME RANGE];subst object.
      apply(proj1(PERMISSIONS position Cur Readable RANGE));exact READABLE.
Qed.

Theorem actual_caller_mode_clock_api sample before world events returned after next descriptor:
  gateway_caller_mode_clock_ready sample before world->
  gateway_steps backend ge
    (gateway_live(Callstate clock_gettime_definition[Vint Int.one;Vptr sample Ptrofs.zero]Kstop before)world)
    events(gateway_live(Returnstate returned Kstop after)next)->
  exists status,returned=Vint status /\gateway_caller_mode_clock_ready sample after next /\
    gateway_received_bytes io descriptor events=[].
Proof.
  intros READY RUN.
  destruct(gateway_external_operation_of_run backend ge _ _ _ _ _ before world events returned after next RUN)
    as(prefix&suffix&called&called_world&changed&changed_world&observed&
      EVENTS&PENDING&PREFIX&OPERATION&SUFFIX).
  assert(CALLED:gateway_caller_mode_clock_ready sample called called_world).
  { eapply gateway_pending_run_ready with
      (source:=Callstate clock_gettime_definition[Vint Int.one;Vptr sample Ptrofs.zero]Kstop before);
      [apply gateway_caller_mode_clock_ambient|exact READY|exact PENDING|exact PREFIX]. }
  destruct(caller_mode_clock_primitive sample called called_world returned changed changed_world observed CALLED OPERATION)
    as[status[RETURNED[CHANGED IO]]].
  exists status;split;[exact RETURNED|]. split.
  - eapply gateway_readonly_run_side with(source:=Returnstate returned Kstop changed);
      [apply gateway_caller_mode_clock_ambient|exact I|exact CHANGED|exact SUFFIX].
  - rewrite(gateway_external_received_projection backend ge io events returned after next prefix suffix
      changed changed_world observed descriptor EVENTS PENDING SUFFIX).
    unfold gateway_received_event;rewrite IO;reflexivity.
Qed.

Theorem actual_caller_mode_clock_after_api sample status before world events returned after next descriptor:
  gateway_caller_mode_clock_ready sample before world->
  gateway_steps backend ge
    (gateway_live(Returnstate(Vint status)(clock_api_cont sample Kstop)before)world)events
    (gateway_live(Returnstate returned Kstop after)next)->
  held after next /\gateway_received_bytes io descriptor events=[].
Proof.
  intros READY RUN.
  destruct(gateway_uniform_edge_side_cut backend ge(gateway_caller_mode_clock_ready sample)
    (gateway_caller_mode_clock_ambient sample)
    (Returnstate(Vint status)(clock_api_cont sample Kstop)before)
    (State f_host_now Sskip mode_clock_return_cont(clock_environment sample)(mode_clock_returned_temporaries status)before)
    before world events returned after next ltac:(cbn;tauto)
    ltac:(intro memory;apply unchanged_store_edge,edge_returnstate)READY RUN)
    as(pending&rest&memory&current&EVENTS&AMBIENT&PREFIX&CALLED&SUFFIX).
  assert(LOCAL:gateway_local_readonly_source native_private current
    (State f_host_now Sskip mode_clock_return_cont(clock_environment sample)(mode_clock_returned_temporaries status)memory)).
  { cbn[gateway_local_readonly_source gateway_readonly_statement];split;[reflexivity|].
    split;[exact mode_actual_clock_after_api_readonly|]. eapply mode_clock_ready_environment;exact(proj1 CALLED). }
  assert(SCOPED:gateway_scoped_readonly scope
    (State f_host_now Sskip mode_clock_return_cont(clock_environment sample)(mode_clock_returned_temporaries status)memory)).
  { cbn[gateway_scoped_readonly gateway_readonly_statement];split;[reflexivity|].
    split;[exact mode_actual_clock_after_api_readonly|]. eapply gateway_caller_mode_clock_environment_avoids;exact CALLED. }
  destruct(gateway_mode_caller_readonly_return backend ge io native_private stable_readonly discipline thread_errno runtime mode
    readonly target reference owner
    (State f_host_now Sskip mode_clock_return_cont(clock_environment sample)(mode_clock_returned_temporaries status)memory)
    current rest returned after next descriptor LOCAL SCOPED
    (conj(proj1(proj1 CALLED))(proj1(proj2 CALLED)))SUFFIX)as[FINAL EMPTY].
  split;[exact FINAL|]. rewrite EVENTS,gateway_received_bytes_append,gateway_received_source_cons.
  assert(PENDING_EMPTY:gateway_received_bytes io descriptor pending=[]).
  { apply gateway_quiet_received_empty;eapply Forall_impl;[|exact AMBIENT]. intros event SAME;right;exact SAME. }
  rewrite PENDING_EMPTY,EMPTY;reflexivity.
Qed.

Theorem actual_caller_mode_clock_complete before world events returned after next symbol descriptor:
  sizeof(genv_cenv ge)clock_sample_type=16->
  Genv.find_symbol ge _clock_gettime=Some symbol->
  Genv.find_funct_ptr ge symbol=Some clock_gettime_definition->held before world->
  gateway_steps backend ge(gateway_live(Callstate(Internal f_host_now)[]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next)->
  held after next /\gateway_received_bytes io descriptor events=[].
Proof.
  intros SIZE SYMBOL FUNCTION READY RUN.
  destruct(actual_caller_mode_clock_call before world events returned after next symbol descriptor SIZE SYMBOL FUNCTION READY RUN)
    as(prefix&suffix&sample&memory&current&EVENTS&EMPTY&CALLED&PREFIX&SUFFIX).
  destruct(gateway_return_cut backend ge clock_gettime_definition[Vint Int.one;Vptr sample Ptrofs.zero]
    (clock_api_cont sample Kstop)memory current suffix(Returnstate returned Kstop after)next ltac:(reflexivity)
    ltac:(cbn[clock_api_cont gateway_continuation gateway_cont_weight];lia)SUFFIX)
    as(api_events&caller_events&value&changed&changed_world&SUFFIX_EVENTS&API&CALLER).
  destruct(actual_caller_mode_clock_api sample memory current api_events value changed changed_world descriptor CALLED API)
    as[status[VALUE[AFTER API_EMPTY]]];subst value.
  destruct(actual_caller_mode_clock_after_api sample status changed changed_world caller_events returned after next descriptor AFTER CALLER)
    as[FINAL CALLER_EMPTY]. split;[exact FINAL|].
  rewrite EVENTS,SUFFIX_EVENTS,!gateway_received_bytes_append,EMPTY,API_EMPTY,CALLER_EMPTY;reflexivity.
Qed.
End CallerModeClock.
