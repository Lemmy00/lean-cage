(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Actual clock source retains per-operation physical state. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine StoreSteps ClightSteps.
From HostGateway Require Import GatewaySource GatewayMachine GatewayClock GatewayClockRuntime
  GatewayThreadRuntime GatewayStreamInterface GatewayLocalRuntime GatewayLocalWorld GatewayReadonly
  GatewayRuntimeCuts GatewayContexts GatewayRuntime GatewayOperations GatewayFrames GatewayPrimitiveCalls.
Import ListNotations.
Open Scope Z_scope.

Section ClockWorld.
Context {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)(io:Event->option gateway_native_io)
    (native_private:World->block->Prop)(stable_readonly:World->block->Z->Prop)
    (discipline:option val->mem->World->Prop)(thread_errno:World->int).
Context(runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).
Variable state:World->Prop.
Hypothesis STATE_AMBIENT:forall before world after next,
  discipline None before world->state world->gateway_interference backend before world after next->state next.
Hypothesis STATE_CLOCK:forall before world sample result after next observed,
  state world->gateway_runtime_operation backend clock_gettime_definition[Vint Int.one;Vptr sample Ptrofs.zero]
    before world result after next observed->state next.

Definition gateway_clock_world_ready sample memory world:Prop:=
  clock_sample_ready native_private discipline sample memory world /\state world.

Lemma gateway_clock_world_ambient sample:gateway_runtime_discipline backend(gateway_clock_world_ready sample).
Proof.
  intros before world after next[SAMPLE STATE]INTERFERENCE;split.
  - eapply clock_sample_ready_discipline;[exact runtime|exact SAMPLE|exact INTERFERENCE].
  - eapply STATE_AMBIENT;[exact(proj1 SAMPLE)|exact STATE|exact INTERFERENCE].
Qed.

Theorem actual_clock_world_call before world events returned after next symbol:
  sizeof(genv_cenv ge)clock_sample_type=16->
  Genv.find_symbol ge _clock_gettime=Some symbol->
  Genv.find_funct_ptr ge symbol=Some clock_gettime_definition->
  discipline None before world->state world->
  gateway_steps backend ge(gateway_live(Callstate(Internal f_host_now)[]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next)->
  exists prefix suffix sample memory current,
    events=prefix++suffix /\gateway_clock_world_ready sample memory current /\
    gateway_steps backend ge(gateway_live(Callstate(Internal f_host_now)[]Kstop before)world)prefix
      (gateway_live(Callstate clock_gettime_definition[Vint Int.one;Vptr sample Ptrofs.zero]
        (clock_api_cont sample Kstop)memory)current) /\
    gateway_steps backend ge
      (gateway_live(Callstate clock_gettime_definition[Vint Int.one;Vptr sample Ptrofs.zero]
        (clock_api_cont sample Kstop)memory)current)suffix(gateway_live(Returnstate returned Kstop after)next).
Proof.
  intros SIZE SYMBOL FUNCTION SIDE STATE RUN.
  set(ready:=fun memory world=>discipline None memory world /\state world).
  assert(AMBIENT:gateway_runtime_discipline backend ready).
  { intros first current changed later[HELD OBSERVED]INTERFERENCE;split.
    - exact(proj1(gateway_thread_ambient _ _ _ _ _ _ runtime None _ _ _ _ HELD INTERFERENCE)).
    - eapply STATE_AMBIENT;eassumption. }
  destruct(gateway_actual_function_entry_side backend ge ready AMBIENT f_host_now[]Kstop
    before world events returned Kstop after next(conj SIDE STATE)RUN)
    as(entry_prefix&body_events&allocation_before&allocation_world&environment&temporaries&allocated&
      EVENTS&QUIET&PREFIX&ENTRY_CONTEXT&ENTRY&BODY).
  destruct(clock_actual_entry_canonical ge allocation_before environment temporaries allocated ENTRY)
    as(sample&ENV&TEMPS&ALLOC&FRESH&PERMISSION&FRAME);subst environment temporaries.
  assert(ALLOCATED:gateway_clock_world_ready sample allocated allocation_world).
  { split;[|exact(proj2 ENTRY_CONTEXT)]. split.
    - eapply gateway_thread_native_alloc;[exact runtime|exact(proj1 ENTRY_CONTEXT)|exact ALLOC].
    - split.
      + eapply gateway_thread_fresh_native;[exact runtime|exact(proj1 ENTRY_CONTEXT)|exact FRESH].
      + rewrite SIZE in PERMISSION;exact PERMISSION. }
  destruct(gateway_retained_call_ready_cut backend ge(gateway_clock_world_ready sample)
    (gateway_clock_world_ambient sample)clock_gettime_definition[Vint Int.one;Vptr sample Ptrofs.zero]
    (clock_api_cont sample Kstop)
    (State f_host_now(fn_body f_host_now)Kstop(clock_environment sample)clock_temporaries allocated)
    allocation_world body_events returned after next
    (clock_body_first_call_retained ge sample allocated Kstop symbol SYMBOL FUNCTION)ALLOCATED BODY)
    as(body_prefix&suffix&memory&current&BODY_EVENTS&BODY_QUIET&CALL&CALLED&REST).
  exists(entry_prefix++gateway_source E0::body_prefix),suffix,sample,memory,current.
  split;[rewrite EVENTS,BODY_EVENTS;rewrite <-app_assoc;reflexivity|]. split;[exact CALLED|].
  split;[|exact REST]. eapply gateway_steps_append;[exact PREFIX|].
  econstructor;[apply gateway_internal;[exact I|apply step_internal_function;exact ENTRY]|exact CALL].
Qed.

Theorem actual_clock_world_api sample before world events returned after next:
  gateway_clock_world_ready sample before world->
  gateway_steps backend ge
    (gateway_live(Callstate clock_gettime_definition[Vint Int.one;Vptr sample Ptrofs.zero]Kstop before)world)
    events(gateway_live(Returnstate returned Kstop after)next)->
  exists status,returned=Vint status /\gateway_clock_world_ready sample after next.
Proof.
  intros READY RUN.
  destruct(gateway_external_operation_of_run backend ge _ _ _ _ _ before world events returned after next RUN)
    as(pending&suffix&memory&called&changed&primitive&observed&EVENTS&PENDING&PREFIX&OPERATION&REST).
  assert(CALLED:gateway_clock_world_ready sample memory called).
  { eapply gateway_pending_run_ready with
      (source:=Callstate clock_gettime_definition[Vint Int.one;Vptr sample Ptrofs.zero]Kstop before);
      [apply gateway_clock_world_ambient|exact READY|exact PENDING|exact PREFIX]. }
  destruct CALLED as[SAMPLE STATE].
  destruct(gateway_clock_operation _ _ _ _ _ _ runtime _ _ _ _ _ _ _ _(proj1 SAMPLE)(proj1(proj2 SAMPLE))
    (clock_sample_ready_pointer native_private discipline sample memory called SAMPLE)OPERATION)
    as(status&VALUE&VALUES&SIDE&ACCESS&PERMISSIONS&FRAME&IO);subst returned.
  assert(AFTER:gateway_clock_world_ready sample changed primitive).
  { split;[|exact(STATE_CLOCK memory called sample(Vint status)changed primitive observed STATE OPERATION)].
    split;[exact SIDE|]. split.
    - apply(proj1 ACCESS);[eapply clock_sample_ready_valid;exact SAMPLE|exact(proj1(proj2 SAMPLE))].
    - intros position RANGE;apply(proj1(PERMISSIONS position Cur Freeable ltac:(cbn;exact RANGE))).
      apply(proj2(proj2 SAMPLE));exact RANGE. }
  exists status;split;[reflexivity|].
  eapply gateway_readonly_run_side with(source:=Returnstate(Vint status)Kstop changed);
    [apply gateway_clock_world_ambient|exact I|exact AFTER|exact REST].
Qed.

Theorem actual_clock_world_after_api sample status before world events returned after next:
  gateway_clock_world_ready sample before world->
  gateway_steps backend ge
    (gateway_live(Returnstate(Vint status)(clock_api_cont sample Kstop)before)world)events
    (gateway_live(Returnstate returned Kstop after)next)->discipline None after next /\state next.
Proof.
  intros READY RUN.
  destruct(gateway_uniform_edge_side_cut backend ge(gateway_clock_world_ready sample)
    (gateway_clock_world_ambient sample)
    (Returnstate(Vint status)(clock_api_cont sample Kstop)before)
    (State f_host_now Sskip clock_return_cont(clock_environment sample)(clock_returned_temporaries status)before)
    before world events returned after next ltac:(cbn;tauto)
    ltac:(intro memory;apply unchanged_store_edge,edge_returnstate)READY RUN)
    as(pending&rest&memory&current&EVENTS&AMBIENT&PREFIX&CALLED&SUFFIX).
  destruct(gateway_local_world_return backend ge io native_private stable_readonly discipline thread_errno runtime
    state STATE_AMBIENT
    (State f_host_now Sskip clock_return_cont(clock_environment sample)(clock_returned_temporaries status)memory)
    current rest returned after next)
    as[SIDE[NEXT EMPTY]].
  - cbn[gateway_local_readonly_source gateway_readonly_statement];split;[reflexivity|].
    split;[exact actual_clock_after_api_readonly|]. eapply clock_ready_environment;exact(proj1 CALLED).
  - exact(proj1(proj1 CALLED)).
  - exact(proj2 CALLED).
  - exact SUFFIX.
  - split;assumption.
Qed.

Theorem actual_clock_world_complete before world events returned after next symbol:
  sizeof(genv_cenv ge)clock_sample_type=16->
  Genv.find_symbol ge _clock_gettime=Some symbol->
  Genv.find_funct_ptr ge symbol=Some clock_gettime_definition->
  discipline None before world->state world->
  gateway_steps backend ge(gateway_live(Callstate(Internal f_host_now)[]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next)->discipline None after next /\state next.
Proof.
  intros SIZE SYMBOL FUNCTION SIDE STATE RUN.
  destruct(actual_clock_world_call before world events returned after next symbol SIZE SYMBOL FUNCTION SIDE STATE RUN)
    as(prefix&suffix&sample&memory&current&EVENTS&CALLED&PREFIX&SUFFIX).
  destruct(gateway_return_cut backend ge clock_gettime_definition[Vint Int.one;Vptr sample Ptrofs.zero]
    (clock_api_cont sample Kstop)memory current suffix(Returnstate returned Kstop after)next ltac:(reflexivity)
    ltac:(cbn[clock_api_cont gateway_continuation gateway_cont_weight];lia)SUFFIX)
    as(api_events&caller_events&value&changed&changed_world&SUFFIX_EVENTS&API&CALLER).
  destruct(actual_clock_world_api sample memory current api_events value changed changed_world CALLED API)
    as[status[VALUE AFTER]];subst value.
  exact(actual_clock_world_after_api sample status changed changed_world caller_events returned after next AFTER CALLER).
Qed.
End ClockWorld.
