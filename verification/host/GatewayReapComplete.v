(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual reap returns retain the caller's response and thread roots. *)
From Stdlib Require Import ZArith List Lia Wf_nat.
From compcert Require Import Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayThreadRuntime GatewayStreamInterface
  GatewayReapRuntime GatewayReapAllocation GatewayReapContext GatewayReapScope GatewayReapStructure GatewayReapState
  GatewayCallerBuffers GatewayCallerFamily GatewayClockModeInterface GatewayContexts GatewayTransferMath.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_actual_reap_body_complete {World Event}(backend:gateway_backend World Event)io observation native stable discipline thread_errno
    (thread:gateway_thread_runtime backend io native stable discipline thread_errno)
    (runtime:gateway_reap_runtime backend io observation native stable discipline thread_errno)saved
    (clock:gateway_clock_mode_operation backend io native stable discipline(Some saved))
    slots allocated allocation_world readonly selected reference owner allocation_before child source world events returned after next descriptor:
  reap_allocations allocation_before slots allocated->gateway_reap_scope slots readonly selected reference->0<Int.signed child->
  (exists target,selected target)->
  gateway_reap_assertion native stable discipline saved slots allocated allocation_world
    readonly selected reference owner child source world->
  gateway_steps backend(Clight.globalenv prog)(gateway_live source world)events(gateway_live(Returnstate returned Kstop after)next)->
  discipline(Some saved)after next /\gateway_caller_family native stable readonly selected reference owner after next /\
    gateway_received_bytes io descriptor events=[].
Proof.
  intros ALLOC SCOPE CHILD NONEMPTY.
  remember(length events)as size eqn:SIZE;revert events SIZE source world.
  induction size using lt_wf_ind;intros events SIZE source world READY RUN.
  assert(REGULAR_CASE:gateway_reap_regular source->
    discipline(Some saved)after next /\gateway_caller_family native stable readonly selected reference owner after next /\
      gateway_received_bytes io descriptor events=[]).
  { intro REGULAR;destruct events as[|event rest].
    - inversion RUN;subst;split;[exact(proj1(proj2 READY))|].
      split;[exact(proj2(proj2 READY))|reflexivity].
    - inversion RUN as[|first observed middle remaining last STEP TAIL];subst.
      destruct(gateway_reap_regular_step backend io observation native stable discipline thread_errno thread runtime
        saved slots allocated allocation_world readonly selected reference owner allocation_before child ALLOC SCOPE CHILD
        source world event middle descriptor READY REGULAR STEP)as[STATE EMPTY].
      destruct middle as[following current|memory current].
      + destruct(H(length rest)ltac:(cbn;lia)rest eq_refl following current STATE TAIL)
          as[FINAL[HISTORY REST]]. split;[exact FINAL|]. split;[exact HISTORY|].
        change(gateway_received_event io descriptor event++gateway_received_bytes io descriptor rest=[]).
        rewrite EMPTY,REST;reflexivity.
      + destruct(gateway_dead_steps _ _ _ _ _ _ TAIL)as[_ BAD];discriminate. }
  destruct source as[function body continuation environment temporaries memory|
    definition arguments continuation memory|value continuation memory].
  - apply REGULAR_CASE;exact I.
  - destruct definition as[function|ef types result_type convention].
    + destruct READY as[[[site[DEFINITION ARGUMENTS]]FRAME]CONTEXT].
      destruct site;cbn[reap_site_definition]in DEFINITION;try discriminate.
      inversion DEFINITION;subst function;cbn[reap_site_values]in ARGUMENTS;subst arguments.
      destruct FRAME as(destination&temporaries&rest&CONTINUATION&DESTINATION&CHILD_TEMP&CONT);subst continuation.
      destruct(gateway_return_cut backend(Clight.globalenv prog)(Internal f_host_now)[]
        (Kcall destination f_host_engine_reap(reap_environment slots)temporaries rest)memory world events
        (Returnstate returned Kstop after)next I ltac:(cbn[gateway_continuation gateway_cont_weight];lia)RUN)
        as(body_events&caller_events&clock_value&changed&current&EVENTS&BODY&CALLER).
      destruct(gateway_reap_clock_context backend io native stable discipline thread_errno thread saved clock
        slots allocated allocation_world readonly selected reference owner memory world body_events clock_value changed current descriptor
        CONTEXT NONEMPTY BODY)as[AFTER EMPTY].
      assert(RETURNED:gateway_reap_assertion native stable discipline saved slots allocated allocation_world
        readonly selected reference owner child
        (Returnstate clock_value(Kcall destination f_host_engine_reap(reap_environment slots)temporaries rest)changed)current).
      { apply gateway_reap_assertion_context;[right;exists destination,temporaries,rest;repeat split;try reflexivity;assumption|exact AFTER]. }
      assert(BODY_NONEMPTY:body_events<>[])by(intro NIL;subst body_events;inversion BODY).
      destruct(H(length caller_events)ltac:(rewrite SIZE,EVENTS,app_length;destruct body_events;[contradiction|cbn;lia])
        caller_events eq_refl _ current RETURNED CALLER)as[FINAL[HISTORY CALLER_EMPTY]].
      split;[exact FINAL|]. split;[exact HISTORY|].
      rewrite EVENTS,gateway_received_bytes_append,EMPTY,CALLER_EMPTY;reflexivity.
    + apply REGULAR_CASE;exact I.
  - apply REGULAR_CASE;exact I.
Qed.
