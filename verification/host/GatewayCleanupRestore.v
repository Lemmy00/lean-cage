(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual restoration precedes the original response-status projection. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine ClightSteps StoreSteps.
From HostGateway Require Import GatewaySource GatewayMachine GatewayRuntime GatewayRuntimeABI GatewayOperations GatewayThreadRuntime
  GatewayStreamInterface GatewayCallerBuffers GatewayCallerFamily GatewayContexts GatewayPrimitiveCalls GatewayPrimitiveSilence
  GatewayCleanupSource GatewayCleanupRestoreSource GatewayRuntimeCuts GatewayMemoryPrefixes GatewayTransferMath
  GatewayFramedRuntime GatewayGuardObservation GatewayReadonly.
Import ListNotations.

Theorem actual_exchange_cleanup_restore {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (thread:gateway_thread_runtime backend io native stable discipline thread_errno)saved_block saved_offset
    readonly selected reference owner environment temporaries before world events value after next descriptor:
  discipline(Some(Vptr saved_block saved_offset))before world->
  gateway_caller_family native stable readonly selected reference owner before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate gateway_restore_thread_definition[Vptr saved_block saved_offset]
      (cleanup_restore_cont environment temporaries)before)world)events(gateway_live(Returnstate value Kstop after)next)->
  exists prefix suffix memory current,
    events=prefix++suffix /\gateway_received_bytes io descriptor prefix=[] /\discipline None memory current /\
    gateway_caller_family native stable readonly selected reference owner memory current /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate gateway_restore_thread_definition[Vptr saved_block saved_offset]
        (cleanup_restore_cont environment temporaries)before)world)prefix
      (gateway_live(State f_host_exchange(exchange_cleanup_after 5)Kstop environment temporaries memory)current) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange(exchange_cleanup_after 5)Kstop environment temporaries memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros SIDE FAMILY RUN.
  set(property:=fun mode memory world=>discipline mode memory world /\
    gateway_caller_family native stable readonly selected reference owner memory world).
  assert(CLOSED:forall mode,gateway_ambient_closed backend(property mode)).
  { intros mode memory current changed future[HELD HISTORY]INTERFERENCE.
    destruct(gateway_thread_ambient _ _ _ _ _ _ thread mode memory current changed future HELD INTERFERENCE)
      as[AFTER[ACCESS FRAME]]. split;[exact AFTER|].
    intros target SELECTED;eapply gateway_caller_buffers_no_output;[exact(HISTORY target SELECTED)|exact ACCESS|exact FRAME]. }
  assert(EFFECT:forall api_before api_world result api_after api_next api_event,
    property(Some(Vptr saved_block saved_offset))api_before api_world->
    gateway_runtime_operation backend gateway_restore_thread_definition[Vptr saved_block saved_offset]
      api_before api_world result api_after api_next api_event->property None api_after api_next /\io api_event=None).
  { intros api_before api_world result api_after api_next api_event[INPUT HISTORY]API.
    destruct(gateway_restore_thread_operation _ _ _ _ _ _ thread(Vptr saved_block saved_offset)
      api_before api_world result api_after api_next api_event INPUT API)as[AFTER[ACCESS[FRAME IO]]].
    split;[split;[exact AFTER|]|exact IO].
    intros target SELECTED;eapply gateway_caller_buffers_no_output;[exact(HISTORY target SELECTED)|exact ACCESS|exact FRAME]. }
  destruct(gateway_return_cut backend(Clight.globalenv prog)gateway_restore_thread_definition[Vptr saved_block saved_offset]
    (cleanup_restore_cont environment temporaries)before world events(Returnstate value Kstop after)next I
    ltac:(cbn[gateway_continuation gateway_cont_weight cleanup_restore_cont];lia)RUN)
    as(body&caller_events&returned&changed&changed_world&EVENTS1&BODY&CALLER).
  destruct(gateway_actual_primitive_context backend(Clight.globalenv prog)_ _ _ _[Vptr saved_block saved_offset]
    (property(Some(Vptr saved_block saved_offset)))(fun _=>property None)(CLOSED(Some(Vptr saved_block saved_offset)))
    ltac:(intro ignored;apply CLOSED)
    ltac:(intros;exact(proj1(EFFECT _ _ _ _ _ _ H H0)))
    before world body returned changed changed_world(conj SIDE FAMILY)BODY)
    as(pending&tail&called&called_world&api_after&api_next&observed&EB&PENDING&PENDING_RUN&INPUT&API&OUTPUT&TAIL&FINAL).
  assert(EMPTY:gateway_received_bytes io descriptor body=[]).
  { eapply gateway_actual_primitive_no_receive;
      [apply CLOSED| |exact(conj SIDE FAMILY)|exact BODY].
    intros;exact(proj2(EFFECT _ _ _ _ _ _ H H0)). }
  destruct(gateway_uniform_edge_side_cut backend(Clight.globalenv prog)(property None)(CLOSED None)
    (Returnstate returned(cleanup_restore_cont environment temporaries)changed)
    (State f_host_exchange Sskip cleanup_restore_after environment temporaries changed)
    changed changed_world caller_events value after next ltac:(cbn;tauto)
    ltac:(intros;apply unchanged_store_edge,edge_returnstate)FINAL CALLER)
    as(prefix1&rest&memory1&world1&EVENTS2&AMBIENT&PREFIX1&CONTEXT1&REST1).
  destruct(gateway_memory_prefix_cut backend(Clight.globalenv prog)_ _ _ _ memory1 world1 rest(Returnstate value Kstop after)next
    (actual_cleanup_restored_final_path backend(Clight.globalenv prog)(property None)(CLOSED None)environment temporaries memory1)
    I CONTEXT1 REST1)as(prefix2&suffix&memory&current&EVENTS3&QUIET&PREFIX2&[HELD HISTORY]&SUFFIX).
  exists(body++prefix1++gateway_source E0::prefix2),suffix,memory,current.
  split;[rewrite EVENTS1,EVENTS2,EVENTS3;repeat rewrite <-app_assoc;reflexivity|]. split.
  - repeat rewrite gateway_received_bytes_append;rewrite gateway_received_source_cons,EMPTY.
    assert(PENDING_EMPTY:gateway_received_bytes io descriptor prefix1=[]).
    { apply gateway_quiet_received_empty;eapply Forall_impl;[|exact AMBIENT];intros event SAME;right;exact SAME. }
    rewrite PENDING_EMPTY,(gateway_quiet_received_empty io descriptor prefix2 QUIET);reflexivity.
  - split;[exact HELD|]. split;[exact HISTORY|]. split;[|exact SUFFIX].
    eapply gateway_steps_append;
      [exact(gateway_plug_steps backend(Clight.globalenv prog)_ _ _(cleanup_restore_cont environment temporaries)I BODY)|].
    eapply gateway_steps_append;[exact PREFIX1|].
    econstructor;[apply gateway_internal;[exact I|constructor]|exact PREFIX2].
Qed.
