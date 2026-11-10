(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: Real endpoint closes precede cleanup of the same engine
   invocation. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewayRuntime GatewayOperations GatewayContexts
  GatewayThreadRuntime GatewayStreamInterface GatewayStreamLayout GatewayReadonly GatewayPrimitiveCalls GatewayTransferMath
  GatewaySendRuntime GatewayErrnoFragment GatewayFramedRuntime GatewayRuntimeCuts GatewayMemoryPrefixes GatewayExchangeSetup
  GatewayExchangeTransport GatewaySpawnABI GatewayCleanupSource.
Import ListNotations.
Open Scope Z_scope.

Theorem actual_exchange_cleanup_close {World Event}(backend:gateway_backend World Event)io property post
    (CLOSED:gateway_ambient_closed backend property)(POST_CLOSED:gateway_ambient_closed backend post)
    endpoint stream initial allocation_before allocated environment temporaries before world events value after next:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  environment!_stream=Some(stream,Tstruct _host_stream noattr)->
  (forall memory current,property memory current->gateway_stream_memory memory stream Ptrofs.zero initial)->
  (forall memory current result changed future observed,property memory current->
    gateway_runtime_operation backend(gateway_spawn_signature gateway_close_api)[Vint(cleanup_close_value endpoint initial)]
      memory current result changed future observed->post changed future /\io observed=None)->
  property before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_exchange(exchange_cleanup_after(cleanup_close_index endpoint))Kstop environment temporaries before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists prefix suffix memory current,
    events=prefix++suffix /\gateway_errno_silent io prefix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange(exchange_cleanup_after(cleanup_close_index endpoint))Kstop environment temporaries before)world)prefix
      (gateway_live(State f_host_exchange(exchange_cleanup_after(S(cleanup_close_index endpoint)))Kstop environment
        (cleanup_close_temps endpoint(cleanup_close_value endpoint initial)temporaries)memory)current) /\post memory current /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange(exchange_cleanup_after(S(cleanup_close_index endpoint)))Kstop environment
        (cleanup_close_temps endpoint(cleanup_close_value endpoint initial)temporaries)memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros ALLOC STREAM CELLS OPERATION READY RUN.
  set(loaded:=cleanup_close_temps endpoint(cleanup_close_value endpoint initial)temporaries).
  assert(LOCAL:environment!_close=None).
  { eapply actual_exchange_setup_unshadowed;[exact ALLOC|cbn;intuition discriminate]. }
  assert(FUNCTION:gateway_function_binding(Clight.globalenv prog)_close(gateway_spawn_signature gateway_close_api)).
  { apply gateway_actual_function_binding;vm_compute;reflexivity. }
  destruct(gateway_memory_prefix_cut backend(Clight.globalenv prog)_ _ _ _ before world events(Returnstate value Kstop after)next
    (actual_cleanup_close_prefix backend(Clight.globalenv prog)property CLOSED endpoint environment temporaries before stream initial STREAM
      (proj1 actual_stream_layout)(proj1(proj2 actual_stream_layout))LOCAL FUNCTION CELLS)I READY RUN)
    as(p1&r1&m1&w1&E1&Q1&P1&C1&S1).
  cbn[gateway_replace_memory]in P1,S1.
  destruct(gateway_return_cut backend(Clight.globalenv prog)(gateway_spawn_signature gateway_close_api)
    [Vint(cleanup_close_value endpoint initial)](cleanup_close_cont endpoint environment loaded)m1 w1 r1
    (Returnstate value Kstop after)next I ltac:(cbn;lia)S1)
    as(body&r2&returned&m2&w2&E2&BODY&S2).
  destruct(gateway_actual_primitive_context backend(Clight.globalenv prog)_ _ _ _ [Vint(cleanup_close_value endpoint initial)]
    property(fun _=>post)CLOSED ltac:(intro result;exact POST_CLOSED)
    ltac:(intros api_before api_world api_result api_after api_next api_event INPUT API;
      exact(proj1(OPERATION api_before api_world api_result api_after api_next api_event INPUT API)))
    m1 w1 body returned m2 w2 C1 BODY)
    as(pending&tail&called&called_world&changed&changed_world&observed&EB&PENDING&PENDING_RUN&INPUT&API&OUTPUT&TAIL&RETURNED).
  assert(SILENT:gateway_errno_silent io body).
  { destruct(OPERATION _ _ _ _ _ _ INPUT API)as[AFTER EMPTY].
    rewrite EB;apply gateway_errno_silent_append;[apply gateway_errno_silent_pending;exact PENDING|].
    apply gateway_errno_silent_append with(first:=[gateway_primitive observed]).
    - intros descriptor;split;unfold gateway_received_bytes,gateway_sent_bytes;
        cbn[flat_map gateway_received_event gateway_sent_event];rewrite EMPTY;reflexivity.
    - apply gateway_errno_silent_ambient;eapply gateway_terminal_return_ambient;exact TAIL. }
  destruct(gateway_uniform_edge_side_cut backend(Clight.globalenv prog)post POST_CLOSED
    (Returnstate returned(cleanup_close_cont endpoint environment loaded)m2)
    (State f_host_exchange Sskip(cleanup_close_after endpoint)environment loaded m2)
    m2 w2 r2 value after next ltac:(cbn;tauto)
    ltac:(intros;apply unchanged_store_edge,edge_returnstate)RETURNED S2)
    as(p3&r3&m3&w3&E3&Q3&P3&C3&S3).
  cbn[gateway_replace_memory]in P3,S3.
  destruct(gateway_memory_prefix_cut backend(Clight.globalenv prog)_ _ _ _ m3 w3 r3(Returnstate value Kstop after)next
    (actual_cleanup_close_return_path backend(Clight.globalenv prog)post POST_CLOSED endpoint environment loaded m3)I C3 S3)
    as(p4&suffix&memory&current&E4&Q4&P4&FINAL&SUFFIX).
  cbn[gateway_replace_memory]in P4,SUFFIX.
  exists(p1++body++p3++gateway_source E0::p4),suffix,memory,current.
  split;[rewrite E1,E2,E3,E4;repeat rewrite<-app_assoc;reflexivity|]. split.
  - apply gateway_errno_silent_append;[apply gateway_errno_silent_quiet;exact Q1|].
    apply gateway_errno_silent_append;[exact SILENT|].
    apply gateway_errno_silent_append;[apply gateway_errno_silent_ambient;exact Q3|].
    apply gateway_errno_silent_append with(first:=[gateway_source E0]);[apply gateway_errno_silent_source|].
    apply gateway_errno_silent_quiet;exact Q4.
  - split.
    + eapply gateway_steps_append;[exact P1|].
      eapply gateway_steps_append;[exact(gateway_plug_steps backend(Clight.globalenv prog)_ _ _(cleanup_close_cont endpoint environment loaded)I BODY)|].
      eapply gateway_steps_append;[exact P3|].
      econstructor;[apply gateway_internal;[cbn;tauto|constructor;reflexivity]|exact P4].
    + split;assumption.
Qed.
