(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Cleanup passes the actual saved token and stored child to reaping. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewayRuntime GatewayRuntimeABI GatewayOperations
  GatewayContexts GatewayFramedRuntime GatewayRuntimeCuts GatewayMemoryPrefixes GatewayReadonly GatewayPrimitiveCalls
  GatewayPrimitiveSilence GatewayErrnoFragment GatewayExchangeSetup GatewayExchangeTransport GatewayCleanupSource GatewayCleanupThreadSource.
Import ListNotations.
Open Scope Z_scope.

Theorem actual_exchange_cleanup_save {World Event}(backend:gateway_backend World Event)io property(post:val->mem->World->Prop)
    (CLOSED:gateway_ambient_closed backend property)(POST_CLOSED:forall saved,gateway_ambient_closed backend(post saved))
    allocation_before allocated environment temporaries child_cell child object offset before world events value after next:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  environment!_child=Some(child_cell,tint)->temporaries!_result=Some(Vptr object offset)->
  (forall memory current returned changed future observed,property memory current->
    gateway_runtime_operation backend gateway_save_thread_definition[]memory current returned changed future observed->
    (exists saved_block saved_offset,returned=Vptr saved_block saved_offset) /\post returned changed future /\io observed=None)->
  (forall saved memory current,post saved memory current->Mem.load Mint32 memory child_cell 0=Some(Vint child))->
  (forall saved memory current,post saved memory current->Mem.weak_valid_pointer memory object(Ptrofs.unsigned offset)=true)->
  property before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_exchange(exchange_cleanup_after 2)Kstop environment temporaries before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists prefix suffix memory current saved_block saved_offset,
    events=prefix++suffix /\gateway_errno_silent io prefix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange(exchange_cleanup_after 2)Kstop environment temporaries before)world)prefix
      (gateway_live(Callstate(Internal f_host_engine_reap)[Vint child;Vint Int.one]
        (cleanup_reap_cont environment(cleanup_reap_temps child(Vptr saved_block saved_offset)temporaries))memory)current) /\
    post(Vptr saved_block saved_offset)memory current /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(Internal f_host_engine_reap)[Vint child;Vint Int.one]
        (cleanup_reap_cont environment(cleanup_reap_temps child(Vptr saved_block saved_offset)temporaries))memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros ALLOC CHILD RESULT OPERATION CELL POINTER READY RUN.
  assert(SAVE_LOCAL:environment!_PyEval_SaveThread=None).
  { eapply actual_exchange_setup_unshadowed;[exact ALLOC|cbn;intuition discriminate]. }
  assert(SAVE_FUNCTION:gateway_function_binding(Clight.globalenv prog)_PyEval_SaveThread gateway_save_thread_definition).
  { apply gateway_actual_function_binding;vm_compute;reflexivity. }
  assert(REAP_LOCAL:environment!_host_engine_reap=None).
  { eapply actual_exchange_setup_unshadowed;[exact ALLOC|cbn;intuition discriminate]. }
  assert(REAP_FUNCTION:gateway_function_binding(Clight.globalenv prog)_host_engine_reap(Internal f_host_engine_reap)).
  { apply gateway_actual_function_binding;vm_compute;reflexivity. }
  destruct(gateway_memory_prefix_cut backend(Clight.globalenv prog)_ _ _ _ before world events(Returnstate value Kstop after)next
    (actual_cleanup_save_prefix backend(Clight.globalenv prog)property CLOSED environment temporaries before SAVE_LOCAL SAVE_FUNCTION)I READY RUN)
    as(p1&r1&m1&w1&E1&Q1&P1&C1&S1).
  cbn[gateway_replace_memory]in P1,S1.
  destruct(gateway_return_cut backend(Clight.globalenv prog)gateway_save_thread_definition[](cleanup_save_cont environment temporaries)
    m1 w1 r1(Returnstate value Kstop after)next I ltac:(cbn;lia)S1)
    as(body&r2&saved&m2&w2&E2&BODY&S2).
  destruct(gateway_actual_primitive_context backend(Clight.globalenv prog)_ _ _ _ []property
    (fun saved memory current=>(exists object offset,saved=Vptr object offset) /\post saved memory current)CLOSED
    ltac:(intro saved_value;intros memory current changed future[POINTED INPUT]AMBIENT;split;
      [exact POINTED|exact(POST_CLOSED saved_value memory current changed future INPUT AMBIENT)])
    ltac:(intros api_before api_world api_result api_after api_next api_event INPUT API;
      pose proof(OPERATION api_before api_world api_result api_after api_next api_event INPUT API)as[POINTED[AFTER EMPTY]];
      split;assumption)
    m1 w1 body saved m2 w2 C1 BODY)
    as(pending&tail&called&called_world&changed&changed_world&observed&EB&PENDING&PENDING_RUN&INPUT&API&OUTPUT&TAIL&[SAVED RETURNED]).
  destruct SAVED as[saved_block[saved_offset SAVED]];subst saved.
  assert(SILENT:gateway_errno_silent io body).
  { eapply gateway_actual_primitive_silent;
      [exact CLOSED| |exact C1|exact BODY].
    intros api_before api_world api_result api_after api_next api_event INITIAL PRIMITIVE.
    exact(proj2(proj2(OPERATION api_before api_world api_result api_after api_next api_event INITIAL PRIMITIVE))). }
  destruct(gateway_uniform_edge_side_cut backend(Clight.globalenv prog)(post(Vptr saved_block saved_offset))(POST_CLOSED(Vptr saved_block saved_offset))
    (Returnstate(Vptr saved_block saved_offset)(cleanup_save_cont environment temporaries)m2)
    (State f_host_exchange Sskip cleanup_save_after environment(cleanup_save_temps(Vptr saved_block saved_offset)temporaries)m2)
    m2 w2 r2 value after next ltac:(cbn;tauto)
    ltac:(intros;apply unchanged_store_edge,edge_returnstate)RETURNED S2)
    as(p3&r3&m3&w3&E3&Q3&P3&C3&S3).
  cbn[gateway_replace_memory]in P3,S3.
  destruct(gateway_memory_prefix_cut backend(Clight.globalenv prog)_ _ _ _ m3 w3 r3(Returnstate value Kstop after)next
    (actual_cleanup_saved_reap_prefix backend(Clight.globalenv prog)(post(Vptr saved_block saved_offset))(POST_CLOSED(Vptr saved_block saved_offset))
      environment temporaries m3 child_cell child saved_block saved_offset object offset CHILD REAP_LOCAL REAP_FUNCTION RESULT
      (CELL(Vptr saved_block saved_offset))(POINTER(Vptr saved_block saved_offset)))I C3 S3)
    as(p4&suffix&memory&current&E4&Q4&P4&FINAL&SUFFIX).
  cbn[gateway_replace_memory]in P4,SUFFIX.
  exists(p1++body++p3++gateway_source E0::p4),suffix,memory,current,saved_block,saved_offset.
  split;[rewrite E1,E2,E3,E4;repeat rewrite<-app_assoc;reflexivity|]. split.
  - apply gateway_errno_silent_append;[apply gateway_errno_silent_quiet;exact Q1|].
    apply gateway_errno_silent_append;[exact SILENT|].
    apply gateway_errno_silent_append;[apply gateway_errno_silent_ambient;exact Q3|].
    apply gateway_errno_silent_append with(first:=[gateway_source E0]);[apply gateway_errno_silent_source|].
    apply gateway_errno_silent_quiet;exact Q4.
  - split.
    + eapply gateway_steps_append;[exact P1|].
      eapply gateway_steps_append;[exact(gateway_plug_steps backend(Clight.globalenv prog)_ _ _(cleanup_save_cont environment temporaries)I BODY)|].
      eapply gateway_steps_append;[exact P3|].
      econstructor;[apply gateway_internal;[cbn;tauto|constructor;reflexivity]|exact P4].
    + split;assumption.
Qed.
