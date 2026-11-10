(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The parser receipt retains actual readonly native capabilities
   through its caller guards. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayImport GatewayMachine GatewayStreamInterface GatewayStreamLayout GatewayThreadRuntime
  GatewayFramedRuntime GatewayReadonly GatewayValueEntry GatewayValueContext GatewayPython GatewayObjects GatewayReferences
  GatewayObjectDiscipline GatewayObjectThreads GatewayValue GatewayReferenceLedger GatewayReferenceAccounting
  GatewayReferenceHeld GatewayReferenceThreads GatewayReferenceContainerScope
  GatewayReferenceGraphCapture GatewayReferenceDecoded GatewayReferenceParseResult
  GatewayContainerEncoding GatewayExchangeTransport GatewayResponseParserSource GatewayParserBinding GatewayTrailingSource GatewayTrailingComplete.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Section ParserOwnedCaller.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
  (python:World->python_world)(objects:World->gateway_object_heap)
  (stable:World->block->Z->Prop)(detached:Values.val->Memory.mem->World->Prop)(thread_errno:World->int)
  (heap_allocation:block->Z->Prop)(decimal_float:list Z->Floats.float->Prop).
Let native:=fun world object=>gateway_native_private(python world)object.
Let base:=gateway_python_discipline python objects detached.
Context(thread:gateway_thread_runtime backend io native stable base thread_errno)
  (reference_threads:gateway_reference_thread_contract backend native stable base heap_allocation python objects).

(* The final caller applies the actual whole-parser producer to its SAME body.
   This consumer introduces no parser-success or whole-object runtime contract. *)
Theorem actual_parsed_response_reaches_eof_owned environment temporaries ledger held stream initial readonly original parser_events
    parsed before world events value after next:
  environment!_stream=Some(stream,Tstruct _host_stream noattr)->
  gateway_reference_parse_result python objects decimal_float detached io stable(Clight.globalenv prog)
    (response_parser_cont environment temporaries)ledger held stream Ptrofs.zero initial readonly original parser_events parsed before world->
  value<>Vnullptr->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Returnstate parsed(response_parser_cont environment temporaries)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists final final_stream wire ticket object offset prefix suffix memory current,
    parsed=Vptr object offset /\stream_remaining final_stream=Int64.zero /\events=prefix++suffix /\
    Forall gateway_quiet_event prefix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate parsed(response_parser_cont environment temporaries)before)world)prefix
      (gateway_live(State f_host_exchange(exchange_transport_after 7)Kstop environment
        (gateway_trailing_temps(stream_remaining final_stream)(gateway_parser_bound_temps parsed temporaries))memory)current) /\
    gateway_value_context native stable base stream Ptrofs.zero final_stream readonly original memory current /\
    (forall candidate position,readonly candidate position->native current candidate) /\
    gateway_reference_scope python objects decimal_float final
      (held++[gateway_reference_graph_capture ticket parsed wire(objects world)])current /\
    gateway_value_heap decimal_float(objects current)parsed wire /\
    gateway_response_frame(LeanCage_Host_GatewayResponseCode_Subject_value wire)
      (gateway_received_bytes io(stream_descriptor initial)parser_events) /\
    stream_descriptor final_stream=stream_descriptor initial /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange(exchange_transport_after 7)Kstop environment
        (gateway_trailing_temps(stream_remaining final_stream)(gateway_parser_bound_temps parsed temporaries))memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros STREAM PARSED NONNULL RUN.
  destruct PARSED as(final&final_stream&wire&ticket&DECODED&CONTEXT&READONLY&DESCRIPTOR&FRAMING).
  pose proof DECODED as[FORMED ENTRIES FRESH OWNER BOUND SCOPE VALUE AVOIDS].
  set(scope:=gateway_reference_scope python objects decimal_float final
    (held++[gateway_reference_graph_capture ticket parsed wire(objects world)])).
  set(property:=fun memory current=>gateway_value_context native stable base stream Ptrofs.zero final_stream readonly original memory current /\scope current /\
    (forall candidate position,readonly candidate position->native current candidate)).
  assert(READY:property before world)by(split;[exact CONTEXT|];split;assumption).
  assert(CLOSED:gateway_ambient_closed backend property).
  { intros memory current changed future[INPUT[HELD PRIVATE]]AMBIENT;split.
    - eapply gateway_value_context_ambient;[exact thread|exact INPUT|exact AMBIENT].
    - split.
      + eapply gateway_reference_scope_thread_effect;[exact HELD|].
        eapply gateway_reference_thread_ambient;[exact reference_threads|exact(proj1 INPUT)|exact AMBIENT].
      + intros candidate position HERE.
        destruct(gateway_thread_ambient _ _ _ _ _ _ thread None memory current changed future(proj1 INPUT)AMBIENT)
          as[NORMAL[[NATIVE STABLE]FRAME]].
        apply NATIVE.
        * exact(gateway_value_readonly_live _ _ _ _ _(proj1(proj2(proj2(proj2 INPUT))))candidate position HERE).
        * exact(PRIVATE candidate position HERE). }
  assert(POINTER:forall memory current,property memory current->exists object offset,
    parsed=Vptr object offset /\Mem.weak_valid_pointer memory object(Ptrofs.unsigned offset)=true).
  { intros memory current[INPUT[HELD PRIVATE]].
    assert(ROOT:gateway_rooted(python current)(objects current)parsed).
    { eapply gateway_reference_owned_rooted;[exact(proj1 HELD)|exact OWNER]. }
    pose proof(proj1 INPUT)as[SOUND REST].
    destruct SOUND as[PYTHON[LIVE[BYTES[DICTS POINTERS]]]].
    apply POINTERS;exact ROOT. }
  destruct(POINTER before world READY)as(object&offset&POINTER_VALUE&VALID_POINTER).
  subst parsed.
  assert(CELLS:forall memory current,property memory current->
    gateway_stream_memory memory stream Ptrofs.zero final_stream).
  { intros memory current[[NORMAL[PRIVATE[IMMUTABLE[INPUT FRAME]]]][HELD NATIVE]].
    exact(gateway_value_stream_cells _ _ _ _ _ INPUT). }
  assert(WEAK:forall memory current,property memory current->
    Mem.weak_valid_pointer memory object(Ptrofs.unsigned offset)=true).
  { intros memory current GOOD.
    destruct(POINTER memory current GOOD)as(actual&position&SAME&VALID).
    inversion SAME;subst;exact VALID. }
  destruct(actual_parser_bound_prefix backend(Clight.globalenv prog)property CLOSED environment temporaries object offset
    before world events value after next READY RUN)as(p1&r1&m1&w1&E1&Q1&P1&R1&S1).
  destruct(actual_successful_trailing_guard backend(Clight.globalenv prog)property CLOSED environment
    (gateway_parser_bound_temps(Vptr object offset)temporaries)stream final_stream object offset m1 w1 r1 value after next
    STREAM(proj1(proj2(proj2(proj2(proj2(proj2 actual_stream_layout))))))ltac:(apply PTree.gss)
    CELLS WEAK R1 NONNULL S1)
    as[ZERO[p2[suffix[memory[current[E2[Q2[P2[FINAL SUFFIX]]]]]]]]].
  exists final,final_stream,wire,ticket,object,offset,(p1++p2),suffix,memory,current.
  split;[reflexivity|]. split;[exact ZERO|]. split;[rewrite E1,E2,app_assoc;reflexivity|].
  split;[apply Forall_app;split;assumption|]. split;[eapply gateway_steps_append;[exact P1|exact P2]|].
  split;[exact(proj1 FINAL)|]. split;[exact(proj2(proj2 FINAL))|]. split;[exact(proj1(proj2 FINAL))|]. split.
  - pose proof(gateway_reference_capture_member _ _ _ _ _ _ _(proj1(proj2 FINAL))
      ltac:(apply in_or_app;right;left;reflexivity))as[OWNED[PRIVATE[DESTROY[WIRE REST]]]];exact WIRE.
  - split;[exact FRAMING|]. split;assumption.
Qed.
End ParserOwnedCaller.
