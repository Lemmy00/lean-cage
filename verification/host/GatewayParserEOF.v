(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The same parsed graph and byte framing survive real EOF and retries. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayImport GatewayMachine GatewayPython GatewayObjects GatewayReferences
  GatewayObjectDiscipline GatewayObjectThreads GatewayValue GatewayValueEntry GatewayValueContext GatewayThreadRuntime
  GatewayReadContext GatewayStreamInterface GatewayBufferReference GatewayReadonly GatewayPrimitiveCalls
  GatewayTransferMath GatewaySendRuntime GatewayStreamRelations GatewayThreadInvariant GatewayReferenceLedger
  GatewayReferenceAccounting GatewayReferenceHeld GatewayReferenceThreads GatewayReferenceContainerScope GatewayReferenceGraphCapture
  GatewayReferenceDecoded GatewayReferenceParseResult GatewayContainerEncoding GatewayExchangeEntry GatewayExchangeTransport
  GatewayResponseParserSource GatewayParserBinding GatewayTrailingSource GatewayParserOwnedCaller
  GatewayEOFNative GatewayEOFReferences GatewayEOFInputs GatewayEOFComplete.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Section ParserEOF.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
  (python:World->python_world)(objects:World->gateway_object_heap)
  (stable:World->block->Z->Prop)(detached:Values.val->Memory.mem->World->Prop)(thread_errno:World->int)
  (heap_allocation:block->Z->Prop)(decimal_float:list Z->Floats.float->Prop).
Let native:=fun world object=>gateway_native_private(python world)object.
Let base:=gateway_python_discipline python objects detached.
Context(thread:gateway_thread_runtime backend io native stable base thread_errno)
  (reference_threads:gateway_reference_thread_contract backend native stable base heap_allocation python objects)
  (held_receive:gateway_eof_receive_runtime backend io native stable base)
  (receive_references:gateway_eof_reference_runtime backend native base python objects).

Theorem actual_parsed_response_observes_eof allocation_before allocated environment temporaries ledger held
    stream extra initial readonly original parser_events parsed before world events value after next control:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  environment!_stream=Some(stream,Tstruct _host_stream noattr)->environment!_extra=Some(extra,tuchar)->
  (forall position,0<=position<1->readonly extra position)->Mem.range_perm original extra 0 1 Cur Writable->
  (forall position,4<=position<8->readonly stream position)->Mem.load Mint32 original stream 4=Some(Vint control)->
  stream_descriptor initial<>control->
  gateway_reference_parse_result python objects decimal_float detached io stable(Clight.globalenv prog)
    (response_parser_cont environment temporaries)ledger held stream Ptrofs.zero initial readonly original parser_events parsed before world->
  value<>Vnullptr->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Returnstate parsed(response_parser_cont environment temporaries)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists final wire ticket object offset prefix suffix memory current final_temps updated observed,
    parsed=Vptr object offset /\events=prefix++suffix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate parsed(response_parser_cont environment temporaries)before)world)prefix
      (gateway_live(State f_host_exchange exchange_cleanup_phase Kstop environment final_temps memory)current) /\
    final_temps!_result=Some parsed /\stream_descriptor updated=stream_descriptor initial /\stream_remaining updated=Int64.zero /\
    gateway_read_context native stable base None stream Ptrofs.zero updated extra Ptrofs.zero 1
      (gateway_eof_readonly readonly extra)memory current /\
    gateway_reference_scope python objects decimal_float final
      (held++[gateway_reference_graph_capture ticket parsed wire(objects world)])current /\
    gateway_value_heap decimal_float(objects current)parsed wire /\
    gateway_response_frame(LeanCage_Host_GatewayResponseCode_Subject_value wire)
      (gateway_received_bytes io(stream_descriptor initial)(parser_events++prefix)) /\
    gateway_received_bytes io(stream_descriptor initial)prefix=[] /\gateway_sent_bytes io(stream_descriptor initial)prefix=[] /\
    In(gateway_primitive observed)prefix /\io observed=Some(gateway_native_receive(stream_descriptor initial)1 0[]) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange exchange_cleanup_phase Kstop environment final_temps memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros ALLOC STREAM EXTRA EXTRA_READONLY EXTRA_WRITABLE CONTROL_READONLY CONTROL_LOAD SEPARATE PARSED NONNULL RUN.
  assert(BLOCKS:stream<>extra).
  { destruct(actual_exchange_allocations(Clight.globalenv prog)allocation_before environment allocated ALLOC)
      as[BUFFERS[[LIVE DISTINCT]FRAME]].
    eapply DISTINCT;[exact STREAM|exact EXTRA|discriminate]. }
  destruct(actual_parsed_response_reaches_eof_owned backend io python objects stable detached thread_errno heap_allocation decimal_float
    thread reference_threads environment temporaries ledger held stream initial readonly original parser_events parsed
    before world events value after next STREAM PARSED NONNULL RUN)
    as(final&final_stream&wire&ticket&object&offset&p1&r1&m1&w1&POINTER&ZERO&E1&Q1&P1&INPUT&NATIVE&SCOPE&VALUE&FRAMING&DESCRIPTOR&S1).
  subst parsed.
  set(captures:=held++[gateway_reference_graph_capture ticket(Vptr object offset)wire(objects world)]).
  set(scope:=gateway_reference_scope python objects decimal_float final captures).
  set(scoped:=gateway_thread_invariant_discipline base scope).
  pose proof(gateway_thread_with_reference_scope backend io native stable base thread_errno heap_allocation python objects decimal_float
    reference_threads final captures thread)as SCOPED_THREAD.
  pose proof(gateway_eof_with_reference_scope backend io native stable base python objects held_receive receive_references
    decimal_float final captures)as SCOPED_RECEIVE.
  assert(RAW:gateway_read_context native stable base None stream Ptrofs.zero final_stream extra Ptrofs.zero 1
    (gateway_eof_readonly readonly extra)m1 w1).
  { eapply gateway_eof_inputs_from_parser;[exact INPUT|exact NATIVE|exact BLOCKS|exact EXTRA_READONLY|exact EXTRA_WRITABLE]. }
  assert(READY:gateway_read_context native stable scoped None stream Ptrofs.zero final_stream extra Ptrofs.zero 1
    (gateway_eof_readonly readonly extra)m1 w1).
  { split;[split;[exact(proj1 RAW)|exact SCOPE]|exact(proj2 RAW)]. }
  assert(WEAK:forall memory current,scoped None memory current->Mem.weak_valid_pointer memory object(Ptrofs.unsigned offset)=true).
  { intros memory current[NORMAL HELD].
    destruct(gateway_reference_capture_member _ _ _ _ _ _ _ HELD
      ltac:(unfold captures;apply in_or_app;right;left;reflexivity))as[[place OWNED]REST].
    assert(ROOT:gateway_rooted(python current)(objects current)(Vptr object offset)).
    { eapply gateway_reference_owned_rooted;[exact(proj1 HELD)|exact OWNED]. }
    destruct NORMAL as[[PYTHON[LIVE[BYTES[DICTS POINTERS]]]]REST_NORMAL].
    destruct(POINTERS _ ROOT)as(actual&position&SAME&VALID);inversion SAME;subst;exact VALID. }
  assert(DISTINCT:stream_descriptor final_stream<>stream_control final_stream).
  { rewrite DESCRIPTOR,(gateway_eof_control_from_parser native stable base stream final_stream readonly original m1 w1 control
      INPUT CONTROL_READONLY CONTROL_LOAD);exact SEPARATE. }
  destruct(actual_exchange_successful_eof backend io native stable scoped thread_errno SCOPED_THREAD SCOPED_RECEIVE
    stream extra(gateway_eof_readonly readonly extra)allocation_before allocated environment
    (gateway_trailing_temps(stream_remaining final_stream)(gateway_parser_bound_temps(Vptr object offset)temporaries))
    final_stream object offset m1 w1 r1 value after next ALLOC STREAM EXTRA
    ltac:(unfold gateway_trailing_temps,gateway_parser_bound_temps;do 2(rewrite PTree.gso by discriminate);apply PTree.gss)
    WEAK DISTINCT READY NONNULL S1)
    as(p2&suffix&memory&current&final_temps&updated&observed&E2&P2&FINAL&TRANSPORT&RESULT&READ2&SEND2&EOF2&IO2&SUFFIX).
  assert(HELD:scope current)by(exact(proj2(proj1(proj1 FINAL)))).
  assert(WIRE:gateway_value_heap decimal_float(objects current)(Vptr object offset)wire).
  { pose proof(gateway_reference_capture_member _ _ _ _ _ _ _ HELD
      ltac:(unfold captures;apply in_or_app;right;left;reflexivity))as[OWNER[PRIVATE[DESTROY[WIRE SNAPSHOT]]]];exact WIRE. }
  assert(READ:gateway_received_bytes io(stream_descriptor initial)(p1++p2)=[]).
  { rewrite gateway_received_bytes_append,(gateway_quiet_received_empty io(stream_descriptor initial)p1 Q1).
    rewrite<-DESCRIPTOR;exact READ2. }
  exists final,wire,ticket,object,offset,(p1++p2),suffix,memory,current,final_temps,updated,observed.
  split;[reflexivity|]. split;[rewrite E1,E2,app_assoc;reflexivity|]. split.
  - eapply gateway_steps_append;[exact P1|exact P2].
  - split;[exact RESULT|]. split;[rewrite(gateway_transport_descriptor final_stream updated TRANSPORT);exact DESCRIPTOR|]. split.
    + exact(eq_trans(proj1(proj2(proj2(proj2(proj2 TRANSPORT)))))ZERO).
    + split.
      * split;[exact(proj1(proj1(proj1 FINAL)))|exact(proj2(proj1 FINAL))].
      * split;[exact HELD|]. split;[exact WIRE|]. split.
        -- rewrite gateway_received_bytes_append,READ,app_nil_r;exact FRAMING.
        -- split;[exact READ|]. split.
           ++ rewrite gateway_sent_bytes_append,(gateway_quiet_sent_empty io(stream_descriptor initial)p1 Q1).
              rewrite<-DESCRIPTOR;exact SEND2.
           ++ split;[apply in_or_app;right;exact EOF2|].
              split;[rewrite<-DESCRIPTOR;exact IO2|exact SUFFIX].
Qed.
End ParserEOF.
