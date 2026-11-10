(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual recursive parsing and exact EOF precede the same original
   exchange cleanup. Neither a parser-success receipt nor EOF is an input. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayImport GatewayMachine GatewayContexts GatewayPython GatewayObjects GatewayReferences
  GatewayObjectDiscipline GatewayObjectConstants GatewayObjectThreads GatewayObjectInstances GatewayContainerABI
  GatewayValue GatewayValueEntry GatewayValueContext GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceHeld
  GatewayReferenceThreads GatewayReferenceContainerScope GatewayReferenceGraphCapture GatewayReferenceDecoded
  GatewayReferenceStackBound GatewayReferenceValueProperties GatewayReferenceParseResult GatewayReferenceReservations
  GatewayReferenceParserPool GatewayPermissionScopes GatewayPermissionEffects GatewayPermissionSurvival GatewayPermissionRuntime
  GatewayNativeMemory GatewayNoMemory GatewayObjectEvents GatewayScalarDecoding GatewayPathEvents
  GatewayStreamInterface GatewayThreadRuntime GatewayReadContext GatewayContainerEncoding GatewayExchangeTransport
  GatewayResponseParserSource GatewayResponseDecoded GatewayEOFNative GatewayEOFReferences GatewayEOFInputs GatewayParserEOF GatewayTransferMath.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Section DecodedEOF.
Context {World Event}(backend:gateway_backend World Event)
  (python:World->python_world)(objects:World->gateway_object_heap)(decimal_float:list Z->Floats.float->Prop)
  (detached:Values.val->Memory.mem->World->Prop)(io:Event->option gateway_native_io)
  (stable:World->block->Z->Prop)(thread_errno:World->int)(heap_allocation:block->Z->Prop).
Let native:=fun current object=>gateway_native_private(python current)object.
Let base:=gateway_python_discipline python objects detached.
Context(runtime:gateway_thread_runtime backend io native stable base thread_errno)
  (lifetimes:gateway_allocation_lifetime_runtime backend)
  (allocations:gateway_native_memory_runtime backend io native stable base heap_allocation)
  (constructors:gateway_objects_runtime backend python objects decimal_float)
  (references:gateway_reference_runtime backend python objects)
  (reference_threads:gateway_reference_thread_contract backend native stable base heap_allocation python objects)
  (containers:gateway_container_runtime backend python objects)(abi:gateway_container_abi_runtime backend python objects)
  (instances:gateway_instance_runtime backend(Clight.globalenv prog)python objects(fun _ _ _=>Logic.False))
  (errors:gateway_no_memory_runtime backend python)(projection:gateway_direct_io_projection backend io)
  (none_symbol mode_symbol:block)
  (constants:gateway_none_runtime python objects(Vptr none_symbol Ptrofs.zero))
  (NONE:Genv.find_symbol(Clight.globalenv prog)__Py_NoneStruct=Some none_symbol)
  (MODE_SYMBOL:Genv.find_symbol(Clight.globalenv prog)___stringlit_8=Some mode_symbol)
  (held_receive:gateway_eof_receive_runtime backend io native stable base)
  (receive_references:gateway_eof_reference_runtime backend native base python objects).

Theorem actual_exchange_decodes_then_eof allocation_before allocated environment temporaries ledger held reserved
    stream extra initial readonly original control before world events value after next:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  environment!_stream=Some(stream,Tstruct _host_stream noattr)->environment!_extra=Some(extra,tuchar)->
  (forall position,0<=position<1->readonly extra position)->Mem.range_perm original extra 0 1 Cur Writable->
  (forall position,readonly extra position->0<=position<1)->
  (forall position,4<=position<8->readonly stream position)->Mem.load Mint32 original stream 4=Some(Vint control)->
  stream_descriptor initial<>control->
  gateway_reference_ledger_well_formed ledger->
  gateway_reference_stack_bound(response_parser_cont environment temporaries)ledger->
  gateway_reference_held python objects decimal_float ledger held world->gateway_reference_graphs_only held->
  (forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count ledger pointer<=
    python_native_strong(python world)pointer)%nat)->
  gateway_unicode_strict_mode original(Vptr mode_symbol Ptrofs.zero)->
  (forall object position,gateway_scalar_mode_region mode_symbol object position->readonly object position)->
  gateway_value_context native stable base stream Ptrofs.zero initial readonly original before world->
  (forall object position,readonly object position->native world object)->value<>Vnullptr->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_value)(response_parser_arguments stream)
      (response_parser_cont environment temporaries)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists body parsed parser_memory parser_world final wire ticket object offset prefix suffix memory current final_temps updated observed,
    parsed=Vptr object offset /\events=prefix++suffix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(Internal f_host_value)(response_parser_arguments stream)Kstop before)world)body
      (gateway_live(Returnstate parsed Kstop parser_memory)parser_world) /\
    gateway_reference_reserved_parse_result python objects decimal_float detached io stable(Clight.globalenv prog)
      (response_parser_cont environment temporaries)ledger held reserved stream Ptrofs.zero initial readonly original
      body parsed parser_memory parser_world /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(Internal f_host_value)(response_parser_arguments stream)
        (response_parser_cont environment temporaries)before)world)prefix
      (gateway_live(State f_host_exchange exchange_cleanup_phase Kstop environment final_temps memory)current) /\
    final_temps!_result=Some parsed /\stream_descriptor updated=stream_descriptor initial /\stream_remaining updated=Int64.zero /\
    gateway_read_context native stable base None stream Ptrofs.zero updated extra Ptrofs.zero 1
      (gateway_eof_readonly readonly extra)memory current /\
    gateway_permission_frame(gateway_permission_region stream Ptrofs.zero readonly)before memory /\
    gateway_reference_scope python objects decimal_float final
      (held++[gateway_reference_graph_capture ticket parsed wire(objects parser_world)])current /\
    gateway_value_heap decimal_float(objects current)parsed wire /\
    gateway_response_frame(LeanCage_Host_GatewayResponseCode_Subject_value wire)
      (gateway_received_bytes io(stream_descriptor initial)prefix) /\
    In(gateway_primitive observed)prefix /\io observed=Some(gateway_native_receive(stream_descriptor initial)1 0[]) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange exchange_cleanup_phase Kstop environment final_temps memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros ALLOC STREAM EXTRA EXTRA_READONLY EXTRA_WRITABLE EXTRA_BOUND CONTROL_READONLY CONTROL_LOAD SEPARATE
    FORMED STACK HELD GRAPHS BUDGET MODE MODE_REGION INPUT READONLY NONNULL RUN.
  destruct(actual_exchange_decodes_response backend python objects decimal_float detached io stable thread_errno heap_allocation
    runtime lifetimes allocations constructors references reference_threads containers abi instances errors projection none_symbol mode_symbol constants NONE MODE_SYMBOL
    environment temporaries ledger held reserved stream initial readonly original before world events value after next
    FORMED STACK HELD GRAPHS BUDGET MODE MODE_REGION INPUT READONLY NONNULL RUN)
    as(body&caller_events&parsed&parser_memory&parser_world&E1&PARSED_NONNULL&BODY&RESERVED&PARSED&PARSER_PERMISSIONS&CALLER).
  destruct(actual_parsed_response_observes_eof backend io python objects stable detached thread_errno heap_allocation decimal_float
    runtime reference_threads held_receive receive_references allocation_before allocated environment temporaries ledger held
    stream extra initial readonly original body parsed parser_memory parser_world caller_events value after next control
    ALLOC STREAM EXTRA EXTRA_READONLY EXTRA_WRITABLE CONTROL_READONLY CONTROL_LOAD SEPARATE PARSED NONNULL CALLER)
    as(final&wire&ticket&object&offset&prefix&suffix&memory&current&final_temps&updated&observed
      &POINTER&E2&PREFIX&RESULT&DESCRIPTOR&ZERO&CONTEXT&SCOPE&VALUE&FRAMING&NO_READ&NO_SEND&SEEN&IO&SUFFIX).
  assert(WHOLE:gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_value)(response_parser_arguments stream)
      (response_parser_cont environment temporaries)before)world)(body++prefix)
    (gateway_live(State f_host_exchange exchange_cleanup_phase Kstop environment final_temps memory)current)).
  { eapply gateway_steps_append;
      [exact(gateway_plug_steps backend(Clight.globalenv prog)_ _ _(response_parser_cont environment temporaries)I BODY)|exact PREFIX]. }
  assert(PERMISSIONS:gateway_permission_frame(gateway_permission_region stream Ptrofs.zero readonly)before memory).
  { eapply gateway_survival_observed_permissions.
    - exact(gateway_actual_run_permissions backend(Clight.globalenv prog)lifetimes _ _ _ WHOLE).
    - intros candidate position[STREAM_CELL|READ].
      + destruct STREAM_CELL as[SAME RANGE];subst candidate;exists Cur,Writable.
        exact(gateway_read_stream_owned _ _ _ _ _ _ _ _(proj2(proj2(proj2(proj2 CONTEXT))))position RANGE).
      + destruct(Pos.eq_dec candidate extra)as[SAME|OTHER].
        * subst candidate;exists Cur,Writable.
          apply(gateway_read_data_owned _ _ _ _ _ _ _ _(proj2(proj2(proj2(proj2 CONTEXT))))position).
          change(0<=position<1);apply EXTRA_BOUND;exact READ.
        * exists Cur,Readable.
          apply(gateway_read_readonly_readable _ _ _ _ _ _ _ _(proj2(proj2(proj2(proj2 CONTEXT))))candidate position).
          split;assumption. }
  exists body,parsed,parser_memory,parser_world,final,wire,ticket,object,offset,(body++prefix),suffix,
    memory,current,final_temps,updated,observed.
  split;[exact POINTER|]. split;[rewrite E1,E2,app_assoc;reflexivity|]. split;[exact BODY|].
  split;[exact RESERVED|]. split.
  - exact WHOLE.
  - split;[exact RESULT|]. split;[exact DESCRIPTOR|]. split;[exact ZERO|]. split;[exact CONTEXT|].
    split;[exact PERMISSIONS|]. split;[exact SCOPE|]. split;[exact VALUE|]. split;[exact FRAMING|].
    split;[apply in_or_app;right;exact SEEN|]. split;[exact IO|exact SUFFIX].
Qed.
End DecodedEOF.
