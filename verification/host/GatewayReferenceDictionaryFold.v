(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Finite actual dictionary loops compose both strictly shorter children;
   each returned field and byte segment belongs to that same source execution. *)
From Stdlib Require Import ZArith List Lia Arith Wf_nat.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine CallContexts.
From HostGateway Require Import GatewaySource GatewayImport GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayObjectDiscipline GatewayObjectThreads
  GatewayValue GatewayValueEntry GatewayValueContext GatewayValueStack GatewayContainerLength GatewayContainerGuards GatewayContainerMemory GatewayContainerLoopSource
  GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting GatewayReferenceThreads GatewayReferenceStackBound GatewayReferenceLoopLedger GatewayReferenceNormalForm
  GatewayReferenceDecoded GatewayReferenceParseResult GatewayReferenceParserInputs GatewayReferenceValueProperties GatewayReferenceGraphCapture GatewayReferenceContainerScope
  GatewayReferenceContainerContext GatewayReferenceSnapshotInputs GatewayReferenceAncestors GatewayReferenceDictionaryFirstInduction GatewayReferenceDictionaryValueResume GatewayReferenceDictionaryEnd GatewayObjectInstances
  GatewayReferenceArrayFold GatewayArrayBounds GatewayContainerABI GatewayContainerEncoding GatewayScalarDecoding GatewayReadonly GatewayPathEvents GatewayObjectEvents GatewayThreadRuntime GatewayStreamInterface.
Import ListNotations.
Local Close Scope lean_scope.

Section DictionaryFold.
Context {World Event}(backend:gateway_backend World Event)
  (python:World->python_world)(objects:World->gateway_object_heap)(decimal_float:list Z->Floats.float->Prop)
  (detached:Values.val->Memory.mem->World->Prop)(io:Event->option gateway_native_io)
  (stable:World->block->Z->Prop)(thread_errno:World->int)(heap_allocation:block->Z->Prop).
Let native:=fun current candidate=>gateway_native_private(python current)candidate.
Let base:=gateway_python_discipline python objects detached.
Context(runtime:gateway_thread_runtime backend io native stable base thread_errno)
  (reference_threads:gateway_reference_thread_contract backend native stable base heap_allocation python objects)
  (containers:gateway_container_runtime backend python objects)(abi:gateway_container_abi_runtime backend python objects)
  (references:gateway_reference_runtime backend python objects)
  (instances:gateway_instance_runtime backend(Clight.globalenv prog)python objects(fun _ _ _=>Logic.False))
  (projection:gateway_direct_io_projection backend io).

Theorem gateway_reference_actual_dictionary_fold mode_symbol run_limit
    (children:gateway_reference_short_parser backend python objects decimal_float detached io stable mode_symbol run_limit)
    context older ledger held parent_ticket parent parent_offset fields entries parent_initial slots parameters depth index size
    stream_block stream_offset initial readonly original before world events value after next:
  is_call_cont context->gateway_reference_stack_bound context older->gateway_reference_ledger_well_formed ledger->
  gateway_reference_loop_entries context older ledger parent_ticket(Vptr parent parent_offset)->
  (gateway_reference_next older<=parent_ticket)%nat->gateway_reference_graphs_only held->
  gateway_reference_snapshots_avoid held(Vptr parent parent_offset)->
  gateway_object_values parent_initial(Vptr parent parent_offset)=Some(gateway_dict_object fields)->
  gateway_dictionary_heap decimal_float parent_initial fields entries->
  (forall pointer,In pointer(gateway_dictionary_children fields)->~gateway_object_reachable parent_initial pointer(Vptr parent parent_offset))->
  (forall pointer,gateway_reference_mutable_target held pointer->~gateway_object_reachable parent_initial(Vptr parent parent_offset)pointer)->
  parameters!_container=Some(Vptr parent parent_offset)->parameters!_stream=Some(Vptr stream_block stream_offset)->
  parameters!_depth=Some(Vint depth)->parameters!_index__1=Some(Vlong index)->
  Z.of_nat(length entries)=Int64.unsigned index->Int64.unsigned index<=Int64.unsigned size->
  gateway_unicode_strict_mode original(Vptr mode_symbol Ptrofs.zero)->
  (forall object position,gateway_scalar_mode_region mode_symbol object position->readonly object position)->
  gateway_reference_counted_context python objects decimal_float detached stable ledger
    (held++[gateway_reference_graph_capture parent_ticket(Vptr parent parent_offset)
      (LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields entries))parent_initial])
    gateway_container_object slots stream_block stream_offset initial readonly original size before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_value gateway_container_loop gateway_container_loop_cont(gateway_value_environment slots)parameters before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->(length events<=run_limit)%nat->
  exists final final_stream remaining chunks,
    gateway_reference_decoded python objects decimal_float(Clight.globalenv prog)context older held
      (LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields(entries++remaining)))parent_ticket value final after next /\
    gateway_value_context native stable base stream_block stream_offset final_stream readonly original after next /\
    (forall object position,readonly object position->native next object) /\stream_descriptor final_stream=stream_descriptor initial /\
    length(entries++remaining)=Z.to_nat(Int64.unsigned size) /\
    Forall2(fun field bytes=>exists key_bytes value_bytes,bytes=key_bytes++value_bytes /\
      gateway_response_frame(LeanCage_Host_GatewayResponseCode_Subject_value(Datatypes.fst field))key_bytes /\
      gateway_response_frame(LeanCage_Host_GatewayResponseCode_Subject_value(Datatypes.snd field))value_bytes)remaining chunks /\
    gateway_received_bytes io(stream_descriptor initial)events=concat chunks.
Proof.
  remember(length events)as measure eqn:MEASURE.
  revert ledger fields entries parent_initial parameters index initial before world events MEASURE.
  induction measure using lt_wf_ind;intros ledger fields entries parent_initial parameters index initial before world events MEASURE
    CALL STACK FORMED ENTRIES FRESH GRAPHS OUTSIDE LOOKUP DICTIONARY ACYCLIC EXCLUDED PARENT STREAM DEPTH INDEX LENGTH INDEX_BOUND MODE MODE_SUBSET INPUT RUN NONNULL LIMIT.
  assert(EVENT_LIMIT:(length events<=run_limit)%nat)by lia.
  destruct(Int64.ltu index size)eqn:LESS.
  - set(parent_capture:=gateway_reference_graph_capture parent_ticket(Vptr parent parent_offset)
      (LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields entries))parent_initial).
    assert(ALL_GRAPHS:gateway_reference_graphs_only(held++[parent_capture])).
    { apply gateway_reference_graphs_only_append;[exact GRAPHS|eexists;eexists;reflexivity]. }
    destruct(gateway_reference_actual_dictionary_first_induction backend python objects decimal_float detached io stable thread_errno heap_allocation
      runtime reference_threads mode_symbol run_limit context older ledger(held++[parent_capture])parent_ticket parent parent_offset slots parameters depth index size
      stream_block stream_offset initial readonly original before world events value after next children FORMED ALL_GRAPHS MODE MODE_SUBSET EVENT_LIMIT
      STACK ENTRIES PARENT STREAM DEPTH INDEX LESS INPUT RUN NONNULL)
      as(called_parameters &prefix &reading &suffix &child_before &child_world &child &child_after &child_next &EVENTS &QUIET &SHORT &
        CALLED_PARENT &CALLED_STREAM &CALLED_DEPTH &CALLED_INDEX &PREFIX &CHILD_RUN &CHILD_NONNULL &REST &CALLED &CHILD_STACK &CHILD_BOUND &CHILD_CONTEXT &CHILD_NATIVE &PARSED).
    assert(SUFFIX_LIMIT:(length suffix<=run_limit)%nat)by(rewrite EVENTS,!length_app in EVENT_LIMIT;lia).
    destruct(gateway_reference_actual_dictionary_value_resume backend python objects decimal_float detached io stable thread_errno heap_allocation
      runtime reference_threads containers abi references instances projection mode_symbol run_limit context older ledger held parent_ticket parent parent_offset
      fields entries parent_initial slots called_parameters depth index size stream_block stream_offset initial readonly original child_before child_world reading child child_after child_next
      suffix value after next children STACK FORMED ENTRIES GRAPHS OUTSIDE LOOKUP DICTIONARY ACYCLIC EXCLUDED CALLED_PARENT CALLED_STREAM CALLED_DEPTH CALLED_INDEX
      MODE MODE_SUBSET CALLED CHILD_RUN PARSED REST NONNULL SUFFIX_LIMIT)
      as(next_ledger &child_stream &key_value &child_value &key &key_offset &object &offset &characters &loop_parameters &source_tail &loop_events &loop_memory &loop_world &parent_snapshot &
        TAIL_EVENTS &TAIL_POSITIVE &KEY_FRAME &CHILD_FRAME &NEXT_FORMED &NEXT_ENTRIES &NEXT_PARENT &NEXT_STREAM &NEXT_DEPTH &NEXT_INDEX &LOOP_RUN &
        LOOP_READY &CHILD_DESCRIPTOR &NEXT_LOOKUP &NEXT_FIELDS &NEXT_ACYCLIC &NEXT_EXCLUDED).
    assert(LOOP_SHORT:(length loop_events<measure)%nat).
    { rewrite MEASURE,EVENTS,TAIL_EVENTS,!length_app;lia. }
    destruct(gateway_array_index_increment index size LESS)as[INCREMENT NEXT_BOUND].
    assert(NEXT_LENGTH:Z.of_nat(length(entries++[(key_value,child_value)]))=Int64.unsigned(Int64.add index Int64.one)).
    { rewrite length_app,Nat2Z.inj_add;cbn;rewrite LENGTH,INCREMENT;lia. }
    destruct(H(length loop_events)LOOP_SHORT next_ledger
      (fields++[{|gateway_dictionary_key:=Vptr key key_offset;gateway_dictionary_text:=characters;gateway_dictionary_value:=Vptr object offset|}])
      (entries++[(key_value,child_value)])parent_snapshot loop_parameters(Int64.add index Int64.one)child_stream loop_memory loop_world loop_events eq_refl
      CALL STACK NEXT_FORMED NEXT_ENTRIES FRESH GRAPHS OUTSIDE NEXT_LOOKUP NEXT_FIELDS NEXT_ACYCLIC NEXT_EXCLUDED
      NEXT_PARENT NEXT_STREAM NEXT_DEPTH NEXT_INDEX NEXT_LENGTH NEXT_BOUND MODE MODE_SUBSET LOOP_READY LOOP_RUN NONNULL ltac:(lia))
      as(final &final_stream &remaining &chunks &DECODED &FINAL_CONTEXT &FINAL_NATIVE &FINAL_DESCRIPTOR &COUNT &FRAMES &BYTES).
    exists final,final_stream,((key_value,child_value)::remaining),
      ((gateway_received_bytes io(stream_descriptor initial)reading++gateway_received_bytes io(stream_descriptor initial)source_tail)::chunks).
    assert(VALUES:(entries++[(key_value,child_value)])++remaining=entries++((key_value,child_value)::remaining))by(rewrite<-app_assoc;reflexivity).
    rewrite VALUES in DECODED,COUNT.
    split;[exact DECODED|]. split;[exact FINAL_CONTEXT|]. split;[exact FINAL_NATIVE|]. split;
      [rewrite FINAL_DESCRIPTOR;exact CHILD_DESCRIPTOR|]. split;[exact COUNT|]. split.
    + constructor;[exists(gateway_received_bytes io(stream_descriptor initial)reading),(gateway_received_bytes io(stream_descriptor initial)source_tail);
        exact(conj eq_refl(conj KEY_FRAME CHILD_FRAME))|exact FRAMES].
    + rewrite EVENTS,TAIL_EVENTS,!gateway_received_append,(gateway_quiet_received io(stream_descriptor initial)prefix QUIET);cbn.
      rewrite<-CHILD_DESCRIPTOR;rewrite BYTES;rewrite app_assoc;reflexivity.
  - assert(SAME:index=size)by(eapply gateway_array_index_exhausted;eassumption).
    destruct(gateway_reference_actual_dictionary_end backend python objects decimal_float detached io stable thread_errno heap_allocation
      runtime reference_threads context older ledger held parent_ticket parent parent_offset entries parent_initial slots parameters index size
      stream_block stream_offset initial readonly original before world events value after next CALL STACK FORMED ENTRIES FRESH
      ltac:(eapply gateway_reference_loop_result_free;eassumption)EXCLUDED PARENT INDEX LESS INPUT RUN)
      as[final[RETURNED[DECODED[FINAL_CONTEXT[FINAL_NATIVE EMPTY]]]]].
    exists final,initial,[],[];rewrite app_nil_r.
    split;[exact DECODED|]. split;[exact FINAL_CONTEXT|]. split;[exact FINAL_NATIVE|]. split;[reflexivity|]. split.
    + apply Nat2Z.inj;rewrite Z2Nat.id by(apply Int64.unsigned_range_2);rewrite LENGTH,SAME;reflexivity.
    + split;[constructor|exact EMPTY].
Qed.
End DictionaryFold.
