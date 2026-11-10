(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual constructor continuation establishes the real local
   receiver and zero index before any recursive child call. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Clight.
Require Import CallContexts.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayValueEntry GatewayContainerLoopSource
  GatewayContainerAllocation GatewayContainerSetup GatewaySourceSegments GatewayReferenceLedger GatewayReferencePlaces
  GatewayReferenceStackBound GatewayFramedRuntime.
Import ListNotations.

Theorem gateway_reference_actual_container_setup {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    context ledger final container slots parameters object offset before world events value after next
    (property:mem->World->Prop):
  gateway_ambient_closed backend property->
  (forall memory current,property memory current->Mem.weak_valid_pointer memory object(Ptrofs.unsigned offset)=true)->
  property before world->gateway_reference_stack_bound context ledger->
  gateway_reference_apply(gateway_reference_mint(gateway_reference_temporary(gateway_reference_depth context)_container)(Vptr object offset))
    (gateway_reference_valid ledger)=gateway_reference_valid final->
  gateway_steps backend ge
    (gateway_live(Returnstate(Vptr object offset)(gateway_container_constructor_cont container slots parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists prefix suffix memory current,
    events=prefix++suffix /\Forall(fun event=>event=gateway_source E0 \/event=gateway_ambient)prefix /\
    gateway_steps backend ge
      (gateway_live(Returnstate(Vptr object offset)(gateway_container_constructor_cont container slots parameters)before)world)prefix
      (gateway_live(State f_host_value gateway_container_loop gateway_container_loop_cont(gateway_value_environment slots)
        (gateway_container_setup_parameters container object offset parameters)memory)current) /\
    property memory current /\gateway_reference_source_bound ge
      (plug_state(State f_host_value gateway_container_loop gateway_container_loop_cont(gateway_value_environment slots)
        (gateway_container_setup_parameters container object offset parameters)memory)context)final /\
    (gateway_container_setup_parameters container object offset parameters)!_container=Some(Vptr object offset) /\
    (gateway_container_setup_parameters container object offset parameters)!_index__1=Some(Vlong Int64.zero) /\
    gateway_steps backend ge
      (gateway_live(State f_host_value gateway_container_loop gateway_container_loop_cont(gateway_value_environment slots)
        (gateway_container_setup_parameters container object offset parameters)memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros CLOSED POINTER INPUT STACK MINT RUN.
  pose proof(gateway_container_setup_segment backend ge property container slots parameters object offset before CLOSED POINTER)as SEGMENT.
  destruct(gateway_source_segment_cut backend ge _ _ _ _ SEGMENT before world events value after next INPUT RUN)
    as(prefix &suffix &memory &current &EVENTS &QUIET &PREFIX &READY &REST).
  exists prefix,suffix,memory,current;split;[exact EVENTS|]. split;[exact QUIET|]. split;[exact PREFIX|]. split;[exact READY|]. split.
  - eapply gateway_reference_mint_local_bound;[reflexivity|exact STACK| |exact MINT].
    unfold gateway_container_setup_parameters;rewrite PTree.gso by discriminate;apply PTree.gss.
  - split;[unfold gateway_container_setup_parameters;rewrite PTree.gso by discriminate;apply PTree.gss|].
    split;[apply PTree.gss|exact REST].
Qed.
