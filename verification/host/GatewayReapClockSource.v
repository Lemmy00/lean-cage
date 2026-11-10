(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The first reap wait follows the same actual clock return. *)
From Stdlib Require Import List.
From compcert Require Import Maps Integers AST Values Memory Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewayContexts GatewayReturnMarker GatewayReapSource
  GatewayReapABI GatewayMemoryPrefixes GatewayFramedRuntime GatewayExchangeABI.
Import ListNotations.

Definition reap_clock_returned(temporaries:temp_env)(returned:val):temp_env:=PTree.set _t'1 returned temporaries.
Definition reap_began_temporaries(temporaries:temp_env)(returned:val):temp_env:=
  PTree.set _began returned(reap_clock_returned temporaries returned).

Theorem actual_reap_after_clock_wait_prefix {World Event}(backend:gateway_backend World Event)ge property
    (CLOSED:gateway_ambient_closed backend property)environment temporaries returned memory status child:
  environment!_status=Some(status,tint)->environment!_waitpid=None->
  gateway_function_binding ge _waitpid gateway_waitpid_definition->temporaries!_child=Some(Vint child)->
  gateway_memory_prefix backend ge
    (Callstate gateway_waitpid_definition[Vint child;Vptr status Ptrofs.zero;Vint Int.one]
      (reap_wait_cont environment(reap_began_temporaries temporaries returned))memory)property property
    (State f_host_engine_reap Sskip reap_clock_after environment(reap_clock_returned temporaries returned)memory).
Proof.
  intros STATUS LOCAL FUNCTION CHILD.
  eapply gateway_memory_same with(following:=State f_host_engine_reap reap_began_bind(Kseq reap_after_began Kstop)
    environment(reap_clock_returned temporaries returned)memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_memory_same with(following:=State f_host_engine_reap Sskip(Kseq reap_after_began Kstop)
    environment(reap_began_temporaries temporaries returned)memory);
    [exact CLOSED|cbn;tauto| |].
  - intros before world READY;apply certified_set_edge,old_expression_value,value_temp;apply PTree.gss.
  - eapply gateway_memory_same with(following:=State f_host_engine_reap reap_after_began Kstop
      environment(reap_began_temporaries temporaries returned)memory);
      [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
    eapply gateway_memory_same with(following:=State f_host_engine_reap reap_main_loop reap_loop_cont
      environment(reap_began_temporaries temporaries returned)memory);
      [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
    apply actual_reap_loop_wait_prefix;[exact CLOSED|exact STATUS|exact LOCAL|exact FUNCTION|].
    unfold reap_began_temporaries,reap_clock_returned;rewrite !PTree.gso by discriminate;exact CHILD.
Qed.

Theorem actual_reap_clock_return_before_wait {World Event}(backend:gateway_backend World Event)ge
    environment temporaries before world events arguments selected_environment selected_temporaries after next:
  gateway_steps backend ge
    (gateway_live(Callstate(Internal f_host_now)[](reap_clock_cont environment temporaries)before)world)events
    (gateway_live(Callstate gateway_waitpid_definition arguments
      (reap_wait_cont selected_environment selected_temporaries)after)next)->
  exists prefix rest returned memory current,
    events=prefix++rest /\
    gateway_steps backend ge(gateway_live(Callstate(Internal f_host_now)[]Kstop before)world)prefix
      (gateway_live(Returnstate returned Kstop memory)current) /\
    gateway_steps backend ge(gateway_live(Returnstate returned(reap_clock_cont environment temporaries)memory)current)rest
      (gateway_live(Callstate gateway_waitpid_definition arguments
        (reap_wait_cont selected_environment selected_temporaries)after)next).
Proof.
  intro RUN;eapply gateway_marked_return_cut with(destination:=Some _t'1).
  - reflexivity.
  - left;reflexivity.
  - cbn[gateway_continuation gateway_return_marker reap_wait_cont reap_wait_after reap_iteration_cont reap_loop_cont].
    intuition discriminate.
  - exact RUN.
Qed.
