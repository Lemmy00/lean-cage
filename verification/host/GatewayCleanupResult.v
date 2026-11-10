(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The original successful return is the same status-zero parsed
   object. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayMemoryPrefixes GatewayFramedRuntime GatewayReadonly
  GatewayReturns GatewayFailurePaths GatewayCleanupSource GatewayCleanupStatus.
Import ListNotations.

Theorem actual_cleanup_zero_return_path {World Event}(backend:gateway_backend World Event)ge property
    (CLOSED:gateway_ambient_closed backend property)environment temporaries memory word:
  Int64.eq word Int64.zero=true->
  gateway_memory_prefix backend ge
    (State f_host_exchange cleanup_final_return Kstop environment(cleanup_status_temps word temporaries)memory)property property
    (State f_host_exchange cleanup_status_test(Kseq cleanup_final_return Kstop)environment(cleanup_status_temps word temporaries)memory).
Proof.
  intro ZERO.
  eapply gateway_memory_same with(following:=State f_host_exchange Sskip(Kseq cleanup_final_return Kstop)
    environment(cleanup_status_temps word temporaries)memory);
    [exact CLOSED|cbn;tauto| |].
  - intros before world READY;apply certified_if_edge with(v:=Vint Int.zero)(b:=false).
    + apply old_expression_value,value_temp;unfold cleanup_status_temps,cleanup_status_flag;rewrite ZERO;apply PTree.gss.
    + reflexivity.
  - eapply gateway_memory_same with(following:=State f_host_exchange cleanup_final_return Kstop
      environment(cleanup_status_temps word temporaries)memory);
      [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|apply gateway_memory_identity].
Qed.

Theorem actual_exchange_successful_result {World Event}(backend:gateway_backend World Event)ge property
    (CLOSED:gateway_ambient_closed backend property)environment temporaries word object offset before world events value after next:
  temporaries!_result=Some(Vptr object offset)->temporaries!_status=Some(Vlong word)->
  (forall memory current,property memory current->Mem.weak_valid_pointer memory object(Ptrofs.unsigned offset)=true)->
  property before world->value<>Vnullptr->
  gateway_steps backend ge
    (gateway_live(State f_host_exchange cleanup_status_phase Kstop environment temporaries before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  word=Int64.zero /\value=Vptr object offset /\
  exists prefix suffix memory current,
    events=prefix++suffix /\Forall gateway_quiet_event prefix /\
    gateway_steps backend ge
      (gateway_live(State f_host_exchange cleanup_status_phase Kstop environment temporaries before)world)prefix
      (gateway_live(State f_host_exchange cleanup_final_return Kstop environment(cleanup_status_temps word temporaries)memory)current) /\
    property memory current /\
    gateway_steps backend ge
      (gateway_live(State f_host_exchange cleanup_final_return Kstop environment(cleanup_status_temps word temporaries)memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros RESULT STATUS POINTER READY NONNULL RUN.
  destruct(gateway_memory_prefix_cut backend ge _ _ _ _ before world events(Returnstate value Kstop after)next
    (actual_cleanup_status_select backend ge property CLOSED environment temporaries before word object offset RESULT STATUS POINTER)I READY RUN)
    as(p1&r1&m1&w1&E1&Q1&P1&C1&S1).
  cbn[gateway_replace_memory]in P1,S1.
  assert(ZERO:Int64.eq word Int64.zero=true).
  { destruct(Int64.eq word Int64.zero)eqn:CHOICE;[reflexivity|]. exfalso;apply NONNULL.
    assert(FAILURE:gateway_failure_result backend ge(State f_host_exchange cleanup_status_test(Kseq cleanup_final_return Kstop)
      environment(cleanup_status_temps word temporaries)m1)).
    { eapply gateway_failure_edge with(target:=State f_host_exchange cleanup_status_error(Kseq cleanup_final_return Kstop)
        environment(cleanup_status_temps word temporaries)m1);
        [cbn;tauto| |apply actual_cleanup_status_error].
      intros;apply certified_if_edge with(v:=Vint Int.one)(b:=true).
      - apply old_expression_value,value_temp;unfold cleanup_status_temps,cleanup_status_flag;rewrite CHOICE;apply PTree.gss.
      - reflexivity. }
    exact(FAILURE m1 w1 r1 value after next S1). }
  destruct(gateway_memory_prefix_cut backend ge _ _ _ _ m1 w1 r1(Returnstate value Kstop after)next
    (actual_cleanup_zero_return_path backend ge property CLOSED environment temporaries m1 word ZERO)I C1 S1)
    as(p2&suffix&memory&current&E2&Q2&P2&FINAL&SUFFIX).
  cbn[gateway_replace_memory]in P2,SUFFIX.
  assert(RETURNED:value=Vptr object offset).
  { eapply gateway_constant_return with(function:=f_host_exchange)(expression:=Etempvar _result(tptr(Tstruct __object noattr)))
      (value:=Vptr object offset)(converted:=Vptr object offset)
      (continuation:=Kstop)(environment:=environment)(temporaries:=cleanup_status_temps word temporaries);
      [reflexivity| |intros;reflexivity|exact SUFFIX].
    intro another;apply old_expression_value,value_temp;unfold cleanup_status_temps;rewrite PTree.gso by discriminate;exact RESULT. }
  split;[apply Int64.same_if_eq;exact ZERO|]. split;[exact RETURNED|].
  exists(p1++p2),suffix,memory,current.
  split;[rewrite E1,E2,app_assoc;reflexivity|]. split;[apply Forall_app;split;assumption|].
  split;[eapply gateway_steps_append;[exact P1|exact P2]|]. split;assumption.
Qed.
