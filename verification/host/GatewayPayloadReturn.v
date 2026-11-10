(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Every successful original exchange derives each field-transfer return. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPure GatewayReturns GatewayFailurePaths
  GatewayReturnTypes GatewayPayloadControl GatewayPayloadUndefined.
Import ListNotations.

Definition payload_bind_failed:=match payload_body with Ssequence _ rest=>rest|_=>Sskip end.
Definition payload_transfer_cont environment temporaries:=Kcall(Some _t'32)f_host_exchange environment temporaries
  (Kseq payload_bind_failed payload_iteration_cont).
Definition payload_advanced_temps temporaries index:=PTree.set _index__1(Vint(Int.add index Int.one))temporaries.

Lemma actual_failed_payload_increment {World Event}(backend:gateway_backend World Event)ge
    environment temporaries memory index:
  temporaries!_failed=Some(Vint(Int.neg Int.one))->temporaries!_index__1=Some(Vint index)->
  gateway_failure_result backend ge(State f_host_exchange Sskip payload_iteration_cont environment temporaries memory).
Proof.
  intros FAILED INDEX.
  eapply gateway_failure_edge with(target:=State f_host_exchange payload_increment
    (Kloop2 payload_iteration payload_increment payload_loop_cont)environment temporaries memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_skip_loop1|].
  eapply gateway_failure_edge with(target:=State f_host_exchange Sskip
    (Kloop2 payload_iteration payload_increment payload_loop_cont)environment(payload_advanced_temps temporaries index)memory);
    [cbn;tauto|intros;apply certified_set_edge,old_expression_value;WriteAll.expression|].
  eapply gateway_failure_edge with(target:=State f_host_exchange payload_loop payload_loop_cont
    environment(payload_advanced_temps temporaries index)memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_skip_loop2|].
  apply actual_failed_payload_loop;unfold payload_advanced_temps;rewrite PTree.gso by discriminate;exact FAILED.
Qed.

Lemma actual_undefined_payload_increment ge environment temporaries memory index:
  temporaries!_failed=Some Vundef->temporaries!_index__1=Some(Vint index)->
  gateway_blocked_path ge(State f_host_exchange Sskip payload_iteration_cont environment temporaries memory).
Proof.
  intros UNDEFINED INDEX.
  eapply gateway_blocked_next with(next:=State f_host_exchange payload_increment
    (Kloop2 payload_iteration payload_increment payload_loop_cont)environment temporaries memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_skip_loop1|].
  eapply gateway_blocked_next with(next:=State f_host_exchange Sskip
    (Kloop2 payload_iteration payload_increment payload_loop_cont)environment(payload_advanced_temps temporaries index)memory);
    [cbn;tauto|intros;apply certified_set_edge,old_expression_value;WriteAll.expression|].
  eapply gateway_blocked_next with(next:=State f_host_exchange payload_loop payload_loop_cont
    environment(payload_advanced_temps temporaries index)memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_skip_loop2|].
  apply actual_undefined_payload_loop;unfold payload_advanced_temps;rewrite PTree.gso by discriminate;exact UNDEFINED.
Qed.

Lemma actual_payload_failed_return {World Event}(backend:gateway_backend World Event)ge
    environment temporaries memory index:
  temporaries!_index__1=Some(Vint index)->
  gateway_failure_result backend ge(Returnstate(Vint(Int.neg Int.one))(payload_transfer_cont environment temporaries)memory).
Proof.
  intro INDEX.
  eapply gateway_failure_edge with(target:=State f_host_exchange Sskip(Kseq payload_bind_failed payload_iteration_cont)
    environment(PTree.set _t'32(Vint(Int.neg Int.one))temporaries)memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_returnstate|].
  eapply gateway_failure_edge with(target:=State f_host_exchange payload_bind_failed payload_iteration_cont
    environment(PTree.set _t'32(Vint(Int.neg Int.one))temporaries)memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_failure_edge with(target:=State f_host_exchange Sskip payload_iteration_cont environment
    (PTree.set _failed(Vint(Int.neg Int.one))(PTree.set _t'32(Vint(Int.neg Int.one))temporaries))memory);
    [cbn;tauto|intros;apply certified_set_edge,old_expression_value;WriteAll.expression|].
  eapply actual_failed_payload_increment;[apply PTree.gss|rewrite !PTree.gso by discriminate;exact INDEX].
Qed.

Lemma actual_payload_undefined_return ge environment temporaries memory index:
  temporaries!_index__1=Some(Vint index)->
  gateway_blocked_path ge(Returnstate Vundef(payload_transfer_cont environment temporaries)memory).
Proof.
  intro INDEX.
  eapply gateway_blocked_next with(next:=State f_host_exchange Sskip(Kseq payload_bind_failed payload_iteration_cont)
    environment(PTree.set _t'32 Vundef temporaries)memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_returnstate|].
  eapply gateway_blocked_next with(next:=State f_host_exchange payload_bind_failed payload_iteration_cont
    environment(PTree.set _t'32 Vundef temporaries)memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_blocked_next with(next:=State f_host_exchange Sskip payload_iteration_cont environment
    (PTree.set _failed Vundef(PTree.set _t'32 Vundef temporaries))memory);
    [cbn;tauto|intros;apply certified_set_edge,old_expression_value;WriteAll.expression|].
  eapply actual_undefined_payload_increment;[apply PTree.gss|rewrite !PTree.gso by discriminate;exact INDEX].
Qed.

Theorem actual_successful_payload_return {World Event}(backend:gateway_backend World Event)ge
    environment temporaries index before world events returned value after next:
  temporaries!_index__1=Some(Vint index)->gateway_int_return_value returned->value<>Vnullptr->
  gateway_steps backend ge(gateway_live(Returnstate returned(payload_transfer_cont environment temporaries)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->returned=Vint Int.zero.
Proof.
  intros INDEX[UNDEFINED|[ZERO|FAILED]]NONNULL RUN;[subst returned|exact ZERO|subst returned].
  - exfalso;eapply gateway_blocked_cannot_return;[eapply actual_payload_undefined_return;exact INDEX|exact RUN].
  - exfalso;apply NONNULL;exact(actual_payload_failed_return backend ge environment temporaries before index INDEX
      before world events value after next RUN).
Qed.
