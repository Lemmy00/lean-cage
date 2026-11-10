(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A failed field transfer exits the same payload loop before response use. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPure GatewayReturns GatewayFailurePaths
  GatewayHeaderTransfer GatewayExchangeTransport GatewayExchangeDenied.
Import ListNotations.
Open Scope Z_scope.

Definition payload_phase:=exchange_transport_at 0.
Definition payload_loop:=match payload_phase with Ssequence _ rest=>rest|_=>Sskip end.
Definition payload_iteration:=match payload_loop with Sloop first _=>first|_=>Sskip end.
Definition payload_increment:=match payload_loop with Sloop _ rest=>rest|_=>Sskip end.
Definition payload_guard:=match payload_iteration with Ssequence first _=>first|_=>Sskip end.
Definition payload_body:=match payload_iteration with Ssequence _ rest=>rest|_=>Sskip end.
Definition payload_guard_select:=match payload_guard with Ssequence first _=>first|_=>Sskip end.
Definition payload_guard_test:=match payload_guard with Ssequence _ rest=>rest|_=>Sskip end.
Definition payload_loop_cont:=Kseq(exchange_transport_after 1)Kstop.
Definition payload_iteration_cont:=Kloop1 payload_iteration payload_increment payload_loop_cont.

Ltac payload_failed_same sink:=eapply gateway_failure_edge with(target:=sink);[cbn;tauto| |].

Section Failed.
Context {World Event}(backend:gateway_backend World Event)(ge:Clight.genv).
Variables(environment:env)(temporaries:temp_env)(memory:mem).
Hypothesis FAILED:temporaries!_failed=Some(Vint(Int.neg Int.one)).


Theorem actual_failed_payload_loop:
  gateway_failure_result backend ge(State f_host_exchange payload_loop payload_loop_cont environment temporaries memory).
Proof.
  payload_failed_same(State f_host_exchange payload_iteration payload_iteration_cont environment temporaries memory);
    [intros;apply unchanged_store_edge,edge_loop|].
  payload_failed_same(State f_host_exchange payload_guard(Kseq payload_body payload_iteration_cont)environment temporaries memory);
    [intros;apply unchanged_store_edge,edge_seq|].
  payload_failed_same(State f_host_exchange payload_guard_select
    (Kseq payload_guard_test(Kseq payload_body payload_iteration_cont))environment temporaries memory);
    [intros;apply unchanged_store_edge,edge_seq|].
  payload_failed_same(State f_host_exchange(Sset _t'31(Econst_int Int.zero tint))
    (Kseq payload_guard_test(Kseq payload_body payload_iteration_cont))environment temporaries memory).
  - intros;apply certified_if_edge with(v:=Vint Int.zero)(b:=false);
      [apply old_expression_value;WriteAll.expression|reflexivity].
  - payload_failed_same(State f_host_exchange Sskip(Kseq payload_guard_test(Kseq payload_body payload_iteration_cont))
      environment(PTree.set _t'31(Vint Int.zero)temporaries)memory);
      [intros;apply certified_set_edge,old_expression_value;constructor|].
    payload_failed_same(State f_host_exchange payload_guard_test(Kseq payload_body payload_iteration_cont)
      environment(PTree.set _t'31(Vint Int.zero)temporaries)memory);
      [intros;apply unchanged_store_edge,edge_skip_seq|].
    payload_failed_same(State f_host_exchange Sbreak(Kseq payload_body payload_iteration_cont)
      environment(PTree.set _t'31(Vint Int.zero)temporaries)memory).
    + intros;apply certified_if_edge with(v:=Vint Int.zero)(b:=false);
        [apply old_expression_value;WriteAll.expression|reflexivity].
    + payload_failed_same(State f_host_exchange Sbreak payload_iteration_cont
        environment(PTree.set _t'31(Vint Int.zero)temporaries)memory);
        [intros;apply unchanged_store_edge,edge_break_seq|].
      payload_failed_same(State f_host_exchange Sskip payload_loop_cont
        environment(PTree.set _t'31(Vint Int.zero)temporaries)memory);
        [intros;apply unchanged_store_edge,edge_break_loop1|].
      payload_failed_same(State f_host_exchange(exchange_transport_after 1)Kstop
        environment(PTree.set _t'31(Vint Int.zero)temporaries)memory);
        [intros;apply unchanged_store_edge,edge_skip_seq|].
      apply actual_failed_exchange_suffix;rewrite PTree.gso by discriminate;exact FAILED.
Qed.

End Failed.

Section FailedEntry.
Context {World Event}(backend:gateway_backend World Event)(ge:Clight.genv).
Variables(environment:env)(temporaries:temp_env)(memory:mem).
Hypothesis FAILED:temporaries!_failed=Some(Vint(Int.neg Int.one)).

Theorem actual_failed_payload_entry:
  gateway_failure_result backend ge(State f_host_exchange header_transfer_after Kstop environment temporaries memory).
Proof.
  payload_failed_same(State f_host_exchange payload_phase payload_loop_cont environment temporaries memory);
    [intros;apply unchanged_store_edge,edge_seq|].
  payload_failed_same(State f_host_exchange(Sset _index__1(Econst_int Int.zero tint))(Kseq payload_loop payload_loop_cont)
    environment temporaries memory);[intros;apply unchanged_store_edge,edge_seq|].
  payload_failed_same(State f_host_exchange Sskip(Kseq payload_loop payload_loop_cont)
    environment(PTree.set _index__1(Vint Int.zero)temporaries)memory);
    [intros;apply certified_set_edge,old_expression_value;constructor|].
  payload_failed_same(State f_host_exchange payload_loop payload_loop_cont
    environment(PTree.set _index__1(Vint Int.zero)temporaries)memory);
    [intros;apply unchanged_store_edge,edge_skip_seq|].
  apply actual_failed_payload_loop;rewrite PTree.gso by discriminate;exact FAILED.
Qed.
End FailedEntry.
