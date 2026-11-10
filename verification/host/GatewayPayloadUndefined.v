(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Undefined transfer results cannot pass the actual payload guard. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPure GatewayReturns GatewayPayloadControl
  GatewayHeaderTransfer GatewayExchangeTransport.
Import ListNotations.

Lemma payload_undefined_guard ge environment temporaries memory:
  temporaries!_failed=Some Vundef->
  gateway_blocked_path ge(State f_host_exchange payload_guard_select
    (Kseq payload_guard_test(Kseq payload_body payload_iteration_cont))environment temporaries memory).
Proof.
  intro UNDEFINED;apply gateway_blocked_at.
  - cbn;tauto.
  - intros;discriminate.
  - intros available trace target STEP;inversion STEP;subst;
      try match goal with BAD:_=_\/_=_|-_=>destruct BAD;discriminate end.
    all:match goal with VALUE:eval_expr _ _ _ _(Eunop Onotbool _ _)_|-_=>inversion VALUE;subst end.
    all:try match goal with BAD:eval_lvalue _ _ _ _(Eunop _ _ _)_ _ _|-_=>inversion BAD end.
    all:match goal with VALUE:eval_expr _ _ _ _(Etempvar ?identifier ?ty)_|-_=>
      assert(LOOK:temporaries!identifier=Some Vundef)by exact UNDEFINED;
      pose proof(evaluated_unique _ _ _ _ _ _(value_temp _ _ _ _ identifier ty Vundef LOOK)_ VALUE)as SAME;subst end.
    all:discriminate.
Qed.

Lemma actual_undefined_payload_loop ge environment temporaries memory:
  temporaries!_failed=Some Vundef->
  gateway_blocked_path ge(State f_host_exchange payload_loop payload_loop_cont environment temporaries memory).
Proof.
  intro UNDEFINED.
  eapply gateway_blocked_next with(next:=State f_host_exchange payload_iteration payload_iteration_cont environment temporaries memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_loop|].
  eapply gateway_blocked_next with(next:=State f_host_exchange payload_guard(Kseq payload_body payload_iteration_cont)
    environment temporaries memory);[cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_blocked_next with(next:=State f_host_exchange payload_guard_select
    (Kseq payload_guard_test(Kseq payload_body payload_iteration_cont))environment temporaries memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  apply payload_undefined_guard;exact UNDEFINED.
Qed.

Theorem actual_undefined_payload_entry ge environment temporaries memory:
  temporaries!_failed=Some Vundef->
  gateway_blocked_path ge(State f_host_exchange header_transfer_after Kstop environment temporaries memory).
Proof.
  intro UNDEFINED.
  eapply gateway_blocked_next with(next:=State f_host_exchange payload_phase payload_loop_cont environment temporaries memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_blocked_next with(next:=State f_host_exchange(Sset _index__1(Econst_int Int.zero tint))
    (Kseq payload_loop payload_loop_cont)environment temporaries memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_blocked_next with(next:=State f_host_exchange Sskip(Kseq payload_loop payload_loop_cont)
    environment(PTree.set _index__1(Vint Int.zero)temporaries)memory);
    [cbn;tauto|intros;apply certified_set_edge,old_expression_value;constructor|].
  eapply gateway_blocked_next with(next:=State f_host_exchange payload_loop payload_loop_cont
    environment(PTree.set _index__1(Vint Int.zero)temporaries)memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  apply actual_undefined_payload_loop;rewrite PTree.gso by discriminate;exact UNDEFINED.
Qed.
