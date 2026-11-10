(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: The original successful caller forces real EOF readiness success. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From HostGateway Require Import GatewaySource GatewayMachine GatewayFailurePaths GatewayNullReset GatewayReturns
  GatewayReturnTypes GatewayIgnoredFailure GatewayResponseReturn GatewayTrailingError GatewayExchangeTransport GatewayEOFSource.
Import ListNotations.

Definition exchange_eof_ready_error:=match exchange_eof_ready_test with Sifthenelse _ first _=>first|_=>Sskip end.

Lemma actual_eof_null_break {World Event}(backend:gateway_backend World Event)ge environment temporaries memory:
  temporaries!_result=Some Vnullptr->
  gateway_failure_result backend ge(State f_host_exchange Sbreak
    (Kseq exchange_eof_after_ready exchange_eof_iteration_cont)environment temporaries memory).
Proof.
  intro NULL.
  eapply gateway_failure_edge with(target:=State f_host_exchange Sbreak exchange_eof_iteration_cont environment temporaries memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_break_seq|].
  eapply gateway_failure_edge with(target:=State f_host_exchange Sskip exchange_eof_cont environment temporaries memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_break_loop1|].
  eapply gateway_failure_edge with(target:=State f_host_exchange exchange_cleanup_phase Kstop environment temporaries memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  intros before world events value after next RUN.
  eapply gateway_actual_reset_null with(protected:=_result);[|exact RUN].
  left;split;[repeat eexists;reflexivity|]. split;[exact NULL|].
  split;[reflexivity|left;exact(proj2(proj2(proj2 actual_exchange_transport_null_shapes)))].
Qed.

Lemma actual_failed_eof_ready_return {World Event}(backend:gateway_backend World Event)ge environment temporaries memory:
  gateway_failure_result backend ge(Returnstate(Vint(Int.neg Int.one))(exchange_eof_ready_cont environment temporaries)memory).
Proof.
  eapply gateway_failure_edge with(target:=State f_host_exchange Sskip exchange_eof_ready_after environment
    (PTree.set _t'46(Vint(Int.neg Int.one))temporaries)memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_returnstate|].
  unfold exchange_eof_ready_after.
  repeat response_denied_route.
  response_denied_branch true(Vint(Int.neg Int.one)).
  repeat response_denied_route.
  trailing_error_ignore.
  repeat response_denied_route.
  response_denied_set_as Vnullptr.
  repeat response_denied_route.
  apply actual_eof_null_break;WriteAll.lookup.
Qed.

Lemma actual_undefined_eof_ready_return ge environment temporaries memory:
  gateway_blocked_path ge(Returnstate Vundef(exchange_eof_ready_cont environment temporaries)memory).
Proof.
  eapply gateway_blocked_next with(next:=State f_host_exchange Sskip exchange_eof_ready_after environment
    (PTree.set _t'46 Vundef temporaries)memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_returnstate|].
  eapply gateway_blocked_next with(next:=State f_host_exchange exchange_eof_ready_test
    (Kseq exchange_eof_after_ready exchange_eof_iteration_cont)environment(PTree.set _t'46 Vundef temporaries)memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  apply gateway_blocked_at.
  - cbn;tauto.
  - intros;discriminate.
  - intros before trace target STEP;inversion STEP;subst;
      try match goal with BAD:_=_\/_=_|-_=>destruct BAD;discriminate end.
    match goal with VALUE:eval_expr _ _ _ _(Etempvar ?identifier ?ty)_|-_=>
      assert(LOOK:(PTree.set _t'46 Vundef temporaries)!identifier=Some Vundef)by WriteAll.lookup;
      pose proof(evaluated_unique _ _ _ _ _ _
        (value_temp _ _ _ _ identifier ty Vundef LOOK)_ VALUE)as SAME;subst end.
    discriminate.
Qed.

Theorem actual_successful_eof_ready_return {World Event}(backend:gateway_backend World Event)ge
    environment temporaries before world events returned value after next:
  gateway_int_return_value returned->value<>Vnullptr->
  gateway_steps backend ge(gateway_live(Returnstate returned(exchange_eof_ready_cont environment temporaries)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->returned=Vint Int.zero.
Proof.
  intros[UNDEFINED|[ZERO|FAILED]]NONNULL RUN;[subst returned|exact ZERO|subst returned].
  - exfalso;eapply gateway_blocked_cannot_return;[apply actual_undefined_eof_ready_return|exact RUN].
  - exfalso;apply NONNULL;exact(actual_failed_eof_ready_return backend ge environment temporaries before
      before world events value after next RUN).
Qed.
