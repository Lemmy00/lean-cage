(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: Trailing payload bytes force the actual caller's NULL error result. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From HostGateway Require Import GatewaySource GatewayMachine GatewayFailurePaths GatewayNullReset GatewayIgnoredFailure
  GatewayExchangeTransport GatewayResponseReturn GatewayParserReturn.
Import ListNotations.

Definition exchange_trailing_error:=match exchange_trailing_test with Sifthenelse _ first _=>first|_=>Sskip end.

Lemma actual_null_result_eof {World Event}(backend:gateway_backend World Event)ge environment temporaries memory:
  temporaries!_result=Some Vnullptr->
  gateway_failure_result backend ge(State f_host_exchange(exchange_transport_after 7)Kstop environment temporaries memory).
Proof.
  intro NULL.
  response_denied_route.
  response_denied_branch false Vnullptr.
  response_denied_route.
  intros before world events value after next RUN.
  eapply gateway_actual_reset_null with(protected:=_result);[|exact RUN].
  left;split;[repeat eexists;reflexivity|]. split.
  - exact NULL.
  - split;[reflexivity|left;exact(proj2(proj2(proj2 actual_exchange_transport_null_shapes)))].
Qed.

Ltac trailing_error_ignore:=lazymatch goal with
  |-gateway_failure_result ?backend ?ge(State ?function(Scall None ?expression ?arguments)?continuation ?environment ?temporaries ?memory)=>
    apply gateway_failure_ignored_call;let ignored:=fresh "ignored" in intro ignored;
    eapply gateway_failure_edge with(target:=State function Sskip continuation environment temporaries memory);
      [cbn;tauto|intros;apply unchanged_store_edge,edge_returnstate|]
  end.
Ltac trailing_error_arbitrary_set:=lazymatch goal with
  |-gateway_failure_result ?backend ?ge(State ?function(Sset ?identifier ?expression)?continuation ?environment ?temporaries ?memory)=>
    apply gateway_failure_arbitrary_set;intro assigned
  end.

Lemma actual_trailing_error_failure {World Event}(backend:gateway_backend World Event)ge environment temporaries memory:
  gateway_failure_result backend ge(State f_host_exchange exchange_trailing_error
    (Kseq(exchange_transport_after 7)Kstop)environment temporaries memory).
Proof.
  unfold exchange_trailing_error.
  repeat response_denied_route.
  trailing_error_arbitrary_set.
  repeat response_denied_route.
  trailing_error_ignore.
  repeat response_denied_route.
  trailing_error_ignore.
  repeat response_denied_route.
  response_denied_set_as Vnullptr.
  eapply gateway_failure_edge with(target:=State f_host_exchange(exchange_transport_after 7)Kstop environment
    (PTree.set _result Vnullptr(PTree.set _t'63 assigned temporaries))memory);
    [cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  apply actual_null_result_eof;apply PTree.gss.
Qed.
