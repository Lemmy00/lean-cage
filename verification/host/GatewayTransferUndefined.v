(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: An uninitialized captured error number cannot authorize a retry. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPure GatewayReturns GatewayControlPaths
  GatewayOperations GatewayTransferSource GatewayTransferErrno GatewayTransferProgress GatewayTransferRetry.
Import ListNotations.
Open Scope Z_scope.

Lemma actual_negative_errno_prefix ge temporaries memory :
  temporaries!_count=Some(Vlong(Int64.repr(-1))) ->
  gateway_retained_prefix ge
    (State f_host_transfer transfer_errno_first
      (Kseq transfer_errno_second(Kseq transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont)))
      empty_env temporaries memory)
    (State f_host_transfer transfer_after_restore transfer_iteration_cont empty_env temporaries memory).
Proof.
  intro COUNT.
  eapply gateway_prefix_next with(next:=State f_host_transfer transfer_retry_sequence
    (Kseq transfer_after_retry transfer_iteration_cont)empty_env temporaries memory);
    [cbn;tauto|intro another;apply unchanged_store_edge,edge_seq|].
  eapply gateway_prefix_next with(next:=State f_host_transfer transfer_retry_prefix
    (Kseq transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont))empty_env temporaries memory);
    [cbn;tauto|intro another;apply unchanged_store_edge,edge_seq|].
  eapply gateway_prefix_next with(next:=State f_host_transfer transfer_errno_sequence
    (Kseq transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont))empty_env temporaries memory).
  - cbn;tauto.
  - intro another;apply certified_if_edge with(v:=Vint Int.one)(b:=true);
      [apply actual_negative_count_comparison;exact COUNT|reflexivity].
  - eapply gateway_prefix_next with(next:=State f_host_transfer transfer_errno_first
      (Kseq transfer_errno_second(Kseq transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont)))
      empty_env temporaries memory);[cbn;tauto|intro another;apply unchanged_store_edge,edge_seq|].
    change(gateway_retained_prefix ge
      (State f_host_transfer transfer_errno_first
        (Kseq transfer_errno_second(Kseq transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont)))
        empty_env temporaries memory)
      (gateway_replace_memory(State f_host_transfer transfer_errno_first
        (Kseq transfer_errno_second(Kseq transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont)))
        empty_env temporaries memory)memory));constructor.
Qed.

Lemma actual_undefined_errno_blocked ge temporaries memory :
  temporaries!_number=Some Vundef ->
  gateway_blocked_path ge(State f_host_transfer transfer_errno_first
    (Kseq transfer_errno_second(Kseq transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont)))
    empty_env temporaries memory).
Proof.
  intro NUMBER;apply gateway_blocked_at.
  - cbn;tauto.
  - intros;discriminate.
  - intros another trace target STEP;inversion STEP;subst;
      try match goal with BAD:_=_\/_=_|-_=>destruct BAD;discriminate end.
    match goal with ACTUAL:eval_expr _ _ _ _(Ebinop Oeq _ _ _) _|-_=>
      inversion ACTUAL;subst end.
    match goal with LOOK:eval_expr _ _ _ _(Etempvar _number _) _|-_=>
      pose proof(evaluated_unique _ _ _ _ _ _
        (value_temp _ _ _ _ _ tint Vundef NUMBER)_ LOOK)as SAME;subst end.
    match goal with SEM:sem_binary_operation _ Oeq Vundef _ _ _ _=Some _|-_=>
      discriminate SEM end.
    all:try match goal with LOCATION:eval_lvalue _ _ _ _(Ebinop _ _ _ _) _ _ _|-_=>inversion LOCATION end.
Qed.

Theorem actual_negative_undefined_errno_cannot_return {World Event}(backend:gateway_backend World Event)ge
    temporaries before world events returned after next :
  temporaries!_count=Some(Vlong(Int64.repr(-1))) ->temporaries!_number=Some Vundef ->
  gateway_steps backend ge
    (gateway_live(State f_host_transfer transfer_after_restore transfer_iteration_cont empty_env temporaries before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->False.
Proof.
  intros COUNT NUMBER RUN.
  destruct(gateway_prefix_side_cut backend ge(fun _ _=>True)
    ltac:(unfold gateway_runtime_discipline;intros;exact I)
    (State f_host_transfer transfer_errno_first
      (Kseq transfer_errno_second(Kseq transfer_retry_test(Kseq transfer_after_retry transfer_iteration_cont)))
      empty_env temporaries before)
    (State f_host_transfer transfer_after_restore transfer_iteration_cont empty_env temporaries before)
    (actual_negative_errno_prefix ge temporaries before COUNT)before world events returned after next I RUN)
    as[prefix[suffix[memory[current[EVENTS[QUIET[PREFIX[READY REST]]]]]]]].
  cbn[GatewayMachine.gateway_replace_memory]in REST.
  eapply gateway_blocked_cannot_return;[apply actual_undefined_errno_blocked;exact NUMBER|exact REST].
Qed.
