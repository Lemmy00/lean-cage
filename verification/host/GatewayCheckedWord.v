(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Every checked word call must actually return zero before a value succeeds. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewayMachine GatewayFrames GatewayReturns GatewayReturnTypes GatewayFailurePaths GatewayPure.
Import ListNotations.

Definition gateway_word_result_guard destination:=
  Sifthenelse(Etempvar destination tint)(Sreturn(Some gateway_null_expression))Sskip.
Definition gateway_checked_word_cont destination function environment parameters rest:=
  Kcall(Some destination)function environment parameters(Kseq(gateway_word_result_guard destination)rest).

Lemma gateway_checked_word_undefined ge destination function environment parameters rest memory :
  gateway_blocked_path ge
    (Returnstate Vundef(gateway_checked_word_cont destination function environment parameters rest)memory).
Proof.
  eapply gateway_blocked_next with(next:=State function Sskip
    (Kseq(gateway_word_result_guard destination)rest)environment(PTree.set destination Vundef parameters)memory).
  - cbn;tauto.
  - intro another;apply unchanged_store_edge,edge_returnstate.
  - eapply gateway_blocked_next with(next:=State function(gateway_word_result_guard destination)rest
      environment(PTree.set destination Vundef parameters)memory).
    + cbn;tauto.
    + intro another;apply unchanged_store_edge,edge_skip_seq.
    + apply gateway_blocked_at.
      * cbn;tauto.
      * intros;discriminate.
      * intros another trace target STEP;inversion STEP;subst;
          try match goal with BAD:_=_\/_=_|-_=>destruct BAD;discriminate end.
        match goal with VALUE:eval_expr _ _ _ _(Etempvar destination _) _|-_=>
          pose proof(evaluated_unique _ _ _ _ _ _
            (value_temp _ _ _ _ _ tint Vundef ltac:(apply PTree.gss))_ VALUE)as SAME;subst end.
        discriminate.
Qed.

Lemma gateway_checked_word_negative {World Event}(backend:gateway_backend World Event)ge destination function
    environment parameters rest memory :
  gateway_pointer_return function ->call_cont rest=Kstop ->
  gateway_failure_result backend ge
    (Returnstate(Vint(Int.neg Int.one))(gateway_checked_word_cont destination function environment parameters rest)memory).
Proof.
  intros POINTER STOP.
  eapply gateway_failure_edge with(target:=State function Sskip
    (Kseq(gateway_word_result_guard destination)rest)environment(PTree.set destination(Vint(Int.neg Int.one))parameters)memory).
  - cbn;tauto.
  - intro another;apply unchanged_store_edge,edge_returnstate.
  - eapply gateway_failure_edge with(target:=State function(gateway_word_result_guard destination)rest
      environment(PTree.set destination(Vint(Int.neg Int.one))parameters)memory).
    + cbn;tauto.
    + intro another;apply unchanged_store_edge,edge_skip_seq.
    + eapply gateway_failure_edge with(target:=State function(Sreturn(Some gateway_null_expression))rest
        environment(PTree.set destination(Vint(Int.neg Int.one))parameters)memory).
      * cbn;tauto.
      * intro another;eapply certified_if_edge with(b:=true).
        -- apply old_expression_value,value_temp;apply PTree.gss.
        -- reflexivity.
      * apply gateway_failure_selected;[exact POINTER|reflexivity|exact STOP].
Qed.

Theorem gateway_checked_word_result {World Event}(backend:gateway_backend World Event)ge destination function
    environment parameters rest before world events returned value after next :
  gateway_pointer_return function ->call_cont rest=Kstop ->
  gateway_int_return_value returned ->value<>Vnullptr ->
  gateway_steps backend ge
    (gateway_live(Returnstate returned(gateway_checked_word_cont destination function environment parameters rest)before)world)
    events(gateway_live(Returnstate value Kstop after)next) ->returned=Vint Int.zero.
Proof.
  intros POINTER STOP[UNDEFINED|[ZERO|NEGATIVE]]NONNULL RUN;[|exact ZERO|].
  - subst returned;exfalso;eapply gateway_blocked_cannot_return;
      [exact(gateway_checked_word_undefined ge destination function environment parameters rest before)|exact RUN].
  - subst returned;exfalso;apply NONNULL;
      eapply(gateway_checked_word_negative backend ge destination function environment parameters rest before POINTER STOP);exact RUN.
Qed.
