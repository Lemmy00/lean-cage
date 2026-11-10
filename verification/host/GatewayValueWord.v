(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Only a real successful first-word return can reach a non-NULL value result. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayValueEntry GatewayValueGuards GatewayValueTag
  GatewayStreamWord GatewayReturnTypes GatewayReturns GatewayFailurePaths GatewayFrames GatewayPure.
Import ListNotations.
Open Scope Z_scope.

Lemma gateway_value_word_return_profile:gateway_int_return_function f_host_word.
Proof. unfold gateway_int_return_function;split;[reflexivity|].
  cbn;unfold gateway_int_return_expression;intuition. Qed.

Theorem gateway_actual_word_return_type {World Event}(backend:gateway_backend World Event)ge
    arguments before world events returned after next :
  gateway_steps backend ge(gateway_live(Callstate(Internal f_host_word)arguments Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->gateway_int_return_value returned.
Proof. apply gateway_actual_int_return;exact gateway_value_word_return_profile. Qed.

Lemma gateway_value_tag_undefined ge slots arguments initial memory :
  gateway_blocked_path ge(Returnstate Vundef(gateway_value_tag_cont slots arguments initial)memory).
Proof.
  eapply gateway_blocked_next with(next:=State f_host_value Sskip
    (Kseq gateway_value_tag_guard(Kseq gateway_value_after_tag Kstop))(gateway_value_environment slots)
    (PTree.set _t'2 Vundef(gateway_value_debited_parameters arguments initial))memory).
  - cbn;tauto.
  - intro another;apply unchanged_store_edge,edge_returnstate.
  - eapply gateway_blocked_next with(next:=State f_host_value gateway_value_tag_guard
      (Kseq gateway_value_after_tag Kstop)(gateway_value_environment slots)
      (PTree.set _t'2 Vundef(gateway_value_debited_parameters arguments initial))memory).
    + cbn;tauto.
    + intro another;apply unchanged_store_edge,edge_skip_seq.
    + apply gateway_blocked_at.
      * cbn;tauto.
      * intros;discriminate.
      * intros another trace target STEP;inversion STEP;subst;
          try match goal with BAD:_=_\/_=_|-_=>destruct BAD;discriminate end.
        match goal with VALUE:eval_expr _ _ _ _(Etempvar _t'2 _) _|-_=>
          pose proof(evaluated_unique _ _ _ _ _ _
            (value_temp _ _ _ _ _ tint Vundef ltac:(apply PTree.gss))_ VALUE)as SAME;subst end.
        discriminate.
Qed.

Lemma gateway_value_tag_negative {World Event}(backend:gateway_backend World Event)ge slots arguments initial memory :
  gateway_failure_result backend ge
    (Returnstate(Vint(Int.neg Int.one))(gateway_value_tag_cont slots arguments initial)memory).
Proof.
  eapply gateway_failure_edge with(target:=State f_host_value Sskip
    (Kseq gateway_value_tag_guard(Kseq gateway_value_after_tag Kstop))(gateway_value_environment slots)
    (PTree.set _t'2(Vint(Int.neg Int.one))(gateway_value_debited_parameters arguments initial))memory).
  - cbn;tauto.
  - intro another;apply unchanged_store_edge,edge_returnstate.
  - eapply gateway_failure_edge with(target:=State f_host_value gateway_value_tag_guard
      (Kseq gateway_value_after_tag Kstop)(gateway_value_environment slots)
      (PTree.set _t'2(Vint(Int.neg Int.one))(gateway_value_debited_parameters arguments initial))memory).
    + cbn;tauto.
    + intro another;apply unchanged_store_edge,edge_skip_seq.
    + eapply gateway_failure_edge with(target:=State f_host_value(Sreturn(Some gateway_null_expression))
        (Kseq gateway_value_after_tag Kstop)(gateway_value_environment slots)
        (PTree.set _t'2(Vint(Int.neg Int.one))(gateway_value_debited_parameters arguments initial))memory).
      * cbn;tauto.
      * intro another;eapply certified_if_edge with(b:=true).
        -- apply old_expression_value,value_temp;apply PTree.gss.
        -- reflexivity.
      * apply gateway_failure_selected;[exact gateway_value_pointer_return|reflexivity|reflexivity].
Qed.

Theorem gateway_value_successful_tag_result {World Event}(backend:gateway_backend World Event)ge
    slots arguments initial before world events returned value after next :
  gateway_int_return_value returned ->value<>Vnullptr ->
  gateway_steps backend ge(gateway_live(Returnstate returned(gateway_value_tag_cont slots arguments initial)before)world)
    events(gateway_live(Returnstate value Kstop after)next) ->returned=Vint Int.zero.
Proof.
  intros[UNDEFINED|[ZERO|NEGATIVE]]NONNULL RUN;[|exact ZERO|].
  - subst returned;exfalso;eapply gateway_blocked_cannot_return;
      [exact(gateway_value_tag_undefined ge slots arguments initial before)|exact RUN].
  - subst returned;exfalso;apply NONNULL;
      eapply(gateway_value_tag_negative backend ge slots arguments initial before);exact RUN.
Qed.
