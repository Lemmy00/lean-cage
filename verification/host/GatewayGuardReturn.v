(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual checked caller branches exclude undefined and failed helper
   results. *)
From Stdlib Require Import List.
From compcert Require Import Maps Integers AST Values Memory Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewayMachine GatewayReturns GatewayReturnTypes.
Import ListNotations.

Definition gateway_result_guard identifier:=Sifthenelse(Etempvar identifier tint)
  (Sreturn(Some(Eunop Oneg(Econst_int Int.one tint)tint)))Sskip.
Definition gateway_result_guard_cont function environment temporaries identifier following:=
  Kcall(Some identifier)function environment temporaries(Kseq(gateway_result_guard identifier)following).

Lemma gateway_failed_result_path ge function environment temporaries identifier following returned memory :
  fn_return function=tint ->call_cont following=Kstop ->returned<>Int.zero ->
  gateway_constant_path ge(Vint(Int.neg Int.one))
    (Returnstate(Vint returned)(gateway_result_guard_cont function environment temporaries identifier following)memory).
Proof.
  intros TYPE CONT NONZERO.
  eapply gateway_constant_next with(next:=State function Sskip(Kseq(gateway_result_guard identifier)following)
    environment(PTree.set identifier(Vint returned)temporaries)memory).
  - cbn;tauto.
  - intro another;apply unchanged_store_edge,edge_returnstate.
  - eapply gateway_constant_next with(next:=State function(gateway_result_guard identifier)following
      environment(PTree.set identifier(Vint returned)temporaries)memory).
    + cbn;tauto.
    + intro another;apply unchanged_store_edge,edge_skip_seq.
    + eapply gateway_constant_next with(next:=State function
        (Sreturn(Some(Eunop Oneg(Econst_int Int.one tint)tint)))following
        environment(PTree.set identifier(Vint returned)temporaries)memory).
      * cbn;tauto.
      * intro another;apply certified_if_edge with(v:=Vint returned)(b:=true).
        -- apply old_expression_value,value_temp;apply PTree.gss.
        -- change(Some(negb(Int.eq returned Int.zero))=Some true).
           rewrite Int.eq_false by exact NONZERO;reflexivity.
      * eapply gateway_constant_at_return with(value:=Vint(Int.neg Int.one)).
        -- exact CONT.
        -- intro another;apply old_expression_value;eapply value_unary;[constructor|reflexivity].
        -- intro another;rewrite TYPE;reflexivity.
Qed.

Lemma gateway_undefined_result_path ge function environment temporaries identifier following memory :
  gateway_blocked_path ge
    (Returnstate Vundef(gateway_result_guard_cont function environment temporaries identifier following)memory).
Proof.
  eapply gateway_blocked_next with(next:=State function Sskip(Kseq(gateway_result_guard identifier)following)
    environment(PTree.set identifier Vundef temporaries)memory).
  - cbn;tauto.
  - intro another;apply unchanged_store_edge,edge_returnstate.
  - eapply gateway_blocked_next with(next:=State function(gateway_result_guard identifier)following
      environment(PTree.set identifier Vundef temporaries)memory).
    + cbn;tauto.
    + intro another;apply unchanged_store_edge,edge_skip_seq.
    + apply gateway_blocked_at.
      * cbn;tauto.
      * intros;discriminate.
      * intros another trace target STEP;inversion STEP;subst;
          try match goal with BAD:_=_\/_=_|-_=>destruct BAD;discriminate end.
        match goal with VALUE:eval_expr _ _ _ _(Etempvar identifier tint) _|-_=>
          pose proof(evaluated_unique _ _ _ _ _ _
            (value_temp _ _ _ _ identifier tint Vundef ltac:(apply PTree.gss))_ VALUE)as SAME;subst end.
        discriminate.
Qed.

Theorem gateway_successful_checked_result {World Event}(backend:gateway_backend World Event)ge
    function environment temporaries identifier following memory world events returned after next :
  fn_return function=tint ->call_cont following=Kstop ->gateway_int_return_value returned ->
  gateway_steps backend ge
    (gateway_live(Returnstate returned(gateway_result_guard_cont function environment temporaries identifier following)memory)world)
    events(gateway_live(Returnstate(Vint Int.zero)Kstop after)next) ->returned=Vint Int.zero.
Proof.
  intros TYPE CONT[UNDEFINED|[ZERO|FAILED]]RUN;[subst returned|exact ZERO|subst returned].
  - exfalso;eapply gateway_blocked_cannot_return;[apply gateway_undefined_result_path|exact RUN].
  - pose proof(gateway_constant_path_actual backend ge _ _ world events(Vint Int.zero)after next
      (gateway_failed_result_path ge function environment temporaries identifier following(Int.neg Int.one)
        memory TYPE CONT ltac:(discriminate))RUN)as BAD;discriminate BAD.
Qed.
