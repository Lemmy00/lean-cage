(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: An unsuccessful bytes operation cannot reach a successful field return. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPure GatewayReturns
  GatewayAllocation GatewayPrefix.
Import ListNotations.
Open Scope Z_scope.

Definition field_api_return_values arguments returned :=
  PTree.set _t'1(Vint returned)(field_parameters arguments).

Lemma field_failed_api_path ge locals arguments memory returned :
  returned<>Int.zero ->
  gateway_constant_path ge(Vint(Int.neg Int.one))
    (Returnstate(Vint returned)(field_api_cont locals arguments Kstop)memory).
Proof.
  intro NONZERO.
  eapply gateway_constant_next with(next:=State f_host_field_bytes Sskip
    (Kseq field_api_test(Kseq field_after_api Kstop))(field_environment locals)
    (field_api_return_values arguments returned)memory).
  - cbn;tauto.
  - intro another;apply unchanged_store_edge,edge_returnstate.
  - eapply gateway_constant_next with(next:=State f_host_field_bytes field_api_test
      (Kseq field_after_api Kstop)(field_environment locals)(field_api_return_values arguments returned)memory).
    + cbn;tauto.
    + intro another;apply unchanged_store_edge,edge_skip_seq.
    + eapply gateway_constant_next with(next:=State f_host_field_bytes
        (Sreturn(Some(Eunop Oneg(Econst_int Int.one tint)tint)))
        (Kseq field_after_api Kstop)(field_environment locals)(field_api_return_values arguments returned)memory).
      * cbn;tauto.
      * intro another;apply unchanged_store_edge;eapply edge_if with(v:=Vint returned)(b:=true).
        -- apply value_temp;reflexivity.
        -- change(Some(negb(Int.eq returned Int.zero))=Some true).
           rewrite Int.eq_false by exact NONZERO;reflexivity.
      * eapply gateway_constant_at_return with(value:=Vint(Int.neg Int.one)).
        -- reflexivity.
        -- intro another;apply old_expression_value;eapply value_unary;[constructor|reflexivity].
        -- reflexivity.
Qed.

Theorem actual_successful_field_requires_bytes_success {World Event}
    (backend:gateway_backend World Event)ge locals arguments before world events after final_world returned :
  gateway_steps backend ge
    (gateway_live(Returnstate(Vint returned)(field_api_cont locals arguments Kstop)before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)final_world) ->returned=Int.zero.
Proof.
  intro RUN;destruct(Int.eq_dec returned Int.zero)as[SAME|OTHER];[exact SAME|].
  pose proof(gateway_constant_path_actual backend ge _ _ world events _ _ _
    (field_failed_api_path ge locals arguments before returned OTHER)RUN)as IMPOSSIBLE.
  inversion IMPOSSIBLE.
Qed.
