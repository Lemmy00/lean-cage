(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: An actual failed loader call cannot become successful bootstrap. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBootstrapSource GatewayReturns.
Import ListNotations.
Open Scope Z_scope.

Definition bootstrap_failed_loader_temporaries := PTree.set _t'1 (Vint Int.zero) bootstrap_temporaries.
Definition bootstrap_failed_test_temporaries := PTree.set _t'2 (Vint Int.one) bootstrap_failed_loader_temporaries.
Definition bootstrap_loader_failure_body := match bootstrap_loader_test with Sifthenelse _ failed _ => failed | _ => Sskip end.

Theorem actual_bootstrap_failed_loader_script ge information resolved memory :
  gateway_constant_path ge (Vint (Int.neg Int.one))
    (Returnstate (Vint Int.zero) (bootstrap_loader_cont information resolved) memory).
Proof.
  eapply gateway_constant_next with (next := State f_host_bootstrap Sskip
    (Kseq bootstrap_loader_bind (Kseq bootstrap_loader_test (Kseq bootstrap_after_first Kstop)))
    (bootstrap_environment information resolved) bootstrap_failed_loader_temporaries memory).
  - cbn; tauto.
  - intro another; apply unchanged_store_edge, edge_returnstate.
  - eapply gateway_constant_next with (next := State f_host_bootstrap bootstrap_loader_bind
      (Kseq bootstrap_loader_test (Kseq bootstrap_after_first Kstop))
      (bootstrap_environment information resolved) bootstrap_failed_loader_temporaries memory).
    + cbn; tauto.
    + intro another; apply unchanged_store_edge, edge_skip_seq.
    + eapply gateway_constant_next with (next := State f_host_bootstrap
        (Sset _t'2 (Econst_int Int.one tint))
        (Kseq bootstrap_loader_test (Kseq bootstrap_after_first Kstop))
        (bootstrap_environment information resolved) bootstrap_failed_loader_temporaries memory).
      * cbn; tauto.
      * intro another; apply certified_if_edge with (v := Vint Int.one) (b := true).
        -- apply old_expression_value; eapply value_unary.
           ++ apply value_temp, PTree.gss.
           ++ reflexivity.
        -- reflexivity.
      * eapply gateway_constant_next with (next := State f_host_bootstrap Sskip
          (Kseq bootstrap_loader_test (Kseq bootstrap_after_first Kstop))
          (bootstrap_environment information resolved) bootstrap_failed_test_temporaries memory).
        -- cbn; tauto.
        -- intro another; apply certified_set_edge; apply old_expression_value; constructor.
        -- eapply gateway_constant_next with (next := State f_host_bootstrap bootstrap_loader_test
            (Kseq bootstrap_after_first Kstop) (bootstrap_environment information resolved)
            bootstrap_failed_test_temporaries memory).
           ++ cbn; tauto.
           ++ intro another; apply unchanged_store_edge, edge_skip_seq.
           ++ eapply gateway_constant_next with (next := State f_host_bootstrap bootstrap_loader_failure_body
               (Kseq bootstrap_after_first Kstop) (bootstrap_environment information resolved)
               bootstrap_failed_test_temporaries memory).
              ** cbn; tauto.
              ** intro another; apply certified_if_edge with (v := Vint Int.one) (b := true).
                 --- apply old_expression_value, value_temp, PTree.gss.
                 --- reflexivity.
              ** eapply gateway_constant_at_return with (value := Vint (Int.neg Int.one)).
                 --- reflexivity.
                 --- intro another; apply old_expression_value; eapply value_unary; [constructor |reflexivity].
                 --- intro another; reflexivity.
Qed.

Theorem gateway_actual_bootstrap_loader_failure {World Event} (backend : gateway_backend World Event)
    ge information resolved before world events returned after next :
  gateway_steps backend ge
    (gateway_live (Returnstate (Vint Int.zero) (bootstrap_loader_cont information resolved) before) world)
    events (gateway_live (Returnstate returned Kstop after) next) -> returned = Vint (Int.neg Int.one).
Proof.
  intro RUN; eapply gateway_constant_path_actual;
    [apply actual_bootstrap_failed_loader_script |exact RUN].
Qed.
