(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The real final publication result selects module return or failure. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayModulePublication GatewayReturns.
Import ListNotations.
Open Scope Z_scope.

Theorem actual_module_published_return_script ge temporaries memory module object offset :
  temporaries ! _module = Some module -> module = Vptr object offset ->
  gateway_constant_path ge module
    (Returnstate (Vint Int.zero) (module_outcome_add_cont temporaries Kstop) memory).
Proof.
  intros MODULE POINTER; subst module.
  set (updated := PTree.set _t'12 (Vint Int.zero) temporaries).
  eapply gateway_constant_next with (next := State f_host_initialize Sskip
    (Kseq module_outcome_add_test (Kseq module_outcome_return Kstop)) empty_env updated memory).
  - cbn; tauto.
  - intro another; apply unchanged_store_edge, edge_returnstate.
  - eapply gateway_constant_next with (next := State f_host_initialize module_outcome_add_test
      (Kseq module_outcome_return Kstop) empty_env updated memory).
    + cbn; tauto.
    + intro another; apply unchanged_store_edge, edge_skip_seq.
    + eapply gateway_constant_next with (next := State f_host_initialize Sskip
        (Kseq module_outcome_return Kstop) empty_env updated memory).
      * cbn; tauto.
      * intro another; apply certified_if_edge with (v := Vint Int.zero) (b := false).
        -- apply old_expression_value, value_temp, PTree.gss.
        -- reflexivity.
      * eapply gateway_constant_next with (next := State f_host_initialize module_outcome_return Kstop
          empty_env updated memory).
        -- cbn; tauto.
        -- intro another; apply unchanged_store_edge, edge_skip_seq.
        -- eapply gateway_constant_at_return with (value := Vptr object offset).
           ++ reflexivity.
           ++ intro another; apply old_expression_value, value_temp.
              unfold updated; rewrite PTree.gso by discriminate; exact MODULE.
           ++ intro another; reflexivity.
Qed.

Theorem gateway_actual_module_published_return {World Event} (backend : gateway_backend World Event)
    ge temporaries before world events module object offset returned after next :
  temporaries ! _module = Some module -> module = Vptr object offset ->
  gateway_steps backend ge
    (gateway_live (Returnstate (Vint Int.zero) (module_outcome_add_cont temporaries Kstop) before) world)
    events (gateway_live (Returnstate returned Kstop after) next) -> returned = module.
Proof.
  intros MODULE POINTER RUN; eapply gateway_constant_path_actual;
    [eapply actual_module_published_return_script; eassumption |exact RUN].
Qed.
