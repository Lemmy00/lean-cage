(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Real length returns bind size and the literal suffix extent. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewaySourcePaths GatewayFramedRuntime
  GatewayBootstrapSource GatewayBootstrapLengthSource GatewayBootstrapValidationSource.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_bootstrap_sizeof_expression ge environment temporaries memory count :
  expression_value ge environment temporaries memory (Esizeof (tarray tschar count) tulong)
    (Vlong (Int64.repr (Z.max 0 count))).
Proof.
  replace (Vlong (Int64.repr (Z.max 0 count))) with
    (Vptrofs (Ptrofs.repr (sizeof ge (tarray tschar count)))).
  2: { change (Vlong (Ptrofs.to_int64 (Ptrofs.repr (1 * Z.max 0 count))) =
      Vlong (Int64.repr (Z.max 0 count))).
    rewrite Z.mul_1_l; f_equal; apply Ptrofs.agree64_to_int_eq;
      apply Ptrofs.agree64_repr; reflexivity. }
  split; [apply eval_Esizeof |].
  intros other VALUE; inversion VALUE; subst; [reflexivity |].
  match goal with LOCATION : eval_lvalue _ _ _ _ (Esizeof _ _) _ _ _ |- _ => inversion LOCATION end.
Qed.

Definition bootstrap_tail_assignment := match bootstrap_after_length with
  Ssequence first _ => first | _ => Sskip end.
Definition bootstrap_loaded_bound_temporaries size temporaries :=
  PTree.set _tail (Vlong (Int64.repr 30))
    (PTree.set _size (Vlong size) (PTree.set _t'3 (Vlong size) temporaries)).

Theorem actual_bootstrap_length_bindings {World Event} (backend : gateway_backend World Event)
    ge definition arguments target property information resolved temporaries memory size result :
  gateway_ambient_closed backend property ->
  gateway_source_path backend ge definition arguments target property
    (State f_host_bootstrap bootstrap_loaded_validation
      (Kseq bootstrap_after_loaded_validation Kstop) (bootstrap_environment information resolved)
      (bootstrap_loaded_bound_temporaries size temporaries) memory) result ->
  gateway_source_path backend ge definition arguments target property
    (Returnstate (Vlong size) (bootstrap_length_cont information resolved temporaries) memory) result.
Proof.
  intros CLOSED REST.
  set (returned := PTree.set _t'3 (Vlong size) temporaries).
  set (sized := PTree.set _size (Vlong size) returned).
  set (tailed := PTree.set _tail (Vlong (Int64.repr 30)) sized).
  eapply gateway_source_same with (target := State f_host_bootstrap Sskip
    (Kseq bootstrap_length_bind_size (Kseq bootstrap_after_length Kstop))
    (bootstrap_environment information resolved) returned memory);
    [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_returnstate |].
  eapply gateway_source_same with (target := State f_host_bootstrap bootstrap_length_bind_size
    (Kseq bootstrap_after_length Kstop) (bootstrap_environment information resolved) returned memory);
    [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_skip_seq |].
  eapply gateway_source_same with (target := State f_host_bootstrap Sskip
    (Kseq bootstrap_after_length Kstop) (bootstrap_environment information resolved) sized memory);
    [exact CLOSED |cbn; tauto |intros; apply certified_set_edge, old_expression_value, value_temp, PTree.gss |].
  eapply gateway_source_same with (target := State f_host_bootstrap bootstrap_after_length Kstop
    (bootstrap_environment information resolved) sized memory);
    [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_skip_seq |].
  eapply gateway_source_same with (target := State f_host_bootstrap bootstrap_tail_assignment
    (Kseq bootstrap_after_tail Kstop) (bootstrap_environment information resolved) sized memory);
    [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_seq |].
  eapply gateway_source_same with (target := State f_host_bootstrap Sskip
    (Kseq bootstrap_after_tail Kstop) (bootstrap_environment information resolved) tailed memory).
  - exact CLOSED.
  - cbn; tauto.
  - intros; apply certified_set_edge; eapply binary_expression_value;
      [apply gateway_bootstrap_sizeof_expression |apply old_expression_value; constructor |reflexivity].
  - eapply gateway_source_same with (target := State f_host_bootstrap bootstrap_after_tail Kstop
      (bootstrap_environment information resolved) tailed memory);
      [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_skip_seq |].
    eapply gateway_source_same with (target := State f_host_bootstrap bootstrap_loaded_validation
      (Kseq bootstrap_after_loaded_validation Kstop) (bootstrap_environment information resolved) tailed memory);
      [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_seq |exact REST].
Qed.
