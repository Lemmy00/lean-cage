(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A real zero suffix-comparison result passes the actual rejection guard. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewaySourcePaths GatewayFramedRuntime
  GatewayReturns GatewayBootstrapValidationSource.
Import ListNotations.
Open Scope Z_scope.

Definition bootstrap_comparison_cont compared flag function environment temporaries continuation :=
  Kcall (Some compared) function environment temporaries
    (Kseq (Sset flag (Ecast (Etempvar compared tint) tbool))
      (Kseq (Sifthenelse (Etempvar flag tint) bootstrap_path_reject Sskip) continuation)).
Definition bootstrap_compared_temporaries compared flag status temporaries :=
  PTree.set flag (Val.of_bool (negb (Int.eq status Int.zero)))
    (PTree.set compared (Vint status) temporaries).

Theorem gateway_bootstrap_comparison_success {World Event} (backend : gateway_backend World Event)
    ge definition arguments target property function environment temporaries memory continuation
    compared flag result :
  gateway_ambient_closed backend property ->
  gateway_source_path backend ge definition arguments target property
    (State function Sskip continuation environment
      (bootstrap_compared_temporaries compared flag Int.zero temporaries) memory) result ->
  gateway_source_path backend ge definition arguments target property
    (Returnstate (Vint Int.zero)
      (bootstrap_comparison_cont compared flag function environment temporaries continuation) memory) result.
Proof.
  intros CLOSED REST.
  set (returned := PTree.set compared (Vint Int.zero) temporaries).
  set (checked := PTree.set flag (Vint Int.zero) returned).
  set (bind := Sset flag (Ecast (Etempvar compared tint) tbool)).
  set (guard := Sifthenelse (Etempvar flag tint) bootstrap_path_reject Sskip).
  eapply gateway_source_same with (target := State function Sskip (Kseq bind (Kseq guard continuation))
    environment returned memory);
    [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_returnstate |].
  eapply gateway_source_same with (target := State function bind (Kseq guard continuation)
    environment returned memory);
    [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_skip_seq |].
  eapply gateway_source_same with (target := State function Sskip (Kseq guard continuation)
    environment checked memory).
  - exact CLOSED.
  - cbn; tauto.
  - intros; apply certified_set_edge; eapply cast_expression_value;
      [apply old_expression_value, value_temp, PTree.gss |reflexivity].
  - eapply gateway_source_same with (target := State function guard continuation environment checked memory);
      [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_skip_seq |].
    eapply gateway_source_same with (target := State function Sskip continuation environment checked memory).
    + exact CLOSED.
    + cbn; tauto.
    + intros; apply certified_if_edge with (v := Vint Int.zero) (b := false);
        [apply old_expression_value, value_temp, PTree.gss |reflexivity].
    + exact REST.
Qed.

Theorem gateway_bootstrap_comparison_failure ge function environment temporaries memory continuation
    compared flag status :
  fn_return function = tint -> call_cont continuation = Kstop -> status <> Int.zero ->
  gateway_constant_path ge (Vint (Int.neg Int.one))
    (Returnstate (Vint status)
      (bootstrap_comparison_cont compared flag function environment temporaries continuation) memory).
Proof.
  intros TYPE STOP NONZERO.
  set (returned := PTree.set compared (Vint status) temporaries).
  set (checked := PTree.set flag (Vint Int.one) returned).
  set (bind := Sset flag (Ecast (Etempvar compared tint) tbool)).
  set (guard := Sifthenelse (Etempvar flag tint) bootstrap_path_reject Sskip).
  eapply gateway_constant_next with (next := State function Sskip (Kseq bind (Kseq guard continuation))
    environment returned memory);
    [cbn; tauto |intros; apply unchanged_store_edge, edge_returnstate |].
  eapply gateway_constant_next with (next := State function bind (Kseq guard continuation)
    environment returned memory);
    [cbn; tauto |intros; apply unchanged_store_edge, edge_skip_seq |].
  eapply gateway_constant_next with (next := State function Sskip (Kseq guard continuation)
    environment checked memory).
  - cbn; tauto.
  - intros; apply certified_set_edge; eapply cast_expression_value with (v := Vint status).
    + apply old_expression_value, value_temp, PTree.gss.
    + cbn; rewrite (Int.eq_false status Int.zero NONZERO); reflexivity.
  - eapply gateway_constant_next with (next := State function guard continuation environment checked memory);
      [cbn; tauto |intros; apply unchanged_store_edge, edge_skip_seq |].
    eapply gateway_constant_next with (next := State function bootstrap_path_reject continuation
      environment checked memory).
    + cbn; tauto.
    + intros; apply certified_if_edge with (v := Vint Int.one) (b := true);
        [apply old_expression_value, value_temp, PTree.gss |reflexivity].
    + eapply gateway_constant_at_return with (value := Vint (Int.neg Int.one)).
      * exact STOP.
      * intros; apply old_expression_value; eapply value_unary; [constructor |reflexivity].
      * intros; rewrite TYPE; reflexivity.
Qed.
