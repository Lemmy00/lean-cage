(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Copy continuations use the same source index and exact evaluated arguments. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewaySourcePaths GatewaySourceAutomation
  GatewayFramedRuntime GatewayBootstrapABI GatewayBootstrapSource GatewayBootstrapCopySource GatewayBootstrapCopyEdges.
Import ListNotations.
Open Scope Z_scope.

Definition bootstrap_copy_cont index information resolved temporaries :=
  Kcall None f_host_bootstrap (bootstrap_environment information resolved) temporaries
    (Kseq (bootstrap_copy_after (S index)) Kstop).

Theorem gateway_bootstrap_direct_copy_path {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    index information resolved temporaries memory property target origin amount target_value origin_value count symbol :
  gateway_ambient_closed backend property ->
  bootstrap_copy_after index = Ssequence (bootstrap_copy target origin amount) (bootstrap_copy_after (S index)) ->
  Genv.find_symbol ge _memcpy = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some (gateway_bootstrap_signature gateway_memory_copy_api) ->
  (forall memory world, property memory world ->
    expression_value ge (bootstrap_environment information resolved) temporaries memory target target_value /\
    expression_value ge (bootstrap_environment information resolved) temporaries memory origin origin_value /\
    expression_value ge (bootstrap_environment information resolved) temporaries memory amount (Vlong count) /\
    sem_cast target_value (typeof target) (tptr tvoid) memory = Some target_value /\
    sem_cast origin_value (typeof origin) (tptr tvoid) memory = Some origin_value /\
    sem_cast (Vlong count) (typeof amount) tulong memory = Some (Vlong count)) ->
  gateway_source_path backend ge (gateway_bootstrap_signature gateway_memory_copy_api)
    [target_value; origin_value; Vlong count] (bootstrap_copy_cont index information resolved temporaries) property
    (State f_host_bootstrap (bootstrap_copy_after index) Kstop
      (bootstrap_environment information resolved) temporaries memory) property.
Proof.
  intros CLOSED SHAPE SYMBOL FUNCTION OPERANDS.
  eapply gateway_source_same with (target := State f_host_bootstrap (bootstrap_copy target origin amount)
    (Kseq (bootstrap_copy_after (S index)) Kstop) (bootstrap_environment information resolved) temporaries memory).
  - exact CLOSED.
  - rewrite SHAPE; cbn; tauto.
  - intros; apply unchanged_store_edge; rewrite SHAPE; apply edge_seq.
  - eapply gateway_source_same with (target := Callstate (gateway_bootstrap_signature gateway_memory_copy_api)
      [target_value; origin_value; Vlong count] (bootstrap_copy_cont index information resolved temporaries) memory).
    + exact CLOSED.
    + cbn; tauto.
    + intros before world GOOD.
      destruct (OPERANDS before world GOOD) as [TARGET [ORIGIN [AMOUNT [TARGET_CAST [ORIGIN_CAST AMOUNT_CAST]]]]].
      eapply gateway_bootstrap_copy_call_edge;
        [reflexivity |exact SYMBOL |exact FUNCTION |exact TARGET |exact ORIGIN |exact AMOUNT |
         exact TARGET_CAST |exact ORIGIN_CAST |exact AMOUNT_CAST].
    + constructor; intros; assumption.
Qed.

Theorem gateway_bootstrap_copy_return_path {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    index information resolved temporaries memory property returned definition arguments continuation result :
  gateway_ambient_closed backend property ->
  gateway_source_path backend ge definition arguments continuation property
    (State f_host_bootstrap (bootstrap_copy_after (S index)) Kstop
      (bootstrap_environment information resolved) temporaries memory) result ->
  gateway_source_path backend ge definition arguments continuation property
    (Returnstate returned (bootstrap_copy_cont index information resolved temporaries) memory) result.
Proof.
  intros CLOSED REST.
  unfold bootstrap_copy_cont.
  do 2 gateway_source_structure CLOSED.
  exact REST.
Qed.
