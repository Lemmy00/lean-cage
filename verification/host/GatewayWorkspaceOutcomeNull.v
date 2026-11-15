(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A failed actual constructor cannot become a successful Workspace result. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayWorkspaceOutcomeSource GatewayReferenceSourceExecution
  GatewayReferenceRuntime GatewaySourcePaths GatewayContexts GatewayFramedRuntime GatewaySourceCuts.
Import ListNotations.

Theorem gateway_actual_workspace_null_outcome {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    environment parameters data data_offset symbol before world events value after next :
  parameters ! _data = Some (Vptr data data_offset) -> environment ! _Py_DecRef = None ->
  Genv.find_symbol ge _Py_DecRef = Some symbol -> Genv.find_funct_ptr ge symbol = Some gateway_reference_decref_definition ->
  gateway_steps backend ge
    (gateway_live (Returnstate Vnullptr (gateway_workspace_outcome_cont environment parameters) before) world) events
    (gateway_live (Returnstate value Kstop after) next) -> value = Vnullptr.
Proof.
  intros DATA LOCAL SYMBOL FUNCTION RUN.
  assert (CLOSED : gateway_ambient_closed backend (fun _ _ => True)) by (unfold gateway_ambient_closed; auto).
  pose proof (gateway_workspace_outcome_release_source backend ge (fun _ _ => True) environment parameters data data_offset Vnullptr before symbol
    CLOSED DATA LOCAL SYMBOL FUNCTION) as PATH.
  destruct (gateway_source_path_cut backend ge _ _ _ _ _ _ PATH before world events value after next I RUN)
    as (prefix &suffix &called &current &EVENTS &QUIET &PREFIX &READY &REST).
  destruct (gateway_return_cut backend ge gateway_reference_decref_definition [Vptr data data_offset]
    (gateway_workspace_data_release_cont environment (gateway_workspace_outcome_parameters parameters Vnullptr)) called current suffix
    (Returnstate value Kstop after) next I ltac:(cbn [gateway_continuation gateway_workspace_data_release_cont gateway_cont_weight]; lia) REST)
    as (operation &tail &ignored &memory &owner &TAIL_EVENTS &OPERATION &TAIL).
  eapply gateway_actual_workspace_outcome_release_identity;
    [apply PTree.gss |left; reflexivity |exact TAIL].
Qed.
