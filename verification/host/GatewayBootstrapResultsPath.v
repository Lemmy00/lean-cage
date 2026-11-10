(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Default-result copying loads the same actual loader field after prior writes. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewaySourcePaths GatewaySourceAutomation
  GatewayFramedRuntime GatewayBootstrapABI GatewayBootstrapSource GatewayBootstrapCopySource GatewayBootstrapCopyPaths
  GatewayBootstrapCopyEdges GatewayBootstrapFilename.
Import ListNotations.
Open Scope Z_scope.

Definition bootstrap_results_temporaries (filename : val) temporaries := PTree.set _t'14 filename temporaries.

Theorem actual_bootstrap_results_prefix_path {World Event} (backend : gateway_backend World Event)
    (ge : Clight.genv) information resolved temporaries memory property destination object offset symbol count :
  gateway_ambient_closed backend property -> gateway_bootstrap_information_layout ge ->
  Genv.find_symbol ge _host_default_results = Some destination ->
  Genv.find_symbol ge _memcpy = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some (gateway_bootstrap_signature gateway_memory_copy_api) ->
  temporaries ! _api_size = Some (Vlong count) ->
  (forall memory world, property memory world ->
    Mem.load Mptr memory information 0 = Some (Vptr object offset)) ->
  gateway_source_path backend ge (gateway_bootstrap_signature gateway_memory_copy_api)
    [Vptr destination Ptrofs.zero; Vptr object offset; Vlong count]
    (bootstrap_copy_cont 4 information resolved
      (bootstrap_results_temporaries (Vptr object offset) temporaries)) property
    (State f_host_bootstrap (bootstrap_copy_after 4) Kstop
      (bootstrap_environment information resolved) temporaries memory) property.
Proof.
  intros CLOSED LAYOUT DESTINATION SYMBOL FUNCTION COUNT INFORMATION.
  repeat gateway_source_structure CLOSED.
  eapply gateway_source_same with (target := State f_host_bootstrap Sskip
    (Kseq (bootstrap_copy (bootstrap_array _host_default_results) (Etempvar _t'14 (tptr tschar)) bootstrap_api_size)
      (Kseq (bootstrap_copy_after 5) Kstop)) (bootstrap_environment information resolved)
    (bootstrap_results_temporaries (Vptr object offset) temporaries) memory).
  - exact CLOSED.
  - cbn; tauto.
  - intros before world GOOD; apply certified_set_edge, gateway_bootstrap_filename_value;
      [exact LAYOUT |exact (INFORMATION before world GOOD)].
  - repeat gateway_source_structure CLOSED.
    eapply gateway_source_same with (target := Callstate (gateway_bootstrap_signature gateway_memory_copy_api)
      [Vptr destination Ptrofs.zero; Vptr object offset; Vlong count]
      (bootstrap_copy_cont 4 information resolved
        (bootstrap_results_temporaries (Vptr object offset) temporaries)) memory).
    + exact CLOSED.
    + cbn; tauto.
    + intros before world GOOD; eapply gateway_bootstrap_copy_call_edge.
      * reflexivity.
      * exact SYMBOL.
      * exact FUNCTION.
      * eapply gateway_bootstrap_global_array_reference; [reflexivity |exact DESTINATION].
      * apply old_expression_value, value_temp, PTree.gss.
      * apply old_expression_value, value_temp; unfold bootstrap_results_temporaries;
          rewrite PTree.gso by discriminate; exact COUNT.
      * reflexivity.
      * reflexivity.
      * reflexivity.
    + constructor; intros; assumption.
Qed.
