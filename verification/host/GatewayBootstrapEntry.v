(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The loader request is reached from actual bootstrap entry and allocations. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayBootstrapABI GatewayBootstrapSource GatewayFunctionEntry.
Import ListNotations.

Theorem actual_bootstrap_reaches_loader (ge : Clight.genv) before symbol entry_symbol :
  Genv.find_symbol ge _dladdr = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some (gateway_bootstrap_signature gateway_loader_address_api) ->
  Genv.find_symbol ge _PyInit__host = Some entry_symbol ->
  exists information resolved allocated,
    function_entry2 ge f_host_bootstrap [] before (bootstrap_environment information resolved)
      bootstrap_temporaries allocated /\
    store_path ge (fun _ => True) (Callstate (Internal f_host_bootstrap) [] Kstop before) 5
      (Callstate (gateway_bootstrap_signature gateway_loader_address_api)
        [Vptr entry_symbol Integers.Ptrofs.zero; Vptr information Integers.Ptrofs.zero]
        (bootstrap_loader_cont information resolved) allocated).
Proof.
  intros SYMBOL FUNCTION ENTRY.
  destruct (actual_bootstrap_allocations ge before)
    as (information & first & resolved & allocated & INFO & RESOLVED & DISTINCT & INFO_FRESH & RESOLVED_FRESH &
      INFO_ACCESS & RESOLVED_ACCESS & ALLOCATED).
  exists information, resolved, allocated; split; [exact ALLOCATED |].
  eapply store_next; [exact I |apply function_entry_source_edge; exact ALLOCATED |].
  eapply store_next; [exact I |apply unchanged_store_edge, edge_seq |].
  eapply store_next; [exact I |apply unchanged_store_edge, edge_seq |].
  eapply store_next; [exact I |apply unchanged_store_edge, edge_seq |].
  eapply store_next; [exact I |eapply actual_bootstrap_loader_edge; eassumption |].
  constructor; exact I.
Qed.
