(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-assurance.evidence: Complete caller component types and transitive foundations are
   inspected together. This checkpoint query is not an integrated acceptance theorem. *)
From HostGateway Require Import GatewayResponseDecoded GatewayDecodedEOF GatewayCleanupReferences GatewayCleanupOwnedCloses
  GatewayCleanupReap GatewayCleanupRestore GatewayReapNativeObservation.

Set Printing All.
Set Printing Depth 1000000.
Check actual_exchange_decodes_response.
Print Assumptions actual_exchange_decodes_response.
Check actual_exchange_decodes_then_eof.
Print Assumptions actual_exchange_decodes_then_eof.
Check gateway_cleanup_reference_runtime.
Check gateway_cleanup_graph_operation.
Check gateway_reap_with_reference_scope.
Print Assumptions gateway_reap_with_reference_scope.
Check gateway_clock_with_reference_scope.
Print Assumptions gateway_clock_with_reference_scope.
Check actual_exchange_closes_owned_endpoints.
Print Assumptions actual_exchange_closes_owned_endpoints.
Check actual_exchange_cleanup_reap.
Print Assumptions actual_exchange_cleanup_reap.
Check actual_exchange_cleanup_restore.
Print Assumptions actual_exchange_cleanup_restore.
