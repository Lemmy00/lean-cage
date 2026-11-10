(* SPDX-License-Identifier: Apache-2.0 *)
(* §REQ-proof-integrity.statement: Inspect actual callback entry, flag load, allocation and denial inputs. *)
From HostGateway Require Import GatewayPublicInitializationCaller GatewayPublicInitializationBoundary
  GatewayPublicInitializationGuard GatewayPublicInitializationContexts GatewayInitializationAllocation GatewayFunctionEntryBoundary.
Set Printing Depth 100000.
Redirect "public-initialization-caller-type" Check @gateway_actual_uninitialized_callback.
Redirect "public-initialization-caller-assumptions" Print Assumptions gateway_actual_uninitialized_callback.
Redirect "public-initialization-body-type" Check @gateway_uninitialized_callback_excludes_operation.
Redirect "public-initialization-body-assumptions" Print Assumptions gateway_uninitialized_callback_excludes_operation.
Redirect "public-initialization-guard-type" Check @gateway_public_guard_source_prefix.
Redirect "public-initialization-guard-assumptions" Print Assumptions gateway_public_guard_source_prefix.
Redirect "public-initialization-globals-type" Check @actual_public_guard_global_scope.
Redirect "public-initialization-globals-assumptions" Print Assumptions actual_public_guard_global_scope.
Redirect "public-initialization-cells-type" Check @gateway_initialization_cells_allocate.
Redirect "public-initialization-cells-assumptions" Print Assumptions gateway_initialization_cells_allocate.
Redirect "public-initialization-allocations-type" Check @gateway_initialization_rooted_entry.
Redirect "public-initialization-allocations-assumptions" Print Assumptions gateway_initialization_rooted_entry.
Redirect "public-initialization-entry-type" Check @actual_gateway_entry_before_external.
Redirect "public-initialization-entry-assumptions" Print Assumptions actual_gateway_entry_before_external.
Redirect "public-initialization-context-type" Check @gateway_initialization_context_public_cells.
Redirect "public-initialization-context-assumptions" Print Assumptions gateway_initialization_context_public_cells.
Redirect "public-initialization-definition-owners" Print public_guard_owner.
Redirect "public-initialization-definition-target" Print public_guard_target.
Redirect "public-initialization-definition-source-only-error" Print public_denial_api.
