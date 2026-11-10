(* SPDX-License-Identifier: Apache-2.0 *)
(* §REQ-proof-integrity.statement: Review the actual source key, primitive bridge and held-entry consumer. *)
From HostGateway Require Import GatewayNativeRows GatewayNativeReferences GatewayNativeSourceLeases
  GatewayNativeSourceBinding GatewayNativeSpawnOperands.
Set Printing Depth 100000.
Redirect "native-rows-source-type" Check @gateway_actual_pending_spawn_key.
Redirect "native-rows-binding-type" Check @gateway_actual_spawn_row.
Redirect "native-rows-leases-type" Check @gateway_actual_spawn_row_leases.
Redirect "native-rows-source-assumptions" Print Assumptions gateway_actual_pending_spawn_key.
Redirect "native-rows-binding-assumptions" Print Assumptions gateway_actual_spawn_row.
Redirect "native-rows-leases-assumptions" Print Assumptions gateway_actual_spawn_row_leases.
Redirect "native-rows-pending" Print gateway_native_pending_spawn.
Redirect "native-rows-runtime" Print gateway_native_row_runtime.
Redirect "native-rows-inputs" Print gateway_native_operation_inputs.
Redirect "native-rows-arguments" Print gateway_native_spawn_operands.
Redirect "native-rows-sdk-view" Print gateway_native_sdk_view.
Redirect "native-rows-reference-runtime" Print gateway_native_reference_runtime.
Redirect "native-rows-source-leases" Print gateway_native_leased_references.
Redirect "native-rows-one-lease" Print gateway_native_lease_at.
Redirect "native-rows-shared-key" Print gateway_native_shared_key.
