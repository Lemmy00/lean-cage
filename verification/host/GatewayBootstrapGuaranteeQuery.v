(* SPDX-License-Identifier: Apache-2.0 *)
(* §REQ-proof-integrity.statement: Inspect the complete source bootstrap types and transitive foundations. *)
From HostGateway Require Import GatewayBootstrapGuarantee GatewayBootstrapLoaderSetup
  GatewayBootstrapLoadedSetup GatewayBootstrapRealpathSetup GatewayBootstrapCanonicalSetup
  GatewayBootstrapRuntime GatewayBootstrapRegions GatewayLoaderRegions GatewayBootstrapReturn
  GatewayBootstrapCapacities GatewayBootstrapBuffers GatewayInitializationBootstrap
  GatewayBootstrapDescriptors GatewayInitializerProtection GatewayProtectedMemory GatewayProtectedThreads
  GatewayProtectedBootstrap.
Set Printing Depth 100000.
Redirect "bootstrap-guarantee-call-type" Check @actual_bootstrap_call_return.
Redirect "bootstrap-guarantee-loaded-type" Check @actual_loaded_bootstrap_return.
Redirect "bootstrap-guarantee-call-assumptions" Print Assumptions actual_bootstrap_call_return.
Redirect "bootstrap-guarantee-loaded-assumptions" Print Assumptions actual_loaded_bootstrap_return.
Redirect "bootstrap-guarantee-names" Print gateway_bootstrap_named_paths.
Redirect "bootstrap-guarantee-loaded-paths" Print gateway_bootstrap_loaded_paths.
Redirect "bootstrap-guarantee-resolved-paths" Print gateway_bootstrap_resolved_paths.
Redirect "bootstrap-guarantee-checked-paths" Print gateway_bootstrap_checked_paths.
Redirect "bootstrap-guarantee-runtime" Print gateway_bootstrap_runtime.
Redirect "bootstrap-guarantee-storage" Print gateway_native_storage_boundary.
Redirect "bootstrap-guarantee-loader" Print gateway_native_loader_boundary.
Redirect "bootstrap-guarantee-paths" Print gateway_bootstrap_paths.
Redirect "bootstrap-guarantee-buffers" Print gateway_bootstrap_buffers.
Redirect "bootstrap-guarantee-capacity" Print gateway_bootstrap_capacity.
Redirect "bootstrap-guarantee-storage-selection" Print gateway_native_storage_selected.
Redirect "bootstrap-guarantee-initializer-type" Check @gateway_actual_initializer_bootstrap.
Redirect "bootstrap-guarantee-initializer-assumptions" Print Assumptions gateway_actual_initializer_bootstrap.
Redirect "bootstrap-guarantee-initializer-call" Check @actual_initializer_bootstrap_call_edge.
Redirect "bootstrap-guarantee-initializer-guard" Check @actual_initializer_derives_bootstrap_zero.
Redirect "bootstrap-guarantee-descriptors-type" Check @actual_loaded_bootstrap_descriptors.
Redirect "bootstrap-guarantee-descriptors-assumptions" Print Assumptions actual_loaded_bootstrap_descriptors.
Redirect "bootstrap-guarantee-readonly-mapping" Print gateway_native_readonly_mapping.
Redirect "bootstrap-guarantee-protected-memory" Print gateway_protected_memory.
Redirect "bootstrap-guarantee-protected-native" Print gateway_protected_native.
Redirect "bootstrap-guarantee-protected-threads" Check @gateway_protected_threads.
Redirect "bootstrap-guarantee-protected-bootstrap" Check @gateway_protected_bootstrap.
