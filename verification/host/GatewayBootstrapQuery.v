(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Inspect full imported native path computation. *)
From HostGateway Require Import GatewayBootstrapImport GatewayBootstrapRuntime GatewayLoaderRegions.
Set Printing All.
Set Printing Depth 100000.
Redirect "bootstrap-code-supported" Print LeanCage_Host_BootstrapCode_supported.
Redirect "bootstrap-code-layout" Print LeanCage_Host_BootstrapCode_layout.
Redirect "bootstrap-code-suffix" Print LeanCage_Host_BootstrapCode_suffix.
Check LeanCage_Host_BootstrapCode_suffix.
Check LeanCage_Host_BootstrapCode_Layout.
Check gateway_bootstrap_runtime.
Check gateway_native_loader_boundary.
