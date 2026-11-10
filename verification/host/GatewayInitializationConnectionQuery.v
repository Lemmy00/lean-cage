(* SPDX-License-Identifier: Apache-2.0 *)
(* §REQ-proof-integrity.statement: Inspect the public source path, actual flags and each primitive input. *)
From HostGateway Require Import GatewayInitializationConnection GatewayInitializationCaller GatewayInitializationGuarded
  GatewayInitializationResult GatewayInitializationInterpreter GatewayInitializationRegions GatewayBootstrapFlagged
  GatewayInterpreterRuntime GatewayBootstrapProtectedHistory GatewayInitializationFlags.
Set Printing Depth 100000.
Redirect "initialization-connection-public-type" Check @gateway_actual_public_bootstrap_connection.
Redirect "initialization-connection-public-assumptions" Print Assumptions gateway_actual_public_bootstrap_connection.
Redirect "initialization-connection-loaded-body-type" Check @gateway_actual_loaded_initialization_body.
Redirect "initialization-connection-loaded-body-assumptions" Print Assumptions gateway_actual_loaded_initialization_body.
Redirect "initialization-connection-guard-type" Check @gateway_actual_initialization_guarded_path.
Redirect "initialization-connection-guard-assumptions" Print Assumptions gateway_actual_initialization_guarded_path.
Redirect "initialization-connection-null-type" Check @gateway_actual_initialization_null_body.
Redirect "initialization-connection-null-assumptions" Print Assumptions gateway_actual_initialization_null_body.
Redirect "initialization-connection-interpreter-type" Check @gateway_actual_initialization_interpreter.
Redirect "initialization-connection-interpreter-assumptions" Print Assumptions gateway_actual_initialization_interpreter.
Redirect "initialization-connection-flagged-type" Check @gateway_actual_bootstrap_flagged.
Redirect "initialization-connection-flagged-assumptions" Print Assumptions gateway_actual_bootstrap_flagged.
Redirect "initialization-connection-interpreter-runtime" Print gateway_interpreter_runtime.
Redirect "initialization-connection-interpreter-post" Print gateway_interpreter_query_post.
Redirect "initialization-connection-loaded-regions" Print gateway_initialization_regions.
Redirect "initialization-connection-flag-state" Print gateway_initialization_flag_state.
Redirect "initialization-connection-protected-selection" Print gateway_initialization_guarded_object.
Redirect "initialization-connection-immutable-selection" Print gateway_initialization_immutable_object.
