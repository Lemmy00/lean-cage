(* SPDX-License-Identifier: Apache-2.0 *)
(* §REQ-proof-integrity.statement: Inspect real success/failure flag stores and exception-capable cleanup inputs. *)
From HostGateway Require Import GatewayInitializationCompletion GatewayInitializationFailure
  GatewayInitializationCompletionSource GatewayInitializationCells GatewayReturnScope GatewayAttachedNative.
Set Printing Depth 100000.
Redirect "initialization-return-success-type" Check @gateway_actual_initialization_completed.
Redirect "initialization-return-success-assumptions" Print Assumptions gateway_actual_initialization_completed.
Redirect "initialization-return-failure-type" Check @gateway_actual_initialization_failed.
Redirect "initialization-return-failure-assumptions" Print Assumptions gateway_actual_initialization_failed.
Redirect "initialization-return-owned-module-type" Check @gateway_initialization_owned_module_live.
Redirect "initialization-return-owned-module-assumptions" Print Assumptions gateway_initialization_owned_module_live.
Redirect "initialization-return-source-success-type" Check @gateway_initialization_completion_script.
Redirect "initialization-return-source-success-assumptions" Print Assumptions gateway_initialization_completion_script.
Redirect "initialization-return-source-failure-type" Check @gateway_initialization_failure_script.
Redirect "initialization-return-source-failure-assumptions" Print Assumptions gateway_initialization_failure_script.
Redirect "initialization-return-cell-store-type" Check @gateway_initialization_cells_store.
Redirect "initialization-return-cell-store-assumptions" Print Assumptions gateway_initialization_cells_store.
Redirect "initialization-return-terminal-type" Check @gateway_terminal_return_scope.
Redirect "initialization-return-terminal-assumptions" Print Assumptions gateway_terminal_return_scope.
Redirect "initialization-return-attached-runtime" Print gateway_attached_native_runtime.
Redirect "initialization-return-failure-context" Print gateway_initialization_failure_context.
Redirect "initialization-return-cells" Print gateway_initialization_cells.
