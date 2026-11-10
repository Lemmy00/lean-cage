(* SPDX-License-Identifier: Apache-2.0 *)
(* §REQ-proof-integrity.statement: Inspect actual caller cuts, primitive inputs and full native-row connections. *)
From HostGateway Require Import GatewayBootstrapHistory GatewayInitializationHistory GatewayReferenceHistoryThreads
  GatewayBootstrapReferenceScope GatewayPendingNativeRows GatewayNativeChannels GatewayExchangeNativePrepared
  GatewaySendNoReceive GatewayDictionaryCallReceipts GatewayDictionarySecondReceipt GatewayDictionaryInsertReceipt
  GatewayDictionaryReleaseReceipts.
Set Printing Depth 100000.
Redirect "source-connection-bootstrap-type" Check @actual_loaded_bootstrap_reference_history.
Redirect "source-connection-bootstrap-assumptions" Print Assumptions actual_loaded_bootstrap_reference_history.
Redirect "source-connection-initializer-type" Check @actual_initializer_bootstrap_reference_history.
Redirect "source-connection-initializer-assumptions" Print Assumptions actual_initializer_bootstrap_reference_history.
Redirect "source-connection-history-profile" Print gateway_bootstrap_python_profile.
Redirect "source-connection-history-scope" Print gateway_reference_history_scope.
Redirect "source-connection-native-pending-type" Check @gateway_actual_pending_spawn_row_leases.
Redirect "source-connection-native-pending-assumptions" Print Assumptions gateway_actual_pending_spawn_row_leases.
Redirect "source-connection-native-entry-type" Check @actual_exchange_entry_pending_native.
Redirect "source-connection-native-entry-assumptions" Print Assumptions actual_exchange_entry_pending_native.
Redirect "source-connection-native-pending-contract" Print gateway_pending_spawn_runtime.
Redirect "source-connection-native-channels-type" Check @gateway_native_execution_channel_evidence.
Redirect "source-connection-native-channels-assumptions" Print Assumptions gateway_native_execution_channel_evidence.
Redirect "source-connection-native-exec-view" Print gateway_native_table_view.
Redirect "source-connection-send-type" Check @gateway_actual_send_no_receive.
Redirect "source-connection-send-assumptions" Print Assumptions gateway_actual_send_no_receive.
Redirect "source-connection-dict-key-type" Check @gateway_actual_dictionary_key_receipt.
Redirect "source-connection-dict-key-assumptions" Print Assumptions gateway_actual_dictionary_key_receipt.
Redirect "source-connection-dict-contains-type" Check @gateway_actual_dictionary_contains_receipt.
Redirect "source-connection-dict-contains-assumptions" Print Assumptions gateway_actual_dictionary_contains_receipt.
Redirect "source-connection-dict-second-type" Check @gateway_actual_dictionary_second_receipt.
Redirect "source-connection-dict-second-assumptions" Print Assumptions gateway_actual_dictionary_second_receipt.
Redirect "source-connection-dict-insert-type" Check @gateway_actual_dictionary_insert_receipt.
Redirect "source-connection-dict-insert-assumptions" Print Assumptions gateway_actual_dictionary_insert_receipt.
Redirect "source-connection-dict-release-key-type" Check @gateway_actual_dictionary_release_key_receipt.
Redirect "source-connection-dict-release-key-assumptions" Print Assumptions gateway_actual_dictionary_release_key_receipt.
Redirect "source-connection-dict-release-child-type" Check @gateway_actual_dictionary_release_child_receipt.
Redirect "source-connection-dict-release-child-assumptions" Print Assumptions gateway_actual_dictionary_release_child_receipt.
