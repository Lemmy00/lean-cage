(* SPDX-License-Identifier: Apache-2.0 *)
(* §REQ-proof-integrity.statement: Inspect actual initializer setup, rejection and SDK boundaries. *)
From HostGateway Require Import GatewayInitializerObjectsSource GatewayInitializerGlobalStores GatewayInitializerObjectFrontiers GatewayInitializerObjectBindings GatewayInitializerObjectFailures GatewayInitializerObjectLiterals GatewayInitializerSDK GatewayExternalFrontier GatewayInitializerImport GatewaySourceBoundaryCuts GatewayInitializationRejectionSource GatewayInitializationRejectionBoundary GatewayInitializationInventory.
Set Printing Depth 100000.
Redirect "initializer-objects-00-type" Check @gateway_actual_initializer_import.
Redirect "initializer-objects-00-assumptions" Print Assumptions gateway_actual_initializer_import.
Redirect "initializer-objects-01-type" Check @gateway_initializer_pointer_store.
Redirect "initializer-objects-01-assumptions" Print Assumptions gateway_initializer_pointer_store.
Redirect "initializer-objects-02-type" Check @gateway_actual_initializer_pointer_store.
Redirect "initializer-objects-02-assumptions" Print Assumptions gateway_actual_initializer_pointer_store.
Redirect "initializer-objects-03-type" Check @gateway_initializer_import_source.
Redirect "initializer-objects-03-assumptions" Print Assumptions gateway_initializer_import_source.
Redirect "initializer-objects-04-type" Check @gateway_initializer_attribute_source.
Redirect "initializer-objects-04-assumptions" Print Assumptions gateway_initializer_attribute_source.
Redirect "initializer-objects-05-type" Check @gateway_initializer_path_store_frontier.
Redirect "initializer-objects-05-assumptions" Print Assumptions gateway_initializer_path_store_frontier.
Redirect "initializer-objects-06-type" Check @gateway_initializer_cancel_store_frontier.
Redirect "initializer-objects-06-assumptions" Print Assumptions gateway_initializer_cancel_store_frontier.
Redirect "initializer-objects-07-type" Check @gateway_initializer_outcome_store_frontier.
Redirect "initializer-objects-07-assumptions" Print Assumptions gateway_initializer_outcome_store_frontier.
Redirect "initializer-objects-08-type" Check @gateway_initializer_pathlib_release_source.
Redirect "initializer-objects-08-assumptions" Print Assumptions gateway_initializer_pathlib_release_source.
Redirect "initializer-objects-09-type" Check @gateway_initializer_module_source.
Redirect "initializer-objects-09-assumptions" Print Assumptions gateway_initializer_module_source.
Redirect "initializer-objects-10-type" Check @gateway_initializer_workspace_source.
Redirect "initializer-objects-10-assumptions" Print Assumptions gateway_initializer_workspace_source.
Redirect "initializer-objects-11-type" Check @gateway_initializer_workspace_publication_source.
Redirect "initializer-objects-11-assumptions" Print Assumptions gateway_initializer_workspace_publication_source.
Redirect "initializer-objects-12-type" Check @gateway_initializer_cancel_source.
Redirect "initializer-objects-12-assumptions" Print Assumptions gateway_initializer_cancel_source.
Redirect "initializer-objects-13-type" Check @gateway_initializer_cancel_publication_source.
Redirect "initializer-objects-13-assumptions" Print Assumptions gateway_initializer_cancel_publication_source.
Redirect "initializer-objects-14-type" Check @gateway_initializer_outcome_source.
Redirect "initializer-objects-14-assumptions" Print Assumptions gateway_initializer_outcome_source.
Redirect "initializer-objects-15-type" Check @gateway_initializer_outcome_publication_source.
Redirect "initializer-objects-15-assumptions" Print Assumptions gateway_initializer_outcome_publication_source.
Redirect "initializer-objects-16-type" Check @gateway_actual_initializer_object_bindings.
Redirect "initializer-objects-16-assumptions" Print Assumptions gateway_actual_initializer_object_bindings.
Redirect "initializer-objects-17-type" Check @gateway_actual_initializer_object_symbols.
Redirect "initializer-objects-17-assumptions" Print Assumptions gateway_actual_initializer_object_symbols.
Redirect "initializer-objects-18-type" Check @gateway_initializer_object_name_bytes.
Redirect "initializer-objects-18-assumptions" Print Assumptions gateway_initializer_object_name_bytes.
Redirect "initializer-objects-19-type" Check @gateway_actual_external_frontier.
Redirect "initializer-objects-19-assumptions" Print Assumptions gateway_actual_external_frontier.
Redirect "initializer-objects-20-type" Check @gateway_source_segment_external_cut.
Redirect "initializer-objects-20-assumptions" Print Assumptions gateway_source_segment_external_cut.
Redirect "initializer-objects-21-type" Check @gateway_active_initializer_excludes_operation.
Redirect "initializer-objects-21-assumptions" Print Assumptions gateway_active_initializer_excludes_operation.
Redirect "initializer-objects-22-type" Check @gateway_completed_initializer_excludes_operation.
Redirect "initializer-objects-22-assumptions" Print Assumptions gateway_completed_initializer_excludes_operation.
Redirect "initializer-objects-23-type" Check @gateway_actual_class_global_writer.
Redirect "initializer-objects-23-assumptions" Print Assumptions gateway_actual_class_global_writer.
Redirect "initializer-objects-24-type" Check @gateway_actual_private_initializer_caller.
Redirect "initializer-objects-24-assumptions" Print Assumptions gateway_actual_private_initializer_caller.
Redirect "initializer-objects-25-type" Check @actual_initialization_class_writer_inventory.
Redirect "initializer-objects-25-assumptions" Print Assumptions actual_initialization_class_writer_inventory.
Redirect "initializer-objects-26-type" Check @actual_initialization_private_caller_inventory.
Redirect "initializer-objects-26-assumptions" Print Assumptions actual_initialization_private_caller_inventory.
Redirect "initializer-objects-27-type" Check @actual_initialization_indirect_call_inventory.
Redirect "initializer-objects-27-assumptions" Print Assumptions actual_initialization_indirect_call_inventory.
Redirect "initializer-objects-28-type" Check @actual_initialization_class_address_inventory.
Redirect "initializer-objects-28-assumptions" Print Assumptions actual_initialization_class_address_inventory.
Redirect "initializer-objects-29-type" Check @gateway_initializer_import_failed.
Redirect "initializer-objects-29-assumptions" Print Assumptions gateway_initializer_import_failed.
Redirect "initializer-objects-30-type" Check @gateway_initializer_module_failed.
Redirect "initializer-objects-30-assumptions" Print Assumptions gateway_initializer_module_failed.
Redirect "initializer-objects-31-type" Check @gateway_initializer_workspace_failed.
Redirect "initializer-objects-31-assumptions" Print Assumptions gateway_initializer_workspace_failed.
Redirect "initializer-objects-32-type" Check @gateway_initializer_path_failed.
Redirect "initializer-objects-32-assumptions" Print Assumptions gateway_initializer_path_failed.
Redirect "initializer-objects-33-type" Check @gateway_initializer_cancel_failed.
Redirect "initializer-objects-33-assumptions" Print Assumptions gateway_initializer_cancel_failed.
Redirect "initializer-objects-34-type" Check @gateway_initializer_outcome_failed.
Redirect "initializer-objects-34-assumptions" Print Assumptions gateway_initializer_outcome_failed.
Redirect "initializer-objects-35-type" Check @gateway_initializer_workspace_publication_failed.
Redirect "initializer-objects-35-assumptions" Print Assumptions gateway_initializer_workspace_publication_failed.
Redirect "initializer-objects-36-type" Check @gateway_initializer_cancel_publication_failed.
Redirect "initializer-objects-36-assumptions" Print Assumptions gateway_initializer_cancel_publication_failed.
Redirect "initializer-objects-37-type" Check @gateway_initializer_outcome_publication_failed.
Redirect "initializer-objects-37-assumptions" Print Assumptions gateway_initializer_outcome_publication_failed.
Redirect "initializer-objects-interface-00" Print gateway_initializer_sdk.
Redirect "initializer-objects-interface-01" Print gateway_initializer_new_reference.
Redirect "initializer-objects-interface-02" Print gateway_initializer_reference_debit.
Redirect "initializer-objects-interface-03" Print initialization_statement_any.
Redirect "initializer-objects-interface-04" Print initialization_class_store.
Redirect "initializer-objects-interface-05" Print initialization_private_call.
Redirect "initializer-objects-interface-06" Print initialization_unknown_call.
Redirect "initializer-objects-interface-07" Print initialization_class_address.
Redirect "initializer-objects-interface-08" Print initialization_expression_exposure.
Redirect "initializer-objects-interface-09" Print initialization_writer_entry.
Redirect "initializer-objects-interface-10" Print initialization_caller_entry.
Redirect "initializer-objects-interface-11" Print initialization_call_classification_entry.
Redirect "initializer-objects-interface-12" Print initialization_unexposed_entry.
