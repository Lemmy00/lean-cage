(* SPDX-License-Identifier: Apache-2.0 *)
(* §REQ-proof-integrity.statement: Print the complete same-call numeric lexer/constructor connection. *)
From HostGateway Require Import GatewayJsonNumberSourceConnection GatewayJsonNumberSourceLexical
  GatewayJsonNumberCallEntry GatewayJsonNumberSourceCalls GatewayJsonNumberLexical GatewayJsonNumberSourceIntegerPrefix
  GatewayJsonNumberSourceFraction GatewayJsonNumberSourceExponent GatewayJsonNumberSourceIntegerFold
  GatewayJsonNumberSourceFold GatewayJsonNumberSource.
Set Printing Depth 100000.
Redirect "number-source-constructor-type" Check @gateway_actual_json_number_constructor.
Redirect "number-source-constructor-assumptions" Print Assumptions gateway_actual_json_number_constructor.
Redirect "number-source-lexical-source-type" Check @gateway_actual_json_number_lexical_source.
Redirect "number-source-lexical-source-assumptions" Print Assumptions gateway_actual_json_number_lexical_source.
Redirect "number-source-entry-type" Check @gateway_actual_json_number_call_entry.
Redirect "number-source-entry-assumptions" Print Assumptions gateway_actual_json_number_call_entry.
Redirect "number-source-long-call-type" Check @gateway_json_number_long_call.
Redirect "number-source-long-call-assumptions" Print Assumptions gateway_json_number_long_call.
Redirect "number-source-decode-call-type" Check @gateway_json_number_decode_call.
Redirect "number-source-decode-call-assumptions" Print Assumptions gateway_json_number_decode_call.
Redirect "number-source-bindings-type" Check @gateway_actual_json_number_api_bindings.
Redirect "number-source-bindings-assumptions" Print Assumptions gateway_actual_json_number_api_bindings.
Redirect "number-source-lexical-type" Check @json_number_lexical_sound.
Redirect "number-source-lexical-assumptions" Print Assumptions json_number_lexical_sound.
Redirect "number-source-integer-type" Check @gateway_json_number_integer_source.
Redirect "number-source-integer-assumptions" Print Assumptions gateway_json_number_integer_source.
Redirect "number-source-fraction-type" Check @gateway_json_number_fraction_source.
Redirect "number-source-fraction-assumptions" Print Assumptions gateway_json_number_fraction_source.
Redirect "number-source-exponent-type" Check @gateway_json_number_exponent_source.
Redirect "number-source-exponent-assumptions" Print Assumptions gateway_json_number_exponent_source.
Redirect "number-source-integer-fold-type" Check @gateway_json_number_integer_digits.
Redirect "number-source-integer-fold-assumptions" Print Assumptions gateway_json_number_integer_digits.
Redirect "number-source-fraction-exponent-fold-type" Check @gateway_json_number_scan_digits.
Redirect "number-source-fraction-exponent-fold-assumptions" Print Assumptions gateway_json_number_scan_digits.
Redirect "number-source-invalid-type" Check @gateway_json_number_invalid_denied.
Redirect "number-source-invalid-assumptions" Print Assumptions gateway_json_number_invalid_denied.
Redirect "number-source-definition-json_number_selected_api" Print json_number_selected_api.
Redirect "number-source-definition-json_number_selected_arguments" Print json_number_selected_arguments.
Redirect "number-source-definition-json_number_selected_cont" Print json_number_selected_cont.
Redirect "number-source-definition-json_number_lexical" Print json_number_lexical.
Redirect "number-source-definition-json_number_parts" Print json_number_parts.
