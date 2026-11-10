(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Lexically selected constructors receive the actual exact ABI operands. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayJsonNumberSource GatewayJsonNumberSourcePhases
  GatewayNumberConstruction GatewayBindings GatewayObjects GatewaySourcePaths GatewayFramedRuntime.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_json_number_long_call {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) parameters memory symbol definition :
  gateway_ambient_closed backend property ->
  Genv.find_symbol ge _PyLong_FromLong = Some symbol -> Genv.find_funct_ptr ge symbol = Some definition ->
  type_of_fundef definition = Tfunction [tlong] (tptr (Tstruct __object noattr)) cc_default ->
  gateway_source_path backend ge definition [Vlong (Int64.repr 0)] (gateway_number_zero_cont parameters) property
    (State f_host_json_number json_number_long_call json_lexical_long_cont empty_env parameters memory) property.
Proof.
  intros CLOSED SYMBOL FUNCTION TYPE.
  eapply gateway_source_same with (target := Callstate definition [Vlong (Int64.repr 0)] (gateway_number_zero_cont parameters) memory).
  - exact CLOSED.
  - cbn; tauto.
  - intros; eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero).
    + reflexivity.
    + apply old_expression_value; eapply value_function; [reflexivity |exact SYMBOL |reflexivity].
    + apply cons_argument_values with (v := Vint Int.zero);
        [apply old_expression_value, value_int |reflexivity |apply no_argument_values].
    + exact FUNCTION.
    + exact TYPE.
  - apply gateway_source_reached; auto.
Qed.

Theorem gateway_json_number_decode_call {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) parameters object count memory symbol definition mode_symbol :
  gateway_ambient_closed backend property ->
  parameters ! _bytes = Some (Vptr object Ptrofs.zero) -> parameters ! _size = Some (Vlong (Int64.repr count)) ->
  Genv.find_symbol ge _PyUnicode_DecodeUTF8 = Some symbol -> Genv.find_funct_ptr ge symbol = Some definition ->
  type_of_fundef definition = Tfunction [tptr tschar; tlong; tptr tschar] (tptr (Tstruct __object noattr)) cc_default ->
  Genv.find_symbol ge ___stringlit_8 = Some mode_symbol ->
  gateway_source_path backend ge definition [Vptr object Ptrofs.zero; Vlong (Int64.repr count); Vptr mode_symbol Ptrofs.zero]
    (gateway_number_decode_cont parameters) property
    (State f_host_json_number json_number_decode_call json_lexical_decode_cont empty_env parameters memory) property.
Proof.
  intros CLOSED BYTES SIZE SYMBOL FUNCTION TYPE MODE.
  eapply gateway_source_same with (target := Callstate definition
    [Vptr object Ptrofs.zero; Vlong (Int64.repr count); Vptr mode_symbol Ptrofs.zero] (gateway_number_decode_cont parameters) memory).
  - exact CLOSED.
  - cbn; tauto.
  - intros; eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero).
    + reflexivity.
    + apply old_expression_value; eapply value_function; [reflexivity |exact SYMBOL |reflexivity].
    + apply cons_argument_values with (v := Vptr object Ptrofs.zero).
      * apply old_expression_value, value_temp; exact BYTES.
      * reflexivity.
      * apply cons_argument_values with (v := Vlong (Int64.repr count)).
        -- apply cast_expression_value with (v := Vlong (Int64.repr count));
             [apply old_expression_value, value_temp; exact SIZE |reflexivity].
        -- reflexivity.
        -- apply cons_argument_values with (v := Vptr mode_symbol Ptrofs.zero).
           ++ eapply location_read_value; [apply global_location_value; [reflexivity |exact MODE] |].
              apply deref_loc_reference; reflexivity.
           ++ reflexivity.
           ++ apply no_argument_values.
    + exact FUNCTION.
    + exact TYPE.
  - apply gateway_source_reached; auto.
Qed.

Theorem gateway_actual_json_number_api_bindings :
  (exists definition, gateway_object_api_definition gateway_api_long_signed = Some definition /\
    gateway_function_binding (Clight.globalenv prog) _PyLong_FromLong definition /\
    type_of_fundef definition = Tfunction [tlong] (tptr (Tstruct __object noattr)) cc_default) /\
  (exists definition, gateway_object_api_definition gateway_api_unicode_utf8 = Some definition /\
    gateway_function_binding (Clight.globalenv prog) _PyUnicode_DecodeUTF8 definition /\
    type_of_fundef definition = Tfunction [tptr tschar; tlong; tptr tschar] (tptr (Tstruct __object noattr)) cc_default) /\
  (exists mode_symbol, Genv.find_symbol (Clight.globalenv prog) ___stringlit_8 = Some mode_symbol).
Proof.
  split.
  - eexists; split; [reflexivity |]. split;
      [apply gateway_actual_function_binding; vm_compute; reflexivity |reflexivity].
  - split.
    + eexists; split; [reflexivity |]. split;
        [apply gateway_actual_function_binding; vm_compute; reflexivity |reflexivity].
    + eexists; vm_compute; reflexivity.
Qed.
