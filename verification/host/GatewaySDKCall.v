(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Actual source SDK calls use the pinned declarations and arguments. *)
From Stdlib Require Import List.
From compcert Require Import Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewaySpawnABI.
Import ListNotations.

Definition gateway_sdk_argument_types api:list type:=
  match gateway_spawn_signature api with External _ arguments _ _=>arguments|_=>[]end.

Theorem gateway_sdk_source_call(ge:Clight.genv)function destination api expressions arguments continuation environment temporaries memory symbol:
  environment!(gateway_spawn_identifier api)=None->
  Genv.find_symbol ge(gateway_spawn_identifier api)=Some symbol->
  Genv.find_funct_ptr ge symbol=Some(gateway_spawn_signature api)->
  argument_values ge environment temporaries memory expressions(gateway_sdk_argument_types api)arguments->
  store_edge ge
    (State function(Scall destination(Evar(gateway_spawn_identifier api)
      (Tfunction(gateway_sdk_argument_types api)tint cc_default))expressions)continuation environment temporaries memory)
    (Callstate(gateway_spawn_signature api)arguments(Kcall destination function environment temporaries continuation)memory).
Proof.
  intros UNSHADOWED SYMBOL FUNCTION ARGUMENTS;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value;eapply value_function;[exact UNSHADOWED|exact SYMBOL|reflexivity].
  - exact ARGUMENTS.
  - cbn;exact FUNCTION.
  - destruct api;reflexivity.
Qed.
