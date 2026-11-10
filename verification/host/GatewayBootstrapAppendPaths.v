(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual engine/result suffix calls use their source globals and offsets. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewaySourcePaths GatewayFramedRuntime
  GatewayBootstrapABI GatewayBootstrapSource GatewayBootstrapCopySource GatewayBootstrapCopyPaths
  GatewayBootstrapCopyAddress GatewayBootstrapCopyEdges GatewayBootstrapLengthBindings.
Import ListNotations.
Open Scope Z_scope.

Theorem actual_bootstrap_append_source_path {World Event} (backend : gateway_backend World Event)
    (ge : Clight.genv) (engine : bool) information resolved temporaries memory property destination literal symbol offset :
  gateway_ambient_closed backend property ->
  Genv.find_symbol ge (if engine then _host_engine else _host_default_results) = Some destination ->
  Genv.find_symbol ge (if engine then _executable else _results) = Some literal ->
  Genv.find_symbol ge _memcpy = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some (gateway_bootstrap_signature gateway_memory_copy_api) ->
  temporaries ! (if engine then _root_size else _api_size) = Some (Vlong (Int64.repr offset)) ->
  0 <= offset <= Int64.max_unsigned ->
  gateway_source_path backend ge (gateway_bootstrap_signature gateway_memory_copy_api)
    [Vptr destination (Ptrofs.repr offset); Vptr literal Ptrofs.zero;
     Vlong (Int64.repr (if engine then 19 else 21))]
    (bootstrap_copy_cont (if engine then 3 else 5) information resolved temporaries) property
    (State f_host_bootstrap (bootstrap_copy_after (if engine then 3 else 5)) Kstop
      (bootstrap_environment information resolved) temporaries memory) property.
Proof.
  intros CLOSED DESTINATION LITERAL SYMBOL FUNCTION OFFSET WIDTH.
  destruct engine.
  all: eapply gateway_bootstrap_direct_copy_path;
    [exact CLOSED |reflexivity |exact SYMBOL |exact FUNCTION |].
  all: intros before world GOOD; split.
  all: try solve [eapply gateway_bootstrap_array_offset;
    [reflexivity |exact DESTINATION |exact OFFSET |exact WIDTH]].
  all: split.
  all: try solve [eapply gateway_bootstrap_global_array_reference; [reflexivity |exact LITERAL]].
  all: split.
  all: try solve [apply gateway_bootstrap_sizeof_expression].
  all: split; [reflexivity |].
  all: split; reflexivity.
Qed.

Theorem actual_bootstrap_engine_prefix_path {World Event} (backend : gateway_backend World Event)
    (ge : Clight.genv) information resolved temporaries memory property destination origin symbol count :
  gateway_ambient_closed backend property ->
  Genv.find_symbol ge _host_engine = Some destination -> Genv.find_symbol ge _host_root = Some origin ->
  Genv.find_symbol ge _memcpy = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some (gateway_bootstrap_signature gateway_memory_copy_api) ->
  temporaries ! _root_size = Some (Vlong count) ->
  gateway_source_path backend ge (gateway_bootstrap_signature gateway_memory_copy_api)
    [Vptr destination Ptrofs.zero; Vptr origin Ptrofs.zero; Vlong count]
    (bootstrap_copy_cont 2 information resolved temporaries) property
    (State f_host_bootstrap (bootstrap_copy_after 2) Kstop
      (bootstrap_environment information resolved) temporaries memory) property.
Proof.
  intros CLOSED DESTINATION ORIGIN SYMBOL FUNCTION COUNT.
  eapply gateway_bootstrap_direct_copy_path;
    [exact CLOSED |reflexivity |exact SYMBOL |exact FUNCTION |].
  intros before world GOOD; split.
  - eapply gateway_bootstrap_global_array_reference; [reflexivity |exact DESTINATION].
  - split.
    + eapply gateway_bootstrap_global_array_reference; [reflexivity |exact ORIGIN].
    + split; [apply old_expression_value, value_temp; exact COUNT |].
      split; [reflexivity |]. split; reflexivity.
Qed.
