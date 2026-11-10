(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Dictionary guards consume the same source-selected SDK returns. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayValueEntry GatewayContainerLoopSource
  GatewayContainerDictionarySource GatewayReferenceDictionaryChild GatewaySourceIntegerReceipt GatewayObjects GatewayFramedRuntime.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_actual_dictionary_key_receipt {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) slots parameters key key_offset before world events value after next
    symbol definition unicode :
  gateway_object_api_definition gateway_api_is_instance = Some definition ->
  gateway_ambient_closed backend property ->
  (forall memory current returned changed following observed, property memory current ->
    gateway_object_operation backend gateway_api_is_instance [Vptr key key_offset; Vptr unicode Ptrofs.zero]
      memory current returned changed following observed -> exists status, returned = Vint status) ->
  (forall memory world, property memory world -> Mem.weak_valid_pointer memory key (Ptrofs.unsigned key_offset) = true) ->
  (forall memory world, property memory world -> Mem.loadv Mint64 memory (Vptr (gateway_value_tag_slot slots) Ptrofs.zero) =
    Some (Vlong (Int64.repr 8))) ->
  Genv.find_symbol ge _PyObject_IsInstance = Some symbol -> Genv.find_funct_ptr ge symbol = Some definition ->
  Genv.find_symbol ge _PyUnicode_Type = Some unicode ->
  type_of_fundef definition = Tfunction [tptr (Tstruct __object noattr); tptr (Tstruct __object noattr)] tint cc_default ->
  property before world ->
  gateway_steps backend ge
    (gateway_live (Returnstate (Vptr key key_offset) (gateway_container_first_cont slots parameters) before) world) events
    (gateway_live (Returnstate value Kstop after) next) -> value <> Vnullptr ->
  exists called_parameters prefix checking suffix called called_world changed changed_world status,
    events = prefix ++ checking ++ suffix /\
    Forall (fun event => event = gateway_source E0 \/ event = gateway_ambient) prefix /\
    called_parameters ! _first = Some (Vptr key key_offset) /\
    called_parameters ! _container = parameters ! _container /\ called_parameters ! _stream = parameters ! _stream /\
    called_parameters ! _depth = parameters ! _depth /\ called_parameters ! _index__1 = parameters ! _index__1 /\
    property called called_world /\ 0 < Int.signed status /\
    gateway_steps backend ge
      (gateway_live (Returnstate (Vptr key key_offset) (gateway_container_first_cont slots parameters) before) world) prefix
      (gateway_live (Callstate definition [Vptr key key_offset; Vptr unicode Ptrofs.zero]
        (gateway_dictionary_key_cont slots called_parameters) called) called_world) /\
    gateway_steps backend ge
      (gateway_live (Callstate definition [Vptr key key_offset; Vptr unicode Ptrofs.zero] Kstop called) called_world) checking
      (gateway_live (Returnstate (Vint status) Kstop changed) changed_world) /\
    gateway_steps backend ge
      (gateway_live (Returnstate (Vint status) (gateway_dictionary_key_cont slots called_parameters) changed) changed_world) suffix
      (gateway_live (Returnstate value Kstop after) next).
Proof.
  intros DEFINITION CLOSED TYPED POINTER TAG SYMBOL FUNCTION UNICODE TYPE INPUT RUN NONNULL.
  destruct (gateway_dictionary_key_source_path backend ge property slots parameters key key_offset before symbol definition unicode
    CLOSED POINTER TAG SYMBOL FUNCTION UNICODE TYPE)
    as (called_parameters & PATH & FIRST & PARENT & STREAM & DEPTH & INDEX).
  destruct (gateway_source_integer_receipt backend ge gateway_api_is_instance definition
    [Vptr key key_offset; Vptr unicode Ptrofs.zero] (gateway_dictionary_key_cont slots called_parameters) property property
    (Returnstate (Vptr key key_offset) (gateway_container_first_cont slots parameters) before) before world events value after next
    DEFINITION ltac:(cbn; exact I) ltac:(cbn; lia) PATH CLOSED TYPED INPUT RUN)
    as (prefix & checking & suffix & called & called_world & changed & changed_world & status & EVENTS & QUIET & PREFIX & READY & CHECK & REST).
  pose proof (gateway_dictionary_key_success_positive backend ge slots called_parameters status changed changed_world suffix value after next
    REST NONNULL) as POSITIVE.
  exists called_parameters, prefix, checking, suffix, called, called_world, changed, changed_world, status.
  split; [exact EVENTS |]. split; [exact QUIET |]. split; [exact FIRST |]. split; [exact PARENT |].
  split; [exact STREAM |]. split; [exact DEPTH |]. split; [exact INDEX |]. split; [exact READY |].
  split; [exact POSITIVE |]. split; [exact PREFIX |]. split; assumption.
Qed.

Theorem gateway_actual_dictionary_contains_receipt {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) slots parameters parent parent_offset key key_offset key_status
    before world events value after next symbol definition :
  gateway_object_api_definition gateway_api_dict_contains = Some definition ->
  gateway_ambient_closed backend property ->
  (forall memory current returned changed following observed, property memory current ->
    gateway_object_operation backend gateway_api_dict_contains [Vptr parent parent_offset; Vptr key key_offset]
      memory current returned changed following observed -> exists status, returned = Vint status) ->
  parameters ! _container = Some (Vptr parent parent_offset) -> parameters ! _first = Some (Vptr key key_offset) ->
  0 < Int.signed key_status ->
  Genv.find_symbol ge _PyDict_Contains = Some symbol -> Genv.find_funct_ptr ge symbol = Some definition ->
  type_of_fundef definition = Tfunction [tptr (Tstruct __object noattr); tptr (Tstruct __object noattr)] tint cc_default ->
  property before world ->
  gateway_steps backend ge
    (gateway_live (Returnstate (Vint key_status) (gateway_dictionary_key_cont slots parameters) before) world) events
    (gateway_live (Returnstate value Kstop after) next) -> value <> Vnullptr ->
  exists called_parameters prefix checking suffix called called_world changed changed_world,
    events = prefix ++ checking ++ suffix /\
    Forall (fun event => event = gateway_source E0 \/ event = gateway_ambient) prefix /\
    called_parameters ! _string_key = Some (Vint key_status) /\
    called_parameters ! _container = parameters ! _container /\ called_parameters ! _first = parameters ! _first /\
    called_parameters ! _stream = parameters ! _stream /\ called_parameters ! _depth = parameters ! _depth /\
    called_parameters ! _index__1 = parameters ! _index__1 /\ property called called_world /\
    gateway_steps backend ge
      (gateway_live (Returnstate (Vint key_status) (gateway_dictionary_key_cont slots parameters) before) world) prefix
      (gateway_live (Callstate definition [Vptr parent parent_offset; Vptr key key_offset]
        (gateway_dictionary_contains_cont slots called_parameters) called) called_world) /\
    gateway_steps backend ge
      (gateway_live (Callstate definition [Vptr parent parent_offset; Vptr key key_offset] Kstop called) called_world) checking
      (gateway_live (Returnstate (Vint Int.zero) Kstop changed) changed_world) /\
    gateway_steps backend ge
      (gateway_live (Returnstate (Vint Int.zero) (gateway_dictionary_contains_cont slots called_parameters) changed) changed_world) suffix
      (gateway_live (Returnstate value Kstop after) next).
Proof.
  intros DEFINITION CLOSED TYPED PARENT KEY POSITIVE SYMBOL FUNCTION TYPE INPUT RUN NONNULL.
  destruct (gateway_dictionary_contains_source_path backend ge property slots parameters parent parent_offset key key_offset key_status before
    symbol definition CLOSED PARENT KEY POSITIVE SYMBOL FUNCTION TYPE)
    as (called_parameters & PATH & STRING_KEY & CALLED_PARENT & CALLED_KEY & STREAM & DEPTH & INDEX).
  destruct (gateway_source_integer_receipt backend ge gateway_api_dict_contains definition
    [Vptr parent parent_offset; Vptr key key_offset] (gateway_dictionary_contains_cont slots called_parameters) property property
    (Returnstate (Vint key_status) (gateway_dictionary_key_cont slots parameters) before) before world events value after next
    DEFINITION ltac:(cbn; exact I) ltac:(cbn; lia) PATH CLOSED TYPED INPUT RUN)
    as (prefix & checking & suffix & called & called_world & changed & changed_world & status & EVENTS & QUIET & PREFIX & READY & CHECK & REST).
  pose proof (gateway_dictionary_contains_success_zero backend ge slots called_parameters key_status status changed changed_world suffix value after next
    STRING_KEY POSITIVE REST NONNULL) as ZERO; subst status.
  exists called_parameters, prefix, checking, suffix, called, called_world, changed, changed_world.
  split; [exact EVENTS |]. split; [exact QUIET |]. split; [exact STRING_KEY |]. split; [exact CALLED_PARENT |].
  split; [exact CALLED_KEY |]. split; [exact STREAM |]. split; [exact DEPTH |]. split; [exact INDEX |].
  split; [exact READY |]. split; [exact PREFIX |]. split; assumption.
Qed.
