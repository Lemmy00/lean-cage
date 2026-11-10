(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The same second child reaches an actual successful dictionary insertion. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayValueEntry GatewayContainerLoopSource GatewayContainerDictionarySource
  GatewayReferenceDictionaryResume GatewayDictionaryInsertStatus GatewaySourceIntegerReceipt GatewayObjects GatewayFramedRuntime.
Import ListNotations.

Theorem gateway_actual_dictionary_insert_receipt {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) slots parameters parent parent_offset key key_offset child child_offset
    before world events value after next symbol definition release_symbol release_definition :
  gateway_object_api_definition gateway_api_dict_set = Some definition -> gateway_ambient_closed backend property ->
  (forall memory current returned changed following observed, property memory current ->
    gateway_object_operation backend gateway_api_dict_set [Vptr parent parent_offset; Vptr key key_offset; Vptr child child_offset]
      memory current returned changed following observed -> exists status, returned = Vint status) ->
  parameters ! _container = Some (Vptr parent parent_offset) -> parameters ! _first = Some (Vptr key key_offset) ->
  (forall memory current, property memory current -> Mem.weak_valid_pointer memory child (Ptrofs.unsigned child_offset) = true) ->
  Genv.find_symbol ge _PyDict_SetItem = Some symbol -> Genv.find_funct_ptr ge symbol = Some definition ->
  type_of_fundef definition = Tfunction [tptr (Tstruct __object noattr); tptr (Tstruct __object noattr);
    tptr (Tstruct __object noattr)] tint cc_default ->
  Genv.find_symbol ge _Py_DecRef = Some release_symbol -> Genv.find_funct_ptr ge release_symbol = Some release_definition ->
  type_of_fundef release_definition = Tfunction [tptr (Tstruct __object noattr)] tvoid cc_default ->
  property before world ->
  gateway_steps backend ge
    (gateway_live (Returnstate (Vptr child child_offset) (gateway_dictionary_second_cont slots parameters) before) world) events
    (gateway_live (Returnstate value Kstop after) next) -> value <> Vnullptr ->
  exists called_parameters prefix inserting suffix called called_world changed changed_world,
    events = prefix ++ inserting ++ suffix /\
    Forall (fun event => event = gateway_source E0 \/ event = gateway_ambient) prefix /\
    called_parameters ! _value__1 = Some (Vptr child child_offset) /\
    called_parameters ! _container = parameters ! _container /\ called_parameters ! _first = parameters ! _first /\
    called_parameters ! _stream = parameters ! _stream /\ called_parameters ! _depth = parameters ! _depth /\
    called_parameters ! _index__1 = parameters ! _index__1 /\ property called called_world /\
    gateway_steps backend ge
      (gateway_live (Returnstate (Vptr child child_offset) (gateway_dictionary_second_cont slots parameters) before) world) prefix
      (gateway_live (Callstate definition [Vptr parent parent_offset; Vptr key key_offset; Vptr child child_offset]
        (gateway_dictionary_insert_cont slots called_parameters) called) called_world) /\
    gateway_steps backend ge
      (gateway_live (Callstate definition [Vptr parent parent_offset; Vptr key key_offset; Vptr child child_offset] Kstop called) called_world) inserting
      (gateway_live (Returnstate (Vint Int.zero) Kstop changed) changed_world) /\
    gateway_steps backend ge
      (gateway_live (Returnstate (Vint Int.zero) (gateway_dictionary_insert_cont slots called_parameters) changed) changed_world) suffix
      (gateway_live (Returnstate value Kstop after) next).
Proof.
  intros DEFINITION CLOSED TYPED PARENT KEY POINTER SYMBOL FUNCTION TYPE RELEASE_SYMBOL RELEASE_FUNCTION RELEASE_TYPE INPUT RUN NONNULL.
  destruct (gateway_dictionary_insert_source_path backend ge property slots parameters parent parent_offset key key_offset child child_offset before
    symbol definition CLOSED PARENT KEY POINTER SYMBOL FUNCTION TYPE)
    as (called_parameters & PATH & CHILD & CALLED_PARENT & CALLED_KEY & STREAM & DEPTH & INDEX).
  destruct (gateway_source_integer_receipt backend ge gateway_api_dict_set definition
    [Vptr parent parent_offset; Vptr key key_offset; Vptr child child_offset] (gateway_dictionary_insert_cont slots called_parameters) property property
    (Returnstate (Vptr child child_offset) (gateway_dictionary_second_cont slots parameters) before) before world events value after next
    DEFINITION ltac:(cbn; exact I) ltac:(cbn; lia) PATH CLOSED TYPED INPUT RUN)
    as (prefix & inserting & suffix & called & called_world & changed & changed_world & status & EVENTS & QUIET & PREFIX & READY & INSERT & REST).
  pose proof (gateway_dictionary_successful_insert_zero backend ge slots called_parameters status key key_offset child child_offset changed changed_world
    suffix value after next release_symbol release_definition ltac:(rewrite CALLED_KEY; exact KEY) CHILD
    RELEASE_SYMBOL RELEASE_FUNCTION RELEASE_TYPE REST NONNULL) as ZERO; subst status.
  exists called_parameters, prefix, inserting, suffix, called, called_world, changed, changed_world.
  split; [exact EVENTS |]. split; [exact QUIET |]. split; [exact CHILD |]. split; [exact CALLED_PARENT |].
  split; [exact CALLED_KEY |]. split; [exact STREAM |]. split; [exact DEPTH |]. split; [exact INDEX |].
  split; [exact READY |]. split; [exact PREFIX |]. split; assumption.
Qed.
