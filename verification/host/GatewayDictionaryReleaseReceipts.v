(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The original dictionary continuation releases exactly its saved key and child. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayValueEntry GatewayContainerLoopSource GatewayContainerDictionarySource
  GatewayReferenceDictionaryResume GatewaySourcePaths GatewayContexts GatewayFramedRuntime.
Import ListNotations.

Theorem gateway_actual_dictionary_release_key_receipt {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) slots parameters status key key_offset before world events value after next symbol definition :
  gateway_ambient_closed backend property -> parameters ! _first = Some (Vptr key key_offset) ->
  Genv.find_symbol ge _Py_DecRef = Some symbol -> Genv.find_funct_ptr ge symbol = Some definition ->
  type_of_fundef definition = Tfunction [tptr (Tstruct __object noattr)] tvoid cc_default ->
  property before world ->
  gateway_steps backend ge
    (gateway_live (Returnstate (Vint status) (gateway_dictionary_insert_cont slots parameters) before) world) events
    (gateway_live (Returnstate value Kstop after) next) ->
  exists called_parameters prefix releasing suffix called called_world result changed changed_world,
    events = prefix ++ releasing ++ suffix /\
    Forall (fun event => event = gateway_source E0 \/ event = gateway_ambient) prefix /\
    called_parameters ! _result__1 = Some (Vint status) /\
    called_parameters ! _container = parameters ! _container /\ called_parameters ! _first = parameters ! _first /\
    called_parameters ! _value__1 = parameters ! _value__1 /\ called_parameters ! _stream = parameters ! _stream /\
    called_parameters ! _depth = parameters ! _depth /\ called_parameters ! _index__1 = parameters ! _index__1 /\
    property called called_world /\
    gateway_steps backend ge
      (gateway_live (Returnstate (Vint status) (gateway_dictionary_insert_cont slots parameters) before) world) prefix
      (gateway_live (Callstate definition [Vptr key key_offset] (gateway_dictionary_release_key_cont slots called_parameters) called) called_world) /\
    gateway_steps backend ge
      (gateway_live (Callstate definition [Vptr key key_offset] Kstop called) called_world) releasing
      (gateway_live (Returnstate result Kstop changed) changed_world) /\
    gateway_steps backend ge
      (gateway_live (Returnstate result (gateway_dictionary_release_key_cont slots called_parameters) changed) changed_world) suffix
      (gateway_live (Returnstate value Kstop after) next).
Proof.
  intros CLOSED KEY SYMBOL FUNCTION TYPE INPUT RUN.
  destruct (gateway_dictionary_release_key_source_path backend ge property slots parameters status key key_offset before symbol definition
    CLOSED KEY SYMBOL FUNCTION TYPE) as (called_parameters & PATH & STATUS & PARENT & FIRST & CHILD & STREAM & DEPTH & INDEX).
  destruct (gateway_source_path_cut backend ge _ _ _ _ _ _ PATH before world events value after next INPUT RUN)
    as (prefix & rest & called & called_world & EVENTS & QUIET & PREFIX & READY & FROM_CALL).
  destruct (gateway_return_cut backend ge definition [Vptr key key_offset] (gateway_dictionary_release_key_cont slots called_parameters)
    called called_world rest (Returnstate value Kstop after) next ltac:(cbn; exact I) ltac:(cbn; lia) FROM_CALL)
    as (releasing & suffix & result & changed & changed_world & REST_EVENTS & RELEASE & REST).
  exists called_parameters, prefix, releasing, suffix, called, called_world, result, changed, changed_world.
  split; [rewrite EVENTS, REST_EVENTS; reflexivity |]. split; [exact QUIET |]. split; [exact STATUS |].
  split; [exact PARENT |]. split; [exact FIRST |]. split; [exact CHILD |]. split; [exact STREAM |].
  split; [exact DEPTH |]. split; [exact INDEX |]. split; [exact READY |]. split; [exact PREFIX |]. split; assumption.
Qed.

Theorem gateway_actual_dictionary_release_child_receipt {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) slots parameters ignored child child_offset before world events value after next symbol definition :
  gateway_ambient_closed backend property -> parameters ! _value__1 = Some (Vptr child child_offset) ->
  Genv.find_symbol ge _Py_DecRef = Some symbol -> Genv.find_funct_ptr ge symbol = Some definition ->
  type_of_fundef definition = Tfunction [tptr (Tstruct __object noattr)] tvoid cc_default ->
  property before world ->
  gateway_steps backend ge
    (gateway_live (Returnstate ignored (gateway_dictionary_release_key_cont slots parameters) before) world) events
    (gateway_live (Returnstate value Kstop after) next) ->
  exists prefix releasing suffix called called_world result changed changed_world,
    events = prefix ++ releasing ++ suffix /\
    Forall (fun event => event = gateway_source E0 \/ event = gateway_ambient) prefix /\ property called called_world /\
    gateway_steps backend ge
      (gateway_live (Returnstate ignored (gateway_dictionary_release_key_cont slots parameters) before) world) prefix
      (gateway_live (Callstate definition [Vptr child child_offset] (gateway_dictionary_release_child_cont slots parameters) called) called_world) /\
    gateway_steps backend ge
      (gateway_live (Callstate definition [Vptr child child_offset] Kstop called) called_world) releasing
      (gateway_live (Returnstate result Kstop changed) changed_world) /\
    gateway_steps backend ge
      (gateway_live (Returnstate result (gateway_dictionary_release_child_cont slots parameters) changed) changed_world) suffix
      (gateway_live (Returnstate value Kstop after) next).
Proof.
  intros CLOSED CHILD SYMBOL FUNCTION TYPE INPUT RUN.
  pose proof (gateway_dictionary_release_child_source_path backend ge property slots parameters ignored child child_offset before symbol definition
    CLOSED CHILD SYMBOL FUNCTION TYPE) as PATH.
  destruct (gateway_source_path_cut backend ge _ _ _ _ _ _ PATH before world events value after next INPUT RUN)
    as (prefix & rest & called & called_world & EVENTS & QUIET & PREFIX & READY & FROM_CALL).
  destruct (gateway_return_cut backend ge definition [Vptr child child_offset] (gateway_dictionary_release_child_cont slots parameters)
    called called_world rest (Returnstate value Kstop after) next ltac:(cbn; exact I) ltac:(cbn; lia) FROM_CALL)
    as (releasing & suffix & result & changed & changed_world & REST_EVENTS & RELEASE & REST).
  exists prefix, releasing, suffix, called, called_world, result, changed, changed_world.
  split; [rewrite EVENTS, REST_EVENTS; reflexivity |]. split; [exact QUIET |]. split; [exact READY |].
  split; [exact PREFIX |]. split; assumption.
Qed.
