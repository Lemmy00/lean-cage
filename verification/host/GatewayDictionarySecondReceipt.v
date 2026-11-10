(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The second dictionary recursion is selected from the same run and is strictly shorter. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayValueEntry GatewayValueReturns GatewayContainerLoopSource
  GatewayContainerDictionarySource GatewayReferenceDictionaryChild GatewaySourcePaths GatewayContexts GatewaySourceCuts GatewayFramedRuntime.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_actual_dictionary_second_receipt {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) slots parameters stream depth status before world events value after next symbol :
  gateway_ambient_closed backend property -> parameters ! _stream = Some stream ->
  parameters ! _depth = Some (Vint depth) -> gateway_object_pointer_value stream ->
  parameters ! _string_key = Some (Vint status) -> 0 < Int.signed status ->
  Genv.find_symbol ge _host_value = Some symbol -> Genv.find_funct_ptr ge symbol = Some (Internal f_host_value) ->
  property before world ->
  gateway_steps backend ge
    (gateway_live (Returnstate (Vint Int.zero) (gateway_dictionary_contains_cont slots parameters) before) world) events
    (gateway_live (Returnstate value Kstop after) next) -> value <> Vnullptr ->
  exists called_parameters prefix reading suffix child_before child_world child child_after child_next,
    events = prefix ++ reading ++ suffix /\
    Forall (fun event => event = gateway_source E0 \/ event = gateway_ambient) prefix /\
    (length reading < length events)%nat /\
    called_parameters ! _duplicate = Some (Vint Int.zero) /\
    called_parameters ! _container = parameters ! _container /\ called_parameters ! _first = parameters ! _first /\
    called_parameters ! _stream = parameters ! _stream /\ called_parameters ! _depth = parameters ! _depth /\
    called_parameters ! _index__1 = parameters ! _index__1 /\ property child_before child_world /\
    gateway_steps backend ge
      (gateway_live (Returnstate (Vint Int.zero) (gateway_dictionary_contains_cont slots parameters) before) world) prefix
      (gateway_live (Callstate (Internal f_host_value) [stream; Vint (Int.sub depth Int.one)]
        (gateway_dictionary_second_cont slots called_parameters) child_before) child_world) /\
    gateway_steps backend ge
      (gateway_live (Callstate (Internal f_host_value) [stream; Vint (Int.sub depth Int.one)] Kstop child_before) child_world) reading
      (gateway_live (Returnstate child Kstop child_after) child_next) /\ child <> Vnullptr /\
    gateway_steps backend ge
      (gateway_live (Returnstate child (gateway_dictionary_second_cont slots called_parameters) child_after) child_next) suffix
      (gateway_live (Returnstate value Kstop after) next).
Proof.
  intros CLOSED STREAM DEPTH POINTER STRING_KEY POSITIVE SYMBOL FUNCTION INPUT RUN NONNULL.
  destruct (gateway_dictionary_second_source_path backend ge property slots parameters stream depth status before symbol
    CLOSED STREAM DEPTH POINTER STRING_KEY POSITIVE SYMBOL FUNCTION)
    as (called_parameters & PATH & DUPLICATE & PARENT & KEY & CALLED_STREAM & CALLED_DEPTH & INDEX).
  destruct (gateway_source_path_cut backend ge _ _ _ _ _ _ PATH before world events value after next INPUT RUN)
    as (prefix & rest & child_before & child_world & EVENTS & QUIET & PREFIX & READY & FROM_CHILD).
  destruct (gateway_return_cut backend ge (Internal f_host_value) [stream; Vint (Int.sub depth Int.one)]
    (gateway_dictionary_second_cont slots called_parameters) child_before child_world rest (Returnstate value Kstop after) next
    ltac:(cbn; exact I) ltac:(cbn; lia) FROM_CHILD)
    as (reading & suffix & child & child_after & child_next & REST_EVENTS & CHILD & REST).
  assert (CHILD_NONNULL : child <> Vnullptr).
  { intro NULL; subst child; apply NONNULL.
    exact (gateway_dictionary_null_second_denied backend ge slots called_parameters child_after child_after child_next suffix value after next I REST). }
  assert (SHORT : (length reading < length events)%nat).
  { assert (POS : (0 < length prefix)%nat).
    { destruct prefix; [inversion PREFIX | cbn; lia]. }
    rewrite EVENTS, REST_EVENTS, !length_app; lia. }
  exists called_parameters, prefix, reading, suffix, child_before, child_world, child, child_after, child_next.
  split; [rewrite EVENTS, REST_EVENTS; reflexivity |]. split; [exact QUIET |]. split; [exact SHORT |].
  split; [exact DUPLICATE |]. split; [exact PARENT |]. split; [exact KEY |]. split; [exact CALLED_STREAM |].
  split; [exact CALLED_DEPTH |]. split; [exact INDEX |]. split; [exact READY |]. split; [exact PREFIX |].
  split; [exact CHILD |]. split; assumption.
Qed.
