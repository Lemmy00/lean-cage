(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Nonzero actual dictionary insertion status releases both children and returns NULL. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayValueEntry GatewayValueGuards GatewayContainerLoopSource
  GatewayContainerDictionarySource GatewayReferenceDictionaryResume GatewaySourceBoundCalls GatewaySourcePaths GatewaySourceCuts
  GatewayContexts GatewayFailurePaths GatewayFramedRuntime.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_dictionary_failed_insert_guard {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    slots parameters status ignored memory :
  parameters ! _result__1 = Some (Vint status) -> status <> Int.zero ->
  gateway_failure_when backend ge (fun _ _ => True)
    (Returnstate ignored (gateway_dictionary_release_child_cont slots parameters) memory).
Proof.
  intros RESULT NONZERO.
  assert (ZERO : Int.eq status Int.zero = false) by (apply Int.eq_false; exact NONZERO).
  pose proof ZERO as ZERO_REPR; change (Int.eq status (Int.repr 0) = false) in ZERO_REPR.
  assert (CLOSED : gateway_ambient_closed backend (fun _ _ => True))
    by (unfold gateway_ambient_closed; intros; exact I).
  gateway_bound_source_failure CLOSED ltac:(fun _ => fail)
    ltac:(fun _ => cbn -[Int.eq]; rewrite ?ZERO, ?ZERO_REPR; reflexivity) gateway_value_pointer_return.
Qed.

Theorem gateway_actual_dictionary_nonzero_insert_failure {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    slots parameters status key key_offset child child_offset before world events value after next symbol definition :
  status <> Int.zero -> parameters ! _first = Some (Vptr key key_offset) ->
  parameters ! _value__1 = Some (Vptr child child_offset) ->
  Genv.find_symbol ge _Py_DecRef = Some symbol -> Genv.find_funct_ptr ge symbol = Some definition ->
  type_of_fundef definition = Tfunction [tptr (Tstruct __object noattr)] tvoid cc_default ->
  gateway_steps backend ge
    (gateway_live (Returnstate (Vint status) (gateway_dictionary_insert_cont slots parameters) before) world) events
    (gateway_live (Returnstate value Kstop after) next) -> value = Vnullptr.
Proof.
  intros NONZERO KEY CHILD SYMBOL FUNCTION TYPE RUN.
  assert (CLOSED : gateway_ambient_closed backend (fun _ _ => True))
    by (unfold gateway_ambient_closed; intros; exact I).
  destruct (gateway_dictionary_release_key_source_path backend ge (fun _ _ => True) slots parameters status key key_offset before
    symbol definition CLOSED KEY SYMBOL FUNCTION TYPE)
    as (called_parameters & PATH & STATUS & PARENT & FIRST & VALUE & STREAM & DEPTH & INDEX).
  destruct (gateway_source_path_cut backend ge _ _ _ _ _ _ PATH before world events value after next I RUN)
    as (prefix & rest & key_before & key_world & EVENTS & QUIET & PREFIX & READY & FROM_KEY).
  destruct (gateway_return_cut backend ge definition [Vptr key key_offset] (gateway_dictionary_release_key_cont slots called_parameters)
    key_before key_world rest (Returnstate value Kstop after) next ltac:(cbn; exact I) ltac:(cbn; lia) FROM_KEY)
    as (key_events & tail & key_result & key_after & key_next & REST_EVENTS & KEY_RUN & AFTER_KEY).
  pose proof (gateway_dictionary_release_child_source_path backend ge (fun _ _ => True) slots called_parameters key_result child child_offset
    key_after symbol definition CLOSED ltac:(rewrite VALUE; exact CHILD) SYMBOL FUNCTION TYPE) as CHILD_PATH.
  destruct (gateway_source_path_cut backend ge _ _ _ _ _ _ CHILD_PATH key_after key_next tail value after next I AFTER_KEY)
    as (child_prefix & child_rest & child_before & child_world & CHILD_EVENTS & CHILD_QUIET & CHILD_PREFIX & CHILD_READY & FROM_CHILD).
  destruct (gateway_return_cut backend ge definition [Vptr child child_offset] (gateway_dictionary_release_child_cont slots called_parameters)
    child_before child_world child_rest (Returnstate value Kstop after) next ltac:(cbn; exact I) ltac:(cbn; lia) FROM_CHILD)
    as (child_events & suffix & child_result & child_after & child_next & CHILD_REST_EVENTS & CHILD_RUN & REST).
  exact (gateway_dictionary_failed_insert_guard backend ge slots called_parameters status child_result child_after STATUS NONZERO
    child_after child_next suffix value after next I REST).
Qed.

Theorem gateway_dictionary_successful_insert_zero {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    slots parameters status key key_offset child child_offset before world events value after next symbol definition :
  parameters ! _first = Some (Vptr key key_offset) -> parameters ! _value__1 = Some (Vptr child child_offset) ->
  Genv.find_symbol ge _Py_DecRef = Some symbol -> Genv.find_funct_ptr ge symbol = Some definition ->
  type_of_fundef definition = Tfunction [tptr (Tstruct __object noattr)] tvoid cc_default ->
  gateway_steps backend ge
    (gateway_live (Returnstate (Vint status) (gateway_dictionary_insert_cont slots parameters) before) world) events
    (gateway_live (Returnstate value Kstop after) next) -> value <> Vnullptr -> status = Int.zero.
Proof.
  intros KEY CHILD SYMBOL FUNCTION TYPE RUN NONNULL; destruct (Int.eq_dec status Int.zero) as [ZERO | NONZERO]; [exact ZERO |].
  exfalso; apply NONNULL; eapply gateway_actual_dictionary_nonzero_insert_failure; eassumption.
Qed.
