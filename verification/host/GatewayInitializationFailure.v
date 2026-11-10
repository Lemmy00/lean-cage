(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Failed initialization clears the actual active flag while allowing a pending exception. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayInitializationSource GatewayInitializationEntrySource
  GatewayInitializationRegions GatewayInitializationCells GatewayInitializationStores GatewayInitializationGuarded
  GatewayInitializationCompletionSource GatewayErrorRuntime GatewayAttachedNative GatewayThreadRuntime GatewaySourceSegments GatewayFramedRuntime GatewayReturnScope.
Import ListNotations.

Definition gateway_initialization_failure_context {World} rooted native symbols active complete memory (world : World) :=
  rooted memory world /\ gateway_initialization_cells native symbols active complete memory world.

Section Failed.
Context {World Event} (backend : gateway_backend World Event) native stable rooted
  (runtime : gateway_attached_native_runtime backend native stable rooted)
  (symbols : gateway_initialization_symbols).
Let context active complete := gateway_initialization_failure_context rooted native symbols active complete.

Lemma gateway_initialization_failure_closed active complete : gateway_ambient_closed backend (context active complete).
Proof.
  intros before world after next [ROOTED CELLS] INTERFERENCE.
  destruct (gateway_attached_native_ambient backend native stable rooted runtime before world after next ROOTED INTERFERENCE)
    as [NEXT [ACCESS FRAME]].
  split; [exact NEXT |]. eapply gateway_initialization_cells_quiet; eassumption.
Qed.

Theorem gateway_initialization_failure_script parameters memory complete :
  gateway_source_segment backend (Clight.globalenv prog) (context Int.one complete)
    (Returnstate Vnullptr (initialization_body_cont parameters) memory)
    (Returnstate Vnullptr Kstop memory) (context Int.zero complete).
Proof.
  destruct (gateway_initialization_failed_frontier backend (Clight.globalenv prog) (context Int.one complete)
    parameters memory (gateway_initialization_failure_closed _ _)) as (changed & FRONTIER & RESULT).
  eapply initialization_completion_segment_compose; [exact FRONTIER |].
  eapply gateway_segment_next with
    (next := State f_PyInit__host Sskip (Kseq initialization_return Kstop) empty_env changed memory)
    (middle := context Int.zero complete).
  - apply gateway_initialization_failure_closed.
  - cbn; tauto.
  - intros before world [ROOTED CELLS].
    pose proof (initialization_cells_active_capacity native symbols Int.one complete before world CELLS) as CAPACITY.
    destruct (Mem.valid_access_store before Mint32 (initialization_active symbols) 0 (Vint Int.zero)
      (gateway_initialization_word_access native before world _ CAPACITY)) as [after STORE].
    exists after; split.
    + apply initialization_global_store with (object := initialization_active symbols);
        [exact (initialization_active_symbol symbols) |exact STORE].
    + split.
      * eapply gateway_attached_native_store; [exact runtime |exact ROOTED |exact (proj1 CAPACITY) |exact STORE].
      * exact (gateway_initialization_cells_store native symbols Int.one complete before world false Int.zero after CELLS STORE).
  - apply gateway_initialization_failed_return; [apply gateway_initialization_failure_closed |exact RESULT].
Qed.

Theorem gateway_actual_initialization_failed parameters complete before world events value after next :
  context Int.one complete before world ->
  gateway_steps backend (Clight.globalenv prog)
    (gateway_live (Returnstate Vnullptr (initialization_body_cont parameters) before) world) events
    (gateway_live (Returnstate value Kstop after) next) ->
  value = Vnullptr /\ context Int.zero complete after next.
Proof.
  intros INPUT RUN.
  pose proof (gateway_initialization_failure_script parameters before complete) as SCRIPT.
  destruct (gateway_source_segment_cut backend (Clight.globalenv prog) _ _ _ _ SCRIPT before world events value after next INPUT RUN)
    as (prefix & suffix & memory & owner & EVENTS & QUIET & PREFIX & READY & SUFFIX).
  exact (gateway_terminal_return_scope backend (Clight.globalenv prog) (context Int.zero complete) Vnullptr
    (gateway_initialization_failure_closed _ _) memory owner suffix value after next READY SUFFIX).
Qed.
End Failed.
