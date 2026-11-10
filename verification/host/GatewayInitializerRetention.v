(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Retain relocated native initializer regions beside the live heap. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Globalenvs Ctypes Clight.
From HostGateway Require Import GatewayLoaderRegions GatewayThreadRuntime.
Open Scope Z_scope.

Lemma gateway_loaded_region_live ge before variable object :
  gateway_loaded_native_region ge before variable object -> Mem.valid_block before object.
Proof.
  intros [BOUND READABLE BYTES VALUES].
  eapply Mem.perm_valid_block; apply (READABLE 0); lia.
Qed.

Theorem gateway_loaded_region_retained ge before after variable object :
  gateway_loaded_native_region ge before variable object ->
  Mem.unchanged_on (fun candidate _ => candidate = object) before after ->
  gateway_loaded_native_region ge after variable object.
Proof.
  intros REGION FRAME.
  pose proof (gateway_loaded_region_live ge before variable object REGION) as LIVE.
  destruct REGION as [BOUND READABLE BYTES VALUES]; constructor; [exact BOUND | | |].
  - intros position INSIDE; eapply Mem.perm_unchanged_on; [exact FRAME |reflexivity |].
    apply READABLE; exact INSIDE.
  - erewrite Mem.loadbytes_unchanged_on_1; [exact BYTES |exact FRAME |exact LIVE |].
    intros; reflexivity.
  - eapply Genv.load_store_init_data_invariant; [|exact VALUES].
    intros chunk offset; eapply Mem.load_unchanged_on_1;
      [exact FRAME |exact LIVE |intros; reflexivity].
Qed.

Theorem gateway_initializer_view_retained ge identifier variable object before after :
  gateway_native_initializer_view ge identifier variable object before ->
  Mem.unchanged_on (fun candidate _ => candidate = object) before after ->
  gateway_native_initializer_view ge identifier variable object after.
Proof.
  intros [DEFINITION [NONVOLATILE [SYMBOL REGION]]] FRAME.
  split; [exact DEFINITION |]. split; [exact NONVOLATILE |]. split; [exact SYMBOL |].
  eapply gateway_loaded_region_retained; eassumption.
Qed.

Theorem gateway_initializer_native_frame {World} ge identifier variable object before after
    (native : World -> block -> Prop) stable output world :
  gateway_native_initializer_view ge identifier variable object before ->
  native world object -> (forall position, ~ output object position) ->
  gateway_native_frame native stable output world before after ->
  gateway_native_initializer_view ge identifier variable object after.
Proof.
  intros VIEW PRIVATE UNWRITTEN FRAME.
  eapply gateway_initializer_view_retained; [exact VIEW |].
  eapply Mem.unchanged_on_implies; [exact FRAME |].
  intros candidate position SAME; subst candidate; split; [left; exact PRIVATE |apply UNWRITTEN].
Qed.
