(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Real source allocation produces bootstrap capacities without resetting globals. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBootstrapABI GatewayBootstrapSource GatewayBootstrapBuffers
  GatewayBootstrapCapacities GatewayBootstrapRuntime GatewayBootstrapRetention GatewayBootstrapReturn
  GatewayThreadRuntime GatewayBootstrapEffects.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_bootstrap_buffers_allocated {World Event} (backend : gateway_backend World Event)
    io native stable discipline thread_errno
    (runtime : gateway_thread_runtime backend io native stable discipline thread_errno)
    buffers literals before world after fresh amount :
  gateway_bootstrap_buffers native stable discipline buffers literals before world ->
  0 < amount <= Ptrofs.modulus -> Mem.alloc before 0 amount = (after, fresh) ->
  gateway_bootstrap_buffers native stable discipline ((fresh, amount, Freeable) :: buffers) literals after world.
Proof.
  intros [SIDE [CAPACITIES LITERALS]] WIDTH ALLOC.
  assert (FRAME : Mem.unchanged_on (fun _ _ => True) before after)
    by (eapply Mem.alloc_unchanged_on; exact ALLOC).
  assert (PRIVATE : native world fresh).
  { eapply gateway_thread_fresh_native; [exact runtime |exact SIDE |eapply Mem.fresh_block_alloc; exact ALLOC]. }
  split; [eapply gateway_thread_native_alloc; eassumption |]. split.
  - intros object extent access [SAME |MEMBER].
    + inversion SAME; subst object extent access.
      split; [exact PRIVATE |]. split; [lia |]. split; [lia |].
      split; [change (0 + amount <= Ptrofs.modulus); lia |].
      split; [eapply Mem.valid_new_block; exact ALLOC |].
      intros position INSIDE; eapply Mem.perm_alloc_2; [exact ALLOC |exact INSIDE].
    + eapply bootstrap_capacity_unchanged; [apply CAPACITIES; exact MEMBER |].
      eapply Mem.unchanged_on_implies; [exact FRAME |]. intros; exact I.
  - intros object bytes MEMBER; eapply gateway_bootstrap_protected_retained.
    + apply LITERALS; exact MEMBER.
    + split; intros; assumption.
    + eapply Mem.unchanged_on_implies; [exact FRAME |]. intros; exact I.
Qed.

Theorem actual_bootstrap_entry_buffers {World Event} (backend : gateway_backend World Event)
    io native stable discipline thread_errno
    (runtime : gateway_thread_runtime backend io native stable discipline thread_errno)
    (ge : Clight.genv) before world environment temporaries allocated globals literals :
  sizeof ge gateway_loader_information_type = 32 ->
  gateway_bootstrap_buffers native stable discipline globals literals before world ->
  function_entry2 ge f_host_bootstrap [] before environment temporaries allocated ->
  exists information middle resolved,
    environment = bootstrap_environment information resolved /\ temporaries = bootstrap_temporaries /\
    Mem.alloc before 0 32 = (middle, information) /\ Mem.alloc middle 0 4096 = (allocated, resolved) /\
    information <> resolved /\ ~ Mem.valid_block before information /\ ~ Mem.valid_block before resolved /\
    gateway_bootstrap_buffers native stable discipline
      ((information, 32, Freeable) :: (resolved, 4096, Freeable) :: globals) literals allocated world.
Proof.
  intros SIZE INPUT ENTRY.
  destruct (actual_bootstrap_entry_canonical ge before environment temporaries allocated ENTRY)
    as [information [middle [resolved [ENV [TEMPS [INFO RESOLVED]]]]]].
  rewrite SIZE in INFO.
  assert (FRESH_INFO : ~ Mem.valid_block before information) by (eapply Mem.fresh_block_alloc; exact INFO).
  assert (FRESH_RESOLVED : ~ Mem.valid_block middle resolved) by (eapply Mem.fresh_block_alloc; exact RESOLVED).
  assert (INFO_LIVE : Mem.valid_block middle information) by (eapply Mem.valid_new_block; exact INFO).
  pose proof (gateway_bootstrap_buffers_allocated backend io native stable discipline thread_errno runtime
    _ _ before world middle information 32 INPUT
    ltac:(change Ptrofs.modulus with 18446744073709551616; lia) INFO) as AFTER_INFO.
  pose proof (gateway_bootstrap_buffers_allocated backend io native stable discipline thread_errno runtime
    _ _ middle world allocated resolved 4096 AFTER_INFO
    ltac:(change Ptrofs.modulus with 18446744073709551616; lia) RESOLVED) as AFTER_RESOLVED.
  exists information, middle, resolved.
  split; [exact ENV |]. split; [exact TEMPS |]. split; [exact INFO |]. split; [exact RESOLVED |].
  split; [congruence |]. split; [exact FRESH_INFO |]. split.
  - intro LIVE; apply FRESH_RESOLVED; eapply Mem.valid_block_alloc; eassumption.
  - destruct AFTER_RESOLVED as [SIDE [CAPACITIES LITERALS]].
    split; [exact SIDE |]. split; [|exact LITERALS].
    intros object amount access MEMBER; apply CAPACITIES.
    cbn [In] in MEMBER |- *; tauto.
Qed.
