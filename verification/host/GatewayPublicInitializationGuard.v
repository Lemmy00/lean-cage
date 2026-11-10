(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Every operational public callback reads the actual completed flag before its original body. *)
From Stdlib Require Import ZArith List Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayMemoryPrefixes GatewayFramedRuntime GatewayUnaryExpressions.
Import ListNotations.

Inductive gateway_public_guard := public_exchange | public_path | public_workspace | public_cli.
Definition public_guard_owner guard := match guard with
  | public_exchange => f_host_exchange | public_path => f_host_as_path
  | public_workspace => f_host_workspace_init | public_cli => f_host_cli end.
Definition public_guard_temporary guard := match guard with
  | public_exchange => _t'105 | public_path => _t'9 | public_workspace => _t'27 | public_cli => _t'24 end.
Definition public_guard_check guard := match fn_body (public_guard_owner guard) with Ssequence first _ => first | _ => Sskip end.
Definition public_guard_after guard := match fn_body (public_guard_owner guard) with Ssequence _ rest => rest | _ => Sskip end.
Definition public_guard_select guard := match public_guard_check guard with Ssequence _ select => select | _ => Sskip end.
Definition public_guard_denied guard := match public_guard_select guard with Sifthenelse _ denied _ => denied | _ => Sskip end.
Definition public_guard_target guard (initialized : bool) environment parameters memory :=
  if initialized then State (public_guard_owner guard) (public_guard_after guard) Kstop environment parameters memory
  else State (public_guard_owner guard) (public_guard_denied guard) (Kseq (public_guard_after guard) Kstop) environment parameters memory.

Theorem actual_public_initialization_guard_shape guard :
  fn_body (public_guard_owner guard) = Ssequence (public_guard_check guard) (public_guard_after guard) /\
  public_guard_check guard = Ssequence
    (Sset (public_guard_temporary guard) (Evar _host_initialized tint)) (public_guard_select guard) /\
  public_guard_select guard = Sifthenelse
    (Eunop Onotbool (Etempvar (public_guard_temporary guard) tint) tint) (public_guard_denied guard) Sskip.
Proof. destruct guard; repeat split; reflexivity. Qed.

Lemma public_guard_allocation_preserves_absent ge environment before variables after_environment after identifier :
  alloc_variables ge environment before variables after_environment after ->
  ~ In identifier (map fst variables) -> after_environment ! identifier = environment ! identifier.
Proof.
  intro ALLOCATED; induction ALLOCATED; intros ABSENT; [reflexivity |].
  rewrite IHALLOCATED; [apply PTree.gso; cbn in ABSENT; intro SAME; apply ABSENT; left; symmetry; exact SAME |].
  cbn in ABSENT; intuition.
Qed.

Theorem actual_public_guard_global_scope ge guard before environment allocated :
  alloc_variables ge empty_env before (fn_vars (public_guard_owner guard)) environment allocated ->
  environment ! _host_initialized = None /\ environment ! _PyErr_SetString = None.
Proof.
  intro ALLOCATED; split; rewrite (public_guard_allocation_preserves_absent _ _ _ _ _ _ _ ALLOCATED);
    [reflexivity |destruct guard; vm_compute; intuition discriminate |
      reflexivity |destruct guard; vm_compute; intuition discriminate].
Qed.

Theorem gateway_public_guard_source_prefix {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) guard (initialized : bool) environment parameters memory complete :
  gateway_ambient_closed backend property -> environment ! _host_initialized = None ->
  Genv.find_symbol ge _host_initialized = Some complete ->
  (forall memory world, property memory world ->
    Mem.load Mint32 memory complete 0 = Some (Vint (if initialized then Int.one else Int.zero))) ->
  gateway_memory_prefix backend ge
    (public_guard_target guard initialized environment
      (PTree.set (public_guard_temporary guard) (Vint (if initialized then Int.one else Int.zero)) parameters) memory)
    property property
    (State (public_guard_owner guard) (fn_body (public_guard_owner guard)) Kstop environment parameters memory).
Proof.
  intros CLOSED GLOBAL SYMBOL LOAD.
  eapply gateway_memory_same with (following := State (public_guard_owner guard) (public_guard_check guard)
    (Kseq (public_guard_after guard) Kstop) environment parameters memory);
    [exact CLOSED |destruct guard; cbn; tauto |intros; rewrite (proj1 (actual_public_initialization_guard_shape guard));
      apply unchanged_store_edge, edge_seq |].
  eapply gateway_memory_same with (following := State (public_guard_owner guard)
    (Sset (public_guard_temporary guard) (Evar _host_initialized tint))
    (Kseq (public_guard_select guard) (Kseq (public_guard_after guard) Kstop)) environment parameters memory);
    [exact CLOSED |destruct guard; cbn; tauto |intros; rewrite (proj1 (proj2 (actual_public_initialization_guard_shape guard)));
      apply unchanged_store_edge, edge_seq |].
  eapply gateway_memory_same with (following := State (public_guard_owner guard) Sskip
    (Kseq (public_guard_select guard) (Kseq (public_guard_after guard) Kstop)) environment
    (PTree.set (public_guard_temporary guard) (Vint (if initialized then Int.one else Int.zero)) parameters) memory).
  - exact CLOSED.
  - destruct guard; cbn; tauto.
  - intros before world GOOD; apply certified_set_edge.
    eapply location_read_value; [apply global_location_value; [exact GLOBAL |exact SYMBOL] |].
    eapply deref_loc_value; [reflexivity |exact (LOAD before world GOOD)].
  - eapply gateway_memory_same with (following := State (public_guard_owner guard) (public_guard_select guard)
      (Kseq (public_guard_after guard) Kstop) environment
      (PTree.set (public_guard_temporary guard) (Vint (if initialized then Int.one else Int.zero)) parameters) memory);
      [exact CLOSED |destruct guard; cbn; tauto |intros; apply unchanged_store_edge, edge_skip_seq |].
    destruct initialized.
    + eapply gateway_memory_same with (following := State (public_guard_owner guard) Sskip
        (Kseq (public_guard_after guard) Kstop) environment
        (PTree.set (public_guard_temporary guard) (Vint Int.one) parameters) memory).
      * exact CLOSED.
      * destruct guard; cbn; tauto.
      * intros; rewrite (proj2 (proj2 (actual_public_initialization_guard_shape guard))).
        eapply certified_if_edge with (v := Vint Int.zero) (b := false).
        -- eapply gateway_unary_expression_value with (value := Vint Int.one);
             [apply old_expression_value, value_temp; apply PTree.gss |reflexivity].
        -- reflexivity.
      * eapply gateway_memory_same with (following := State (public_guard_owner guard) (public_guard_after guard) Kstop environment
          (PTree.set (public_guard_temporary guard) (Vint Int.one) parameters) memory);
          [exact CLOSED |destruct guard; cbn; tauto |intros; apply unchanged_store_edge, edge_skip_seq |apply gateway_memory_identity].
    + eapply gateway_memory_same with (following := State (public_guard_owner guard) (public_guard_denied guard)
        (Kseq (public_guard_after guard) Kstop) environment
        (PTree.set (public_guard_temporary guard) (Vint Int.zero) parameters) memory).
      * exact CLOSED.
      * destruct guard; cbn; tauto.
      * intros; rewrite (proj2 (proj2 (actual_public_initialization_guard_shape guard))).
        eapply certified_if_edge with (v := Vint Int.one) (b := true).
        -- eapply gateway_unary_expression_value with (value := Vint Int.zero);
             [apply old_expression_value, value_temp; apply PTree.gss |reflexivity].
        -- reflexivity.
      * apply gateway_memory_identity.
Qed.
