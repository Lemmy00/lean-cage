(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual suffix success and both capacity guards precede the first root copy. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewaySourcePaths GatewaySourceAutomation
  GatewayFramedRuntime GatewayBootstrapABI GatewayBootstrapSource GatewayBootstrapValidationSource
  GatewayBootstrapCopySource GatewayBootstrapCopyEdges GatewayBootstrapCompareReturn
  GatewayBootstrapCanonicalCompare GatewayBootstrapCanonicalResult GatewayBootstrapCanonicalAmbient
  GatewayBootstrapExtent GatewayThreadRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition bootstrap_copy_temporaries size temporaries :=
  PTree.set _root_size (Vlong (Int64.repr (size - 30)))
    (bootstrap_compared_temporaries _t'13 _t'12 Int.zero
      (bootstrap_canonical_comparison_temporaries temporaries)).
Definition bootstrap_first_copy_cont information resolved size temporaries :=
  Kcall None f_host_bootstrap (bootstrap_environment information resolved)
    (bootstrap_copy_temporaries size temporaries) (Kseq (bootstrap_copy_after 1) Kstop).

Theorem actual_bootstrap_guarded_root_copy {World Event} (backend : gateway_backend World Event)
    io native stable discipline thread_errno
    (runtime : gateway_thread_runtime backend io native stable discipline thread_errno)
    (ge : Clight.genv) information resolved (canonical : list Byte.int) root symbol
    loaded_size temporaries memory (property : mem -> World -> Prop) :
  gateway_ambient_closed backend property ->
  Genv.find_symbol ge _memcpy = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some (gateway_bootstrap_signature gateway_memory_copy_api) ->
  Genv.find_symbol ge _host_root = Some root ->
  temporaries ! _size = Some (Vlong (Int64.repr (Z.of_nat (length canonical)))) ->
  temporaries ! _tail = Some (Vlong (Int64.repr 30)) ->
  temporaries ! _api_size = Some (Vlong (Int64.repr (loaded_size - 30))) ->
  30 < Z.of_nat (length canonical) <= 4095 -> 30 < loaded_size <= 4095 ->
  gateway_source_path backend ge (gateway_bootstrap_signature gateway_memory_copy_api)
    [Vptr root Ptrofs.zero; Vptr resolved Ptrofs.zero;
     Vlong (Int64.repr (Z.of_nat (length canonical) - 30))]
    (bootstrap_first_copy_cont information resolved (Z.of_nat (length canonical)) temporaries)
    property
    (Returnstate (Vint Int.zero)
      (bootstrap_canonical_comparison_cont information resolved temporaries) memory)
    property.
Proof.
  intros CLOSED SYMBOL FUNCTION ROOT SIZE TAIL API_SIZE CANONICAL LOADED.
  eapply gateway_bootstrap_comparison_success; [exact CLOSED |].
  repeat gateway_source_structure CLOSED.
  eapply gateway_source_same with (target := State f_host_bootstrap Sskip
    (Kseq bootstrap_after_root_size Kstop) (bootstrap_environment information resolved)
    (bootstrap_copy_temporaries (Z.of_nat (length canonical)) temporaries) memory).
  - exact CLOSED.
  - cbn; tauto.
  - intros; apply certified_set_edge; eapply gateway_bootstrap_subtract_expression.
    + unfold bootstrap_compared_temporaries, bootstrap_canonical_comparison_temporaries;
        repeat rewrite PTree.gso by discriminate; exact SIZE.
    + unfold bootstrap_compared_temporaries, bootstrap_canonical_comparison_temporaries;
        repeat rewrite PTree.gso by discriminate; exact TAIL.
    + lia.
  - repeat gateway_source_structure CLOSED.
    eapply gateway_source_same with (target := State f_host_bootstrap Sskip
      (Kseq bootstrap_after_root_bound Kstop) (bootstrap_environment information resolved)
      (bootstrap_copy_temporaries (Z.of_nat (length canonical)) temporaries) memory).
    + exact CLOSED.
    + cbn; tauto.
    + intros; apply certified_if_edge with (v := Vint Int.zero) (b := false);
        [eapply gateway_bootstrap_extent_expression; [apply PTree.gss |lia |lia |lia] |reflexivity].
    + repeat gateway_source_structure CLOSED.
      eapply gateway_source_same with (target := State f_host_bootstrap Sskip
        (Kseq bootstrap_copy_start Kstop) (bootstrap_environment information resolved)
        (bootstrap_copy_temporaries (Z.of_nat (length canonical)) temporaries) memory).
      * exact CLOSED.
      * cbn; tauto.
      * intros; apply certified_if_edge with (v := Vint Int.zero) (b := false).
        -- eapply gateway_bootstrap_extent_expression with (amount := loaded_size - 30);
             [|lia |lia |lia].
           unfold bootstrap_copy_temporaries, bootstrap_compared_temporaries,
             bootstrap_canonical_comparison_temporaries;
             repeat rewrite PTree.gso by discriminate; exact API_SIZE.
        -- reflexivity.
      * repeat gateway_source_structure CLOSED.
        eapply gateway_source_same with (target := Callstate
          (gateway_bootstrap_signature gateway_memory_copy_api)
          [Vptr root Ptrofs.zero; Vptr resolved Ptrofs.zero;
           Vlong (Int64.repr (Z.of_nat (length canonical) - 30))]
          (bootstrap_first_copy_cont information resolved (Z.of_nat (length canonical)) temporaries) memory).
        -- exact CLOSED.
        -- cbn; tauto.
        -- intros; eapply gateway_bootstrap_copy_call_edge;
             [reflexivity |exact SYMBOL |exact FUNCTION | | | |reflexivity |reflexivity |reflexivity].
           ++ eapply gateway_bootstrap_global_array_reference; [reflexivity |exact ROOT].
           ++ apply gateway_bootstrap_array_reference; reflexivity.
           ++ apply old_expression_value, value_temp, PTree.gss.
        -- constructor; intros; assumption.
Qed.
