(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The real root terminator is stored before subsequent source copies. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewaySetupPaths GatewaySetupComposition GatewayFramedRuntime
  GatewayBootstrapSource GatewayBootstrapCopySource GatewayBootstrapCopyState GatewayBootstrapCopyAddress
  GatewayBootstrapPathContext GatewayBootstrapBuffers GatewayBootstrapCapacities GatewayBootstrapRuntime GatewayThreadRuntime.
Import ListNotations.
Open Scope Z_scope.

Theorem actual_bootstrap_terminate_root {World Event} (backend : gateway_backend World Event)
    io native stable discipline thread_errno
    (runtime : gateway_thread_runtime backend io native stable discipline thread_errno)
    (ge : Clight.genv) information resolved filename filename_offset root engine results executable results_literal
    root_bytes api_bytes temporaries memory result :
  let buffers := bootstrap_copy_buffers information resolved root engine results in
  let spans phase := bootstrap_copy_spans phase resolved filename filename_offset root engine results executable
    results_literal root_bytes api_bytes in
  let context phase := gateway_bootstrap_path_context native stable discipline buffers information
    (Vptr filename filename_offset) (spans phase) in
  NoDup (bootstrap_copy_names information resolved filename root engine results executable results_literal) ->
  Genv.find_symbol ge _host_root = Some root ->
  temporaries ! _root_size = Some (Vlong (Int64.repr (Z.of_nat (length root_bytes)))) ->
  ~ In Byte.zero root_bytes ->
  Z.of_nat (length root_bytes) <= 4065 -> Z.of_nat (length api_bytes) <= 4065 ->
  (forall memory, gateway_setup_path backend ge result (context 2%nat)
    (State f_host_bootstrap (bootstrap_copy_after 2) Kstop
      (bootstrap_environment information resolved) temporaries memory)) ->
  gateway_setup_path backend ge result (context 1%nat)
    (State f_host_bootstrap (bootstrap_copy_after 1) Kstop
      (bootstrap_environment information resolved) temporaries memory).
Proof.
  cbn zeta; intros DISTINCT ROOT_SYMBOL ROOT_WORD NONZERO ROOT_SIZE API_SIZE NEXT.
  set (context := fun phase => gateway_bootstrap_path_context native stable discipline
    (bootstrap_copy_buffers information resolved root engine results) information (Vptr filename filename_offset)
    (bootstrap_copy_spans phase resolved filename filename_offset root engine results executable results_literal root_bytes api_bytes)).
  assert (CLOSED : gateway_ambient_closed backend (context 1%nat)).
  { apply gateway_bootstrap_path_context_ambient with (io := io) (thread_errno := thread_errno); exact runtime. }
  assert (CLOSED_NEXT : gateway_ambient_closed backend (context 2%nat)).
  { apply gateway_bootstrap_path_context_ambient with (io := io) (thread_errno := thread_errno); exact runtime. }
  gateway_setup_structure CLOSED.
  eapply gateway_setup_next with
    (next := State f_host_bootstrap Sskip (Kseq (bootstrap_copy_after 2) Kstop)
      (bootstrap_environment information resolved) temporaries memory) (middle := context 2%nat).
  - exact CLOSED.
  - cbn; tauto.
  - intros before world INPUT.
    pose proof (proj1 (proj2 (proj1 INPUT)) root 4096 Writable
      ltac:(cbn [bootstrap_copy_buffers In]; auto 12)) as ROOT.
    pose proof (proj1 ROOT) as PRIVATE.
    destruct ROOT as [_ [_ [_ [_ [_ RANGE]]]]].
    assert (ACCESS : Mem.valid_access before Mint8signed root (Z.of_nat (length root_bytes)) Writable).
    { split.
      - intros position INSIDE; apply RANGE; change (0 <= position < 0 + 4096).
        cbn [size_chunk] in INSIDE; lia.
      - cbn [align_chunk]; apply Z.divide_1_l. }
    destruct (Mem.valid_access_store before Mint8signed root (Z.of_nat (length root_bytes)) (Vint Int.zero) ACCESS)
      as [after STORE].
    exists after; split.
    + eapply actual_bootstrap_root_terminator_edge with (root := root) (amount := Z.of_nat (length root_bytes));
        [reflexivity |exact ROOT_SYMBOL |exact ROOT_WORD |lia |exact STORE].
    + eapply gateway_bootstrap_path_context_terminate;
        [exact runtime |exact INPUT |exact PRIVATE |bootstrap_storage_distinct DISTINCT |
         cbn [bootstrap_copy_spans In]; auto 20 |exact NONZERO |
         change Ptrofs.modulus with 18446744073709551616; lia | | |exact STORE].
      * intros; assumption.
      * apply (bootstrap_copy_retained_outside 1 information resolved filename filename_offset
          root engine results executable results_literal root_bytes api_bytes ltac:(lia) DISTINCT ROOT_SIZE API_SIZE).
  - gateway_setup_structure CLOSED_NEXT; apply NEXT.
Qed.
