(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The final source return frees only its actual two local objects. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBootstrapABI GatewayBootstrapSource
  GatewayBootstrapConstants GatewayBootstrapCopySource GatewayBootstrapCopyState GatewayBootstrapPathContext GatewayBootstrapSpans
  GatewayBootstrapRegions GatewayBootstrapCapacities GatewayBootstrapBuffers GatewayBootstrapEffects
  GatewayBootstrapRetention GatewayBootstrapRuntime GatewayErrorRuntime GatewayThreadRuntime GatewayLocalRuntime
  GatewaySetupPaths GatewayFramedRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_bootstrap_paths {World} native
    (discipline : option val -> mem -> World -> Prop) root engine results root_bytes api_bytes memory world : Prop :=
  discipline None memory world /\ gateway_bootstrap_storage native memory world root engine results /\
  gateway_error_cstring memory (Vptr root Ptrofs.zero) root_bytes /\
  gateway_error_cstring memory (Vptr engine Ptrofs.zero) (root_bytes ++ bootstrap_executable_bytes) /\
  gateway_error_cstring memory (Vptr results Ptrofs.zero) (api_bytes ++ bootstrap_results_bytes).

Theorem bootstrap_capacity_unchanged {World} native before world after object offset amount access :
  @gateway_bootstrap_capacity World native before world object offset amount access ->
  Mem.unchanged_on (fun candidate _ => candidate = object) before after ->
  gateway_bootstrap_capacity native after world object offset amount access.
Proof.
  intros [PRIVATE [POSITIVE [NONNEGATIVE [BOUND [LIVE RANGE]]]]] FRAME.
  assert (PERMISSIONS : Mem.range_perm after object (Ptrofs.unsigned offset)
    (Ptrofs.unsigned offset + amount) Cur access).
  { intros position INSIDE; eapply Mem.perm_unchanged_on;
      [exact FRAME |reflexivity |apply RANGE; exact INSIDE]. }
  split; [exact PRIVATE |]. split; [exact POSITIVE |]. split; [exact NONNEGATIVE |].
  split; [exact BOUND |]. split; [|exact PERMISSIONS].
  eapply Mem.perm_valid_block; apply (PERMISSIONS (Ptrofs.unsigned offset)); lia.
Qed.

Theorem bootstrap_cstring_unchanged before after object offset bytes :
  gateway_error_cstring before (Vptr object offset) bytes ->
  Mem.unchanged_on (fun candidate _ => candidate = object) before after ->
  gateway_error_cstring after (Vptr object offset) bytes.
Proof.
  intros [actual [actual_offset [POINTER [NONZERO [BOUND LOAD]]]]] FRAME.
  inversion POINTER; subst actual actual_offset.
  exists object, offset; split; [reflexivity |]. split; [exact NONZERO |]. split; [exact BOUND |].
  eapply Mem.loadbytes_unchanged_on; [exact FRAME |intros; reflexivity |exact LOAD].
Qed.

Theorem actual_bootstrap_free_blocks (ge : Clight.genv) information resolved :
  sizeof ge gateway_loader_information_type = 32 ->
  blocks_of_env ge (bootstrap_environment information resolved) = [(information, 0, 32); (resolved, 0, 4096)].
Proof.
  intro SIZE.
  change ([(information, 0, sizeof ge gateway_loader_information_type); (resolved, 0, 4096)] =
    [(information, 0, 32); (resolved, 0, 4096)]).
  rewrite SIZE; reflexivity.
Qed.

Theorem bootstrap_free_two_other before middle after information resolved object :
  Mem.free before information 0 32 = Some middle -> Mem.free middle resolved 0 4096 = Some after ->
  object <> information -> object <> resolved ->
  Mem.unchanged_on (fun candidate _ => candidate = object) before after.
Proof.
  intros FIRST LAST INFO RESOLVED.
  eapply Mem.unchanged_on_trans.
  - eapply Mem.free_unchanged_on; [exact FIRST |]. intros position RANGE SAME; apply INFO; symmetry; exact SAME.
  - eapply Mem.free_unchanged_on; [exact LAST |]. intros position RANGE SAME; apply RESOLVED; symmetry; exact SAME.
Qed.

Theorem bootstrap_paths_ambient {World Event} (backend : gateway_backend World Event)
    io native stable discipline thread_errno
    (runtime : gateway_thread_runtime backend io native stable discipline thread_errno)
    root engine results root_bytes api_bytes :
  gateway_ambient_closed backend (gateway_bootstrap_paths native discipline root engine results root_bytes api_bytes).
Proof.
  intros before world after next [SIDE [[ROOT [ENGINE RESULTS]] [ROOT_STRING [ENGINE_STRING RESULTS_STRING]]]] INTERFERENCE.
  destruct (gateway_thread_ambient _ _ _ _ _ _ runtime None before world after next SIDE INTERFERENCE)
    as [NEXT [ACCESS FRAME]].
  split; [exact NEXT |]. split.
  - split; [|split]; eapply gateway_bootstrap_capacity_quiet; eassumption.
  - split; [|split]; eapply gateway_bootstrap_cstring_retained;
      [exact ROOT_STRING |eapply gateway_bootstrap_owned_cstring; [exact (proj1 ROOT) |exact ROOT_STRING] |exact FRAME |
       exact ENGINE_STRING |eapply gateway_bootstrap_owned_cstring; [exact (proj1 ENGINE) |exact ENGINE_STRING] |exact FRAME |
       exact RESULTS_STRING |eapply gateway_bootstrap_owned_cstring; [exact (proj1 RESULTS) |exact RESULTS_STRING] |exact FRAME].
Qed.

Theorem actual_bootstrap_zero_return_edge (ge : Clight.genv) information resolved temporaries before after :
  Mem.free_list before (blocks_of_env ge (bootstrap_environment information resolved)) = Some after ->
  store_edge ge
    (State f_host_bootstrap (bootstrap_copy_after 6) Kstop (bootstrap_environment information resolved) temporaries before)
    (Returnstate (Vint Int.zero) Kstop after).
Proof.
  intro FREE.
  assert (VALUE : expression_value ge (bootstrap_environment information resolved) temporaries before
    (Econst_int Int.zero tint) (Vint Int.zero)) by (apply old_expression_value; constructor).
  split; [exact I |]. split.
  - eapply step_return_1; [exact (proj1 VALUE) |reflexivity |exact FREE].
  - intros trace target REAL; inversion REAL; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    match goal with EVALUATION : eval_expr _ _ _ _ _ ?returned |- _ =>
      pose proof ((proj2 VALUE) returned EVALUATION) as SAME; subst returned end.
    match goal with CAST : sem_cast (Vint Int.zero) _ _ _ = Some ?converted |- _ =>
      change (Some (Vint Int.zero) = Some converted) in CAST; inversion CAST; subst converted end.
    split; [reflexivity |]. f_equal; congruence.
Qed.

Theorem bootstrap_copy_return_scope {World Event} (backend : gateway_backend World Event)
    io native stable discipline thread_errno
    (runtime : gateway_thread_runtime backend io native stable discipline thread_errno)
    (ge : Clight.genv) before world after information resolved filename filename_offset
    root engine results executable results_literal root_bytes api_bytes :
  sizeof ge gateway_loader_information_type = 32 ->
  NoDup (bootstrap_copy_names information resolved filename root engine results executable results_literal) ->
  gateway_bootstrap_path_context native stable discipline
    (bootstrap_copy_buffers information resolved root engine results) information (Vptr filename filename_offset)
    (bootstrap_copy_spans 6 resolved filename filename_offset root engine results executable results_literal
      root_bytes api_bytes) before world ->
  ~ In Byte.zero root_bytes -> ~ In Byte.zero api_bytes ->
  Z.of_nat (length root_bytes) <= 4065 -> Z.of_nat (length api_bytes) <= 4065 ->
  Mem.free_list before (blocks_of_env ge (bootstrap_environment information resolved)) = Some after ->
  gateway_bootstrap_paths native discipline root engine results root_bytes api_bytes after world.
Proof.
  intros SIZE DISTINCT [BUFFERS [INFO SPANS]] ROOT_NONZERO API_NONZERO ROOT_SIZE API_SIZE FREE.
  rewrite (actual_bootstrap_free_blocks ge information resolved SIZE) in FREE.
  cbn [Mem.free_list] in FREE.
  destruct (Mem.free before information 0 32) as [middle |] eqn:FIRST; [|discriminate].
  destruct (Mem.free middle resolved 0 4096) as [last |] eqn:LAST; [|discriminate].
  inversion FREE; subst last.
  destruct BUFFERS as [SIDE [CAPACITIES LITERALS]].
  pose proof (CAPACITIES root 4096 Writable ltac:(cbn [bootstrap_copy_buffers In]; auto 12)) as ROOT.
  pose proof (CAPACITIES engine 4096 Writable ltac:(cbn [bootstrap_copy_buffers In]; auto 12)) as ENGINE.
  pose proof (CAPACITIES results 4096 Writable ltac:(cbn [bootstrap_copy_buffers In]; auto 12)) as RESULTS.
  pose proof (CAPACITIES resolved 4096 Freeable ltac:(cbn [bootstrap_copy_buffers In]; auto 12)) as RESOLVED.
  assert (NEXT : discipline None after world).
  { eapply gateway_thread_native_free; [exact runtime | |exact (proj1 RESOLVED) |exact LAST].
    eapply gateway_thread_native_free; [exact runtime |exact SIDE |exact (proj1 (proj2 INFO)) |exact FIRST]. }
  assert (ROOT_FRAME : Mem.unchanged_on (fun object _ => object = root) before after).
  { eapply bootstrap_free_two_other; [exact FIRST |exact LAST | |]; bootstrap_storage_distinct DISTINCT. }
  assert (ENGINE_FRAME : Mem.unchanged_on (fun object _ => object = engine) before after).
  { eapply bootstrap_free_two_other; [exact FIRST |exact LAST | |]; bootstrap_storage_distinct DISTINCT. }
  assert (RESULTS_FRAME : Mem.unchanged_on (fun object _ => object = results) before after).
  { eapply bootstrap_free_two_other; [exact FIRST |exact LAST | |]; bootstrap_storage_distinct DISTINCT. }
  destruct (bootstrap_completed_copy_strings native stable before world resolved filename filename_offset
    root engine results executable results_literal root_bytes api_bytes SPANS ROOT_NONZERO API_NONZERO ROOT_SIZE API_SIZE)
    as [ROOT_STRING [ENGINE_STRING RESULTS_STRING]].
  split; [exact NEXT |]. split.
  - split; [|split]; eapply bootstrap_capacity_unchanged;
      [exact ROOT |exact ROOT_FRAME |exact ENGINE |exact ENGINE_FRAME |exact RESULTS |exact RESULTS_FRAME].
  - split; [|split]; eapply bootstrap_cstring_unchanged;
      [exact ROOT_STRING |exact ROOT_FRAME |exact ENGINE_STRING |exact ENGINE_FRAME |
       exact RESULTS_STRING |exact RESULTS_FRAME].
Qed.

Theorem actual_bootstrap_copy_return_setup {World Event} (backend : gateway_backend World Event)
    io native stable discipline thread_errno
    (runtime : gateway_thread_runtime backend io native stable discipline thread_errno)
    (ge : Clight.genv) information resolved filename filename_offset
    root engine results executable results_literal root_bytes api_bytes temporaries memory :
  sizeof ge gateway_loader_information_type = 32 ->
  NoDup (bootstrap_copy_names information resolved filename root engine results executable results_literal) ->
  ~ In Byte.zero root_bytes -> ~ In Byte.zero api_bytes ->
  Z.of_nat (length root_bytes) <= 4065 -> Z.of_nat (length api_bytes) <= 4065 ->
  gateway_setup_path backend ge
    (gateway_bootstrap_paths native discipline root engine results root_bytes api_bytes)
    (gateway_bootstrap_path_context native stable discipline
      (bootstrap_copy_buffers information resolved root engine results) information (Vptr filename filename_offset)
      (bootstrap_copy_spans 6 resolved filename filename_offset root engine results executable results_literal root_bytes api_bytes))
    (State f_host_bootstrap (bootstrap_copy_after 6) Kstop
      (bootstrap_environment information resolved) temporaries memory).
Proof.
  intros SIZE DISTINCT ROOT_NONZERO API_NONZERO ROOT_SIZE API_SIZE.
  set (property := gateway_bootstrap_path_context native stable discipline
    (bootstrap_copy_buffers information resolved root engine results) information (Vptr filename filename_offset)
    (bootstrap_copy_spans 6 resolved filename filename_offset root engine results executable results_literal root_bytes api_bytes)).
  eapply gateway_setup_next with (next := Returnstate (Vint Int.zero) Kstop memory)
    (middle := gateway_bootstrap_paths native discipline root engine results root_bytes api_bytes).
  - apply gateway_bootstrap_path_context_ambient with (io := io) (thread_errno := thread_errno); exact runtime.
  - cbn; tauto.
  - intros before world INPUT.
    pose proof (proj1 (proj2 (proj1 INPUT)) information 32 Freeable
      ltac:(cbn [bootstrap_copy_buffers In]; auto 12)) as INFO.
    pose proof (proj1 (proj2 (proj1 INPUT)) resolved 4096 Freeable
      ltac:(cbn [bootstrap_copy_buffers In]; auto 12)) as RESOLVED.
    destruct INFO as [_ [_ [_ [_ [_ INFO_PERMISSIONS]]]]].
    destruct RESOLVED as [_ [_ [_ [_ [_ RESOLVED_PERMISSIONS]]]]].
    destruct (Mem.range_perm_free before information 0 32 INFO_PERMISSIONS) as [middle FIRST].
    assert (KEEP_RESOLVED : Mem.range_perm middle resolved 0 4096 Cur Freeable).
    { intros position INSIDE; eapply Mem.perm_free_1;
        [exact FIRST |left; bootstrap_storage_distinct DISTINCT |apply RESOLVED_PERMISSIONS; exact INSIDE]. }
    destruct (Mem.range_perm_free middle resolved 0 4096 KEEP_RESOLVED) as [after LAST].
    assert (FREE : Mem.free_list before (blocks_of_env ge (bootstrap_environment information resolved)) = Some after).
    { rewrite (actual_bootstrap_free_blocks ge information resolved SIZE).
      cbn [Mem.free_list]; rewrite FIRST, LAST; reflexivity. }
    exists after; split; [apply actual_bootstrap_zero_return_edge; exact FREE |].
    eapply bootstrap_copy_return_scope;
      [exact runtime |exact SIZE |exact DISTINCT |exact INPUT |exact ROOT_NONZERO |exact API_NONZERO |
       exact ROOT_SIZE |exact API_SIZE |exact FREE].
  - apply gateway_setup_return.
    + eapply bootstrap_paths_ambient with (io := io) (thread_errno := thread_errno); exact runtime.
    + intros; assumption.
Qed.
