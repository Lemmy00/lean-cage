(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual path checks retain capacities, literals and both observed names together. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewayBootstrapBuffers GatewayBootstrapRuntime
  GatewayBootstrapInformation GatewayBootstrapCanonicalResult GatewayBootstrapCanonicalAmbient
  GatewayBootstrapPrimitiveResults GatewayThreadRuntime GatewayFramedRuntime GatewayErrorRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_bootstrap_loaded_context {World} native stable discipline buffers literals information filename bytes
    memory (world : World) : Prop :=
  gateway_bootstrap_buffers native stable discipline buffers literals memory world /\
  gateway_bootstrap_filename_information native stable discipline information filename bytes memory world.
Definition gateway_bootstrap_check_context {World} native stable discipline buffers literals
    information object offset original resolved canonical memory (world : World) : Prop :=
  gateway_bootstrap_buffers native stable discipline buffers literals memory world /\
  gateway_bootstrap_canonical_information native stable discipline
    information object offset original resolved canonical memory world.

Theorem gateway_bootstrap_loaded_quiet {World} native stable discipline buffers literals information filename bytes
    before world after next :
  @gateway_bootstrap_loaded_context World native stable discipline buffers literals information filename bytes before world ->
  discipline None after next -> gateway_access_retained native stable before world next ->
  gateway_native_frame native stable gateway_native_no_output world before after ->
  gateway_bootstrap_loaded_context native stable discipline buffers literals information filename bytes after next.
Proof.
  intros [BUFFERS INFO] SIDE ACCESS FRAME; split.
  - eapply gateway_bootstrap_buffers_quiet; eassumption.
  - eapply gateway_bootstrap_filename_information_retained; eassumption.
Qed.

Theorem gateway_bootstrap_check_quiet {World} native stable discipline buffers literals
    information object offset original resolved canonical before world after next :
  @gateway_bootstrap_check_context World native stable discipline buffers literals
    information object offset original resolved canonical before world ->
  discipline None after next -> gateway_access_retained native stable before world next ->
  gateway_native_frame native stable gateway_native_no_output world before after ->
  gateway_bootstrap_check_context native stable discipline buffers literals
    information object offset original resolved canonical after next.
Proof.
  intros [BUFFERS INFO] SIDE ACCESS FRAME; split.
  - eapply gateway_bootstrap_buffers_quiet; eassumption.
  - eapply gateway_bootstrap_canonical_retained; eassumption.
Qed.

Theorem gateway_bootstrap_loaded_context_ambient {World Event} (backend : gateway_backend World Event)
    io native stable discipline thread_errno
    (runtime : gateway_thread_runtime backend io native stable discipline thread_errno)
    buffers literals information filename bytes :
  gateway_ambient_closed backend
    (gateway_bootstrap_loaded_context native stable discipline buffers literals information filename bytes).
Proof.
  intros before world after next INPUT INTERFERENCE.
  destruct (gateway_thread_ambient _ _ _ _ _ _ runtime None before world after next
    (proj1 (proj1 INPUT)) INTERFERENCE) as [SIDE [ACCESS FRAME]].
  eapply gateway_bootstrap_loaded_quiet; eassumption.
Qed.

Theorem gateway_bootstrap_check_context_ambient {World Event} (backend : gateway_backend World Event)
    io native stable discipline thread_errno
    (runtime : gateway_thread_runtime backend io native stable discipline thread_errno)
    buffers literals information object offset original resolved canonical :
  gateway_ambient_closed backend
    (gateway_bootstrap_check_context native stable discipline buffers literals
      information object offset original resolved canonical).
Proof.
  intros before world after next INPUT INTERFERENCE.
  destruct (gateway_thread_ambient _ _ _ _ _ _ runtime None before world after next
    (proj1 (proj1 INPUT)) INTERFERENCE) as [SIDE [ACCESS FRAME]].
  eapply gateway_bootstrap_check_quiet; eassumption.
Qed.
