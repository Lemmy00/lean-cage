(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Retain the actual initialized loader field through source checks. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewayThreadRuntime GatewayFramedRuntime
  GatewayBootstrapRuntime GatewayBootstrapRetention GatewayErrorRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_bootstrap_information {World} (native : World -> block -> Prop)
    (discipline : option val -> mem -> World -> Prop) information filename memory world : Prop :=
  discipline None memory world /\ native world information /\
    Mem.load Mptr memory information 0 = Some filename.

Theorem gateway_bootstrap_information_retained {World} native stable discipline information filename
    before world after next :
  @gateway_bootstrap_information World native discipline information filename before world ->
  discipline None after next -> gateway_access_retained native stable before world next ->
  gateway_native_frame native stable gateway_native_no_output world before after ->
  gateway_bootstrap_information native discipline information filename after next.
Proof.
  intros [SIDE [PRIVATE LOAD]] NEXT ACCESS FRAME.
  assert (LIVE : Mem.valid_block before information).
  { eapply Mem.valid_access_valid_block, Mem.valid_access_implies;
      [eapply Mem.load_valid_access; exact LOAD |constructor]. }
  split; [exact NEXT |]. split.
  - exact (proj1 ACCESS information LIVE PRIVATE).
  - eapply Mem.load_unchanged_on; [exact FRAME | |exact LOAD].
    intros; split; [left; exact PRIVATE |cbn; tauto].
Qed.

Theorem gateway_bootstrap_information_ambient {World Event} (backend : gateway_backend World Event)
    io native stable discipline thread_errno
    (runtime : gateway_thread_runtime backend io native stable discipline thread_errno) information filename :
  gateway_ambient_closed backend (gateway_bootstrap_information native discipline information filename).
Proof.
  intros before world after next [SIDE [PRIVATE LOAD]] INTERFERENCE.
  destruct (@gateway_thread_ambient World Event backend io native stable discipline thread_errno runtime
    None before world after next SIDE INTERFERENCE) as [NEXT [ACCESS FRAME]].
  assert (LIVE : Mem.valid_block before information).
  { eapply Mem.valid_access_valid_block, Mem.valid_access_implies;
      [eapply Mem.load_valid_access; exact LOAD |constructor]. }
  split; [exact NEXT |]. split.
  - exact (proj1 ACCESS information LIVE PRIVATE).
  - eapply Mem.load_unchanged_on; [exact FRAME | |exact LOAD].
    intros; split; [left; exact PRIVATE |cbn; tauto].
Qed.

Definition gateway_bootstrap_filename_information {World} (native : World -> block -> Prop) stable
    discipline information filename bytes memory world : Prop :=
  gateway_bootstrap_information native discipline information filename memory world /\
    gateway_error_cstring memory filename bytes /\
    gateway_bootstrap_protected native stable memory world filename (bytes ++ [Byte.zero]).

Theorem gateway_bootstrap_filename_information_retained {World} native stable discipline information filename bytes
    before world after next :
  @gateway_bootstrap_filename_information World native stable discipline information filename bytes before world ->
  discipline None after next -> gateway_access_retained native stable before world next ->
  gateway_native_frame native stable gateway_native_no_output world before after ->
  gateway_bootstrap_filename_information native stable discipline information filename bytes after next.
Proof.
  intros [INFO [STRING PROTECTED]] SIDE ACCESS FRAME; split.
  - eapply gateway_bootstrap_information_retained; eassumption.
  - split.
    + eapply gateway_bootstrap_cstring_retained; eassumption.
    + eapply gateway_bootstrap_protected_retained; eassumption.
Qed.

Theorem gateway_bootstrap_filename_information_ambient {World Event} (backend : gateway_backend World Event)
    io native stable discipline thread_errno
    (runtime : gateway_thread_runtime backend io native stable discipline thread_errno) information filename bytes :
  gateway_ambient_closed backend
    (gateway_bootstrap_filename_information native stable discipline information filename bytes).
Proof.
  intros before world after next [INFO [STRING PROTECTED]] INTERFERENCE.
  destruct (@gateway_thread_ambient World Event backend io native stable discipline thread_errno runtime
    None before world after next (proj1 INFO) INTERFERENCE) as [SIDE [ACCESS FRAME]].
  split.
  - eapply gateway_bootstrap_information_ambient; [exact runtime |exact INFO |exact INTERFERENCE].
  - split.
    + eapply gateway_bootstrap_cstring_retained; eassumption.
    + eapply gateway_bootstrap_protected_retained; eassumption.
Qed.
