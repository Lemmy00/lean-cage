(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The source copy phase crosses only its actual individual libc effect. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewaySourcePaths GatewaySetupPaths GatewaySetupComposition
  GatewayFramedRuntime GatewayBootstrapABI GatewayBootstrapSource GatewayBootstrapCopySource
  GatewayBootstrapCopyPaths GatewayBootstrapPathContext GatewayBootstrapRuntime GatewayThreadRuntime.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_bootstrap_source_copy_effect {World Event} (backend : gateway_backend World Event)
    io native stable discipline thread_errno module_filename canonicalizes
    (threads : gateway_thread_runtime backend io native stable discipline thread_errno)
    (runtime : gateway_bootstrap_runtime backend io native stable discipline module_filename canonicalizes)
    (ge : Clight.genv) source_state continuation buffers information filename spans retained
    destination destination_offset source source_offset bytes result :
  let property := gateway_bootstrap_path_context native stable discipline buffers information filename spans in
  let written := gateway_bootstrap_path_context native stable discipline buffers information filename
    ((destination, destination_offset, bytes) :: retained) in
  gateway_source_path backend ge (gateway_bootstrap_signature gateway_memory_copy_api)
    [Vptr destination destination_offset; Vptr source source_offset;
     Vlong (Int64.repr (Z.of_nat (length bytes)))] continuation property source_state property ->
  destination <> information -> In (source, source_offset, bytes) spans ->
  gateway_bootstrap_disjoint destination destination_offset (Z.of_nat (length bytes)) source source_offset ->
  Z.of_nat (length bytes) <= Int64.max_unsigned ->
  (forall span, In span retained -> In span spans) ->
  (forall object offset kept, In (object, offset, kept) retained ->
    forall position, Ptrofs.unsigned offset <= position < Ptrofs.unsigned offset + Z.of_nat (length kept) ->
    ~ gateway_native_region destination destination_offset (Z.of_nat (length bytes)) object position) ->
  (forall memory world, property memory world -> native world destination /\
    gateway_native_pointer memory destination destination_offset (Z.of_nat (length bytes)) Writable) ->
  (forall memory, gateway_setup_path backend ge result written
    (Returnstate (Vptr destination destination_offset) continuation memory)) ->
  gateway_setup_path backend ge result property source_state.
Proof.
  cbn zeta; intros PATH INFO SOURCE DISJOINT WIDTH INCLUDED OUTSIDE POINTER NEXT.
  set (property := gateway_bootstrap_path_context native stable discipline buffers information filename spans).
  assert (CLOSED : gateway_ambient_closed backend property).
  { apply gateway_bootstrap_path_context_ambient with (io := io) (thread_errno := thread_errno); exact threads. }
  eapply gateway_setup_after_source; [exact PATH |exact CLOSED |exact CLOSED |].
  intros before; cbn [gateway_bootstrap_signature].
  eapply gateway_setup_external; [exact CLOSED |].
  intros called world returned after next observed INPUT OPERATION.
  destruct (POINTER called world INPUT) as [PRIVATE WRITABLE].
  destruct (gateway_bootstrap_path_context_copy backend io native stable discipline module_filename canonicalizes
    runtime called world after next buffers information filename spans retained destination destination_offset
    source source_offset bytes returned observed INPUT PRIVATE INFO WRITABLE SOURCE DISJOINT WIDTH INCLUDED OUTSIDE
    OPERATION) as [VALUE OUTPUT].
  subst returned; eexists; split; [exact OUTPUT |apply NEXT].
Qed.

Theorem gateway_bootstrap_source_copy_rule {World Event} (backend : gateway_backend World Event)
    io native stable discipline thread_errno module_filename canonicalizes
    (threads : gateway_thread_runtime backend io native stable discipline thread_errno)
    (runtime : gateway_bootstrap_runtime backend io native stable discipline module_filename canonicalizes)
    (ge : Clight.genv) index information resolved temporaries memory buffers filename spans retained
    target origin amount destination destination_offset source source_offset bytes symbol result :
  let property := gateway_bootstrap_path_context native stable discipline buffers information filename spans in
  let written := gateway_bootstrap_path_context native stable discipline buffers information filename
    ((destination, destination_offset, bytes) :: retained) in
  bootstrap_copy_after index = Ssequence (bootstrap_copy target origin amount) (bootstrap_copy_after (S index)) ->
  Genv.find_symbol ge _memcpy = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some (gateway_bootstrap_signature gateway_memory_copy_api) ->
  destination <> information -> In (source, source_offset, bytes) spans ->
  gateway_bootstrap_disjoint destination destination_offset (Z.of_nat (length bytes)) source source_offset ->
  Z.of_nat (length bytes) <= Int64.max_unsigned ->
  (forall span, In span retained -> In span spans) ->
  (forall object offset kept, In (object, offset, kept) retained ->
    forall position, Ptrofs.unsigned offset <= position < Ptrofs.unsigned offset + Z.of_nat (length kept) ->
    ~ gateway_native_region destination destination_offset (Z.of_nat (length bytes)) object position) ->
  (forall memory world, property memory world ->
    native world destination /\
    gateway_native_pointer memory destination destination_offset (Z.of_nat (length bytes)) Writable /\
    expression_value ge (bootstrap_environment information resolved) temporaries memory target
      (Vptr destination destination_offset) /\
    expression_value ge (bootstrap_environment information resolved) temporaries memory origin
      (Vptr source source_offset) /\
    expression_value ge (bootstrap_environment information resolved) temporaries memory amount
      (Vlong (Int64.repr (Z.of_nat (length bytes)))) /\
    sem_cast (Vptr destination destination_offset) (typeof target) (tptr tvoid) memory =
      Some (Vptr destination destination_offset) /\
    sem_cast (Vptr source source_offset) (typeof origin) (tptr tvoid) memory = Some (Vptr source source_offset) /\
    sem_cast (Vlong (Int64.repr (Z.of_nat (length bytes)))) (typeof amount) tulong memory =
      Some (Vlong (Int64.repr (Z.of_nat (length bytes))))) ->
  (forall memory, gateway_setup_path backend ge result written
    (Returnstate (Vptr destination destination_offset)
      (bootstrap_copy_cont index information resolved temporaries) memory)) ->
  gateway_setup_path backend ge result property
    (State f_host_bootstrap (bootstrap_copy_after index) Kstop
      (bootstrap_environment information resolved) temporaries memory).
Proof.
  cbn zeta; intros SHAPE SYMBOL FUNCTION INFO SOURCE DISJOINT WIDTH INCLUDED OUTSIDE OPERANDS NEXT.
  set (property := gateway_bootstrap_path_context native stable discipline buffers information filename spans).
  assert (CLOSED : gateway_ambient_closed backend property).
  { apply gateway_bootstrap_path_context_ambient with (io := io) (thread_errno := thread_errno); exact threads. }
  eapply gateway_setup_after_source.
  - eapply gateway_bootstrap_direct_copy_path;
      [exact CLOSED |exact SHAPE |exact SYMBOL |exact FUNCTION |].
    intros before world INPUT.
    destruct (OPERANDS before world INPUT) as [PRIVATE [POINTER VALUES]]; exact VALUES.
  - exact CLOSED.
  - exact CLOSED.
  - intros before; cbn [gateway_bootstrap_signature].
    eapply gateway_setup_external; [exact CLOSED |].
    intros called world returned after next observed INPUT OPERATION.
    destruct (OPERANDS called world INPUT) as [PRIVATE [POINTER VALUES]].
    destruct (gateway_bootstrap_path_context_copy backend io native stable discipline module_filename canonicalizes
      runtime called world after next buffers information filename spans retained destination destination_offset
      source source_offset bytes returned observed INPUT PRIVATE INFO POINTER SOURCE DISJOINT WIDTH INCLUDED OUTSIDE
      OPERATION) as [VALUE OUTPUT].
    subst returned; eexists; split; [exact OUTPUT |apply NEXT].
Qed.
