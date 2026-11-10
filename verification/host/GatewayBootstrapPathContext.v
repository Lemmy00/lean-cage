(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Source path checks retain exact loader fields and tracked copy spans. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewayBootstrapABI GatewayBootstrapRuntime
  GatewayBootstrapBuffers GatewayBootstrapSpans GatewayBootstrapInformation GatewayThreadRuntime GatewayFramedRuntime
  GatewayBootstrapTerminator GatewayBootstrapEffects.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_bootstrap_path_context {World} native stable discipline buffers information filename spans
    memory (world : World) : Prop :=
  gateway_bootstrap_buffers native stable discipline buffers [] memory world /\
  gateway_bootstrap_information native discipline information filename memory world /\
  gateway_bootstrap_spans native stable spans memory world.

Theorem gateway_bootstrap_information_effect {World} native stable discipline information filename
    before world after next output :
  @gateway_bootstrap_information World native discipline information filename before world ->
  discipline None after next -> gateway_access_retained native stable before world next ->
  gateway_native_frame native stable output world before after ->
  (forall position, ~ output information position) ->
  gateway_bootstrap_information native discipline information filename after next.
Proof.
  intros [SIDE [PRIVATE LOAD]] NEXT ACCESS FRAME OUTSIDE.
  assert (LIVE : Mem.valid_block before information).
  { eapply Mem.valid_access_valid_block, Mem.valid_access_implies;
      [eapply Mem.load_valid_access; exact LOAD |constructor]. }
  split; [exact NEXT |]. split; [exact (proj1 ACCESS information LIVE PRIVATE) |].
  eapply Mem.load_unchanged_on; [exact FRAME | |exact LOAD].
  intros position RANGE; split; [left; exact PRIVATE |apply OUTSIDE].
Qed.

Theorem gateway_bootstrap_path_context_quiet {World} native stable discipline buffers information filename spans
    before world after next :
  @gateway_bootstrap_path_context World native stable discipline buffers information filename spans before world ->
  discipline None after next -> gateway_access_retained native stable before world next ->
  gateway_native_frame native stable gateway_native_no_output world before after ->
  gateway_bootstrap_path_context native stable discipline buffers information filename spans after next.
Proof.
  intros [BUFFERS [INFO SPANS]] NEXT ACCESS FRAME.
  split; [eapply gateway_bootstrap_buffers_quiet; eassumption |].
  split; [eapply gateway_bootstrap_information_retained; eassumption |].
  eapply gateway_bootstrap_spans_effect; [exact SPANS | |exact ACCESS |exact FRAME |].
  - intros; assumption.
  - intros; unfold gateway_native_no_output; tauto.
Qed.

Theorem gateway_bootstrap_path_context_ambient {World Event} (backend : gateway_backend World Event)
    io native stable discipline thread_errno
    (runtime : gateway_thread_runtime backend io native stable discipline thread_errno)
    buffers information filename spans :
  gateway_ambient_closed backend
    (gateway_bootstrap_path_context native stable discipline buffers information filename spans).
Proof.
  intros before world after next INPUT INTERFERENCE.
  destruct (gateway_thread_ambient _ _ _ _ _ _ runtime None before world after next
    (proj1 (proj1 INPUT)) INTERFERENCE) as [SIDE [ACCESS FRAME]].
  eapply gateway_bootstrap_path_context_quiet; eassumption.
Qed.

Theorem gateway_bootstrap_path_context_copy {World Event} (backend : gateway_backend World Event)
    io native stable discipline module_filename canonicalizes
    (runtime : gateway_bootstrap_runtime backend io native stable discipline module_filename canonicalizes)
    before world after next buffers information filename spans retained
    destination destination_offset source source_offset bytes returned observed :
  gateway_bootstrap_path_context native stable discipline buffers information filename spans before world ->
  native world destination -> destination <> information ->
  gateway_native_pointer before destination destination_offset (Z.of_nat (length bytes)) Writable ->
  In (source, source_offset, bytes) spans ->
  gateway_bootstrap_disjoint destination destination_offset (Z.of_nat (length bytes)) source source_offset ->
  Z.of_nat (length bytes) <= Int64.max_unsigned ->
  (forall span, In span retained -> In span spans) ->
  (forall object offset kept, In (object, offset, kept) retained ->
    forall position, Ptrofs.unsigned offset <= position < Ptrofs.unsigned offset + Z.of_nat (length kept) ->
    ~ gateway_native_region destination destination_offset (Z.of_nat (length bytes)) object position) ->
  gateway_bootstrap_operation backend gateway_memory_copy_api
    [Vptr destination destination_offset; Vptr source source_offset;
     Vlong (Int64.repr (Z.of_nat (length bytes)))] before world returned after next observed ->
  returned = Vptr destination destination_offset /\
  gateway_bootstrap_path_context native stable discipline buffers information filename
    ((destination, destination_offset, bytes) :: retained) after next.
Proof.
  intros [BUFFERS [INFO SPANS]] PRIVATE SEPARATE POINTER SOURCE DISJOINT WIDTH INCLUDED OUTSIDE OPERATION.
  destruct (gateway_bootstrap_spans_copy backend io native stable discipline module_filename canonicalizes runtime
    before world after next spans retained destination destination_offset source source_offset bytes returned observed
    (proj1 BUFFERS) PRIVATE POINTER SPANS SOURCE DISJOINT WIDTH INCLUDED OUTSIDE OPERATION)
    as [POST [PERMISSIONS [RETURNED WRITTEN]]].
  destruct POST as [SIDE [ACCESS [FRAME QUIET]]].
  split; [exact RETURNED |]. split.
  - eapply gateway_bootstrap_buffers_effect;
      [exact BUFFERS |exact SIDE |exact ACCESS |exact FRAME |exact PERMISSIONS |].
    intros object kept MEMBER; contradiction.
  - split; [|exact WRITTEN].
    eapply gateway_bootstrap_information_effect;
      [exact INFO |exact SIDE |exact ACCESS |exact FRAME |].
    intros position [SAME WRITE]; apply SEPARATE; symmetry; exact SAME.
Qed.

Theorem gateway_bootstrap_path_context_terminate {World Event} (backend : gateway_backend World Event)
    io native stable discipline thread_errno
    (runtime : gateway_thread_runtime backend io native stable discipline thread_errno)
    before world after buffers information filename spans retained destination prefix :
  gateway_bootstrap_path_context native stable discipline buffers information filename spans before world ->
  native world destination -> destination <> information ->
  In (destination, Ptrofs.zero, prefix) spans -> ~ In Byte.zero prefix ->
  Z.of_nat (length prefix) + 1 <= Ptrofs.modulus ->
  (forall span, In span retained -> In span spans) ->
  (forall object offset kept, In (object, offset, kept) retained ->
    forall position, Ptrofs.unsigned offset <= position < Ptrofs.unsigned offset + Z.of_nat (length kept) ->
    ~ gateway_native_region destination (Ptrofs.repr (Z.of_nat (length prefix))) 1 object position) ->
  Mem.store Mint8signed before destination (Z.of_nat (length prefix)) (Vint Int.zero) = Some after ->
  gateway_bootstrap_path_context native stable discipline buffers information filename
    ((destination, Ptrofs.zero, prefix ++ [Byte.zero]) :: retained) after world.
Proof.
  intros [BUFFERS [INFO SPANS]] PRIVATE SEPARATE PREFIX NONZERO BOUND INCLUDED OUTSIDE STORE.
  assert (SHIFT : Ptrofs.unsigned (Ptrofs.repr (Z.of_nat (length prefix))) = Z.of_nat (length prefix)).
  { apply Ptrofs.unsigned_repr; unfold Ptrofs.max_unsigned; lia. }
  assert (FRAME : gateway_native_frame native stable
    (gateway_native_region destination (Ptrofs.repr (Z.of_nat (length prefix))) 1) world before after).
  { eapply Mem.store_unchanged_on; [exact STORE |].
    intros position WRITE [OWNED UNWRITTEN].
    apply UNWRITTEN; split; [reflexivity |]. cbn [size_chunk] in WRITE; rewrite SHIFT; exact WRITE. }
  assert (PERMISSIONS : gateway_native_permissions before after destination
    (Ptrofs.repr (Z.of_nat (length prefix))) 1).
  { intros position kind access RANGE; split; intro PERMISSION.
    - eapply Mem.perm_store_1; eassumption.
    - eapply Mem.perm_store_2; eassumption. }
  assert (ACCESS : gateway_access_retained native stable before world world).
  { split; intros; assumption. }
  assert (SIDE : discipline None after world).
  { eapply gateway_thread_native_store; [exact runtime |exact (proj1 BUFFERS) |exact PRIVATE |exact STORE]. }
  split.
  - eapply gateway_bootstrap_buffers_effect;
      [exact BUFFERS |exact SIDE |exact ACCESS |exact FRAME |exact PERMISSIONS |].
    intros object kept MEMBER; contradiction.
  - split.
    + eapply gateway_bootstrap_information_effect;
        [exact INFO |exact SIDE |exact ACCESS |exact FRAME |].
      intros position [SAME WRITE]; apply SEPARATE; symmetry; exact SAME.
    + intros object offset kept [SAME |MEMBER].
      * inversion SAME; subst object offset kept.
        eapply gateway_bootstrap_owned_cstring; [exact PRIVATE |].
        eapply gateway_bootstrap_stored_terminator with (before := before).
        -- destruct (SPANS _ _ _ PREFIX) as [actual [actual_offset [LOCATION [BYTES OWNED]]]].
           inversion LOCATION; subst actual actual_offset; exact BYTES.
        -- exact NONZERO.
        -- change (0 + Z.of_nat (length prefix) + 1 <= Ptrofs.modulus); exact BOUND.
        -- change (Mem.store Mint8signed before destination
             (0 + Z.of_nat (length prefix)) (Vint Int.zero) = Some after); exact STORE.
      * eapply gateway_bootstrap_spans_effect;
          [exact SPANS |exact INCLUDED |exact ACCESS |exact FRAME |exact OUTSIDE |exact MEMBER].
Qed.

Theorem gateway_bootstrap_path_context_prepend {World} native stable discipline buffers information filename spans
    memory world object offset bytes :
  @gateway_bootstrap_path_context World native stable discipline buffers information filename spans memory world ->
  gateway_bootstrap_protected native stable memory world (Vptr object offset) bytes ->
  gateway_bootstrap_path_context native stable discipline buffers information filename
    ((object, offset, bytes) :: spans) memory world.
Proof.
  intros [BUFFERS [INFO SPANS]] ADDED.
  split; [exact BUFFERS |]. split; [exact INFO |].
  intros actual actual_offset contents [SAME |MEMBER].
  - inversion SAME; subst actual actual_offset contents; exact ADDED.
  - apply SPANS; exact MEMBER.
Qed.
