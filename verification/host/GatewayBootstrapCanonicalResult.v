(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: One realpath observation supplies canonical bytes while retaining its actual inputs. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewayRuntime GatewayBootstrapABI GatewayBootstrapRuntime
  GatewayBootstrapInformation GatewayBootstrapMemory GatewayBootstrapEffects GatewayBootstrapRealpathSource
  GatewayThreadRuntime GatewayErrorRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_bootstrap_canonical_information {World} native stable discipline
    information object offset original resolved canonical memory world : Prop :=
  @gateway_bootstrap_filename_information World native stable discipline information
    (Vptr object offset) original memory world /\
  native world resolved /\ gateway_native_pointer memory resolved Ptrofs.zero 4096 Writable /\
  gateway_error_cstring memory (Vptr resolved Ptrofs.zero) canonical /\
  gateway_bootstrap_protected native stable memory world
    (Vptr resolved Ptrofs.zero) (canonical ++ [Byte.zero]).

Theorem gateway_actual_bootstrap_canonical_result {World Event} (backend : gateway_backend World Event)
    io native stable discipline module_filename canonicalizes
    (runtime : gateway_bootstrap_runtime backend io native stable discipline module_filename canonicalizes)
    ge before world information object offset original resolved continuation returned after next observed :
  gateway_bootstrap_filename_information native stable discipline information (Vptr object offset) original before world ->
  native world resolved -> gateway_native_pointer before resolved Ptrofs.zero 4096 Writable ->
  information <> resolved -> object <> resolved ->
  gateway_step backend ge
    (gateway_live (Callstate (gateway_bootstrap_signature gateway_canonical_path_api)
      [Vptr object offset; Vptr resolved Ptrofs.zero] continuation before) world)
    (gateway_primitive observed)
    (gateway_live (Returnstate returned continuation after) next) ->
  gateway_bootstrap_filename_information native stable discipline information (Vptr object offset) original after next /\
  (returned = Vnullptr \/ exists canonical,
    returned = Vptr resolved Ptrofs.zero /\ Z.of_nat (length canonical) <= 4095 /\
    canonicalizes world next original canonical /\
    gateway_bootstrap_canonical_information native stable discipline
      information object offset original resolved canonical after next).
Proof.
  intros [INFO [STRING PROTECTED]] PRIVATE WRITABLE INFO_SEPARATE SOURCE_SEPARATE STEP.
  assert (OPERATION : gateway_bootstrap_operation backend gateway_canonical_path_api
    [Vptr object offset; Vptr resolved Ptrofs.zero] before world returned after next observed).
  { inversion STEP; subst;
      cbn [gateway_bootstrap_operation gateway_bootstrap_signature gateway_runtime_operation]; eassumption. }
  assert (SEPARATE : gateway_bootstrap_separate_source (Vptr object offset) resolved).
  { intros source source_offset SAME; inversion SAME; subst; exact SOURCE_SEPARATE. }
  destruct (@gateway_canonical_path_operation World Event backend io native stable discipline module_filename canonicalizes
    runtime before world (Vptr object offset) original resolved returned after next observed
    (proj1 INFO) STRING PROTECTED PRIVATE WRITABLE SEPARATE OPERATION)
    as [[SIDE [ACCESS [FRAME QUIET]]] [PERMISSIONS RESULT]].
  assert (NEW_INFO : gateway_bootstrap_information native discipline information (Vptr object offset) after next).
  { destruct INFO as [OLD_SIDE [OLD_PRIVATE LOAD]].
    assert (LIVE : Mem.valid_block before information).
    { eapply Mem.valid_access_valid_block, Mem.valid_access_implies;
        [eapply Mem.load_valid_access; exact LOAD |constructor]. }
    split; [exact SIDE |]. split; [exact (proj1 ACCESS information LIVE OLD_PRIVATE) |].
    eapply Mem.load_unchanged_on; [exact FRAME | |exact LOAD].
    intros position RANGE; split; [left; exact OLD_PRIVATE |].
    intros [SAME _]; apply INFO_SEPARATE; exact SAME. }
  assert (NEW_PROTECTED : gateway_bootstrap_protected native stable after next
    (Vptr object offset) (original ++ [Byte.zero])).
  { eapply gateway_bootstrap_protected_effect;
      [exact PROTECTED |exact ACCESS |exact FRAME |].
    intros position RANGE [SAME _]; apply SOURCE_SEPARATE; exact SAME. }
  assert (NEW_STRING : gateway_error_cstring after (Vptr object offset) original).
  { eapply gateway_bootstrap_cstring_from_bytes.
    - destruct STRING as [actual [actual_offset [POINTER [NONZERO _]]]]; exact NONZERO.
    - destruct NEW_PROTECTED as [actual [actual_offset [POINTER [BYTES OWNED]]]].
      inversion POINTER; subst actual actual_offset; exact BYTES. }
  assert (NEW_INPUT : gateway_bootstrap_filename_information native stable discipline
    information (Vptr object offset) original after next) by (exact (conj NEW_INFO (conj NEW_STRING NEW_PROTECTED))).
  split; [exact NEW_INPUT |].
  destruct RESULT as [NULL |[canonical [VALUE [BOUND [CANONICAL LINK]]]]]; [left; exact NULL |right].
  assert (NEW_PRIVATE : native next resolved) by
    (exact (proj1 ACCESS resolved (proj1 (proj2 (proj2 WRITABLE))) PRIVATE)).
  assert (NEW_WRITABLE : gateway_native_pointer after resolved Ptrofs.zero 4096 Writable).
  { destruct WRITABLE as [NONNEGATIVE [BOUNDARY [LIVE RANGE]]].
    split; [exact NONNEGATIVE |]. split; [exact BOUNDARY |]. split.
    - eapply Mem.perm_valid_block; apply (proj1 (PERMISSIONS 0 Cur Writable ltac:(change (0 <= 0 < 0 + 4096); lia))).
      apply RANGE; change (0 <= 0 < 0 + 4096); lia.
    - intros position INSIDE; apply (proj1 (PERMISSIONS position Cur Writable INSIDE)); apply RANGE; exact INSIDE. }
  exists canonical; split; [exact VALUE |]. split; [exact BOUND |]. split; [exact LINK |].
  split; [exact NEW_INPUT |]. split; [exact NEW_PRIVATE |]. split; [exact NEW_WRITABLE |].
  rewrite VALUE in CANONICAL; split; [exact CANONICAL |].
  eapply gateway_bootstrap_owned_cstring; eassumption.
Qed.
