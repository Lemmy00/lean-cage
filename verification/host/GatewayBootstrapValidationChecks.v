(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The real guards split all length/name failures from the suffix call. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewaySetupPaths GatewaySetupComposition
  GatewaySourceSegments GatewayFramedRuntime GatewayBootstrapSource GatewayBootstrapInformation
  GatewayBootstrapFilename GatewayBootstrapGeometry GatewayBootstrapValidationSource
  GatewayBootstrapLoadedCompare GatewayBootstrapCanonicalCompare GatewayBootstrapRejection
  GatewayBootstrapValidationFailures GatewayBootstrapCanonicalResult GatewayBootstrapCopySource
  GatewayIntegerFailures GatewayBootstrapABI GatewayThreadRuntime.
Import ListNotations.
Open Scope Z_scope.

Lemma bootstrap_rejected_setup {World Event} (backend : gateway_backend World Event)
    (ge : Clight.genv) result property information resolved temporaries memory continuation :
  call_cont continuation = Kstop ->
  gateway_setup_path backend ge result property
    (State f_host_bootstrap bootstrap_path_reject continuation
      (bootstrap_environment information resolved) temporaries memory).
Proof.
  intro STOP; apply gateway_setup_failure; left.
  split; [reflexivity |]. split; [exact STOP |left; reflexivity].
Qed.

Theorem actual_bootstrap_loaded_validation_setup {World Event} (backend : gateway_backend World Event)
    (ge : Clight.genv) native stable discipline property result
    information resolved object offset bytes suffix symbol temporaries memory :
  gateway_ambient_closed backend property -> gateway_bootstrap_information_layout ge ->
  (forall memory world, property memory world ->
    gateway_bootstrap_filename_information native stable discipline information (Vptr object offset) bytes memory world) ->
  Genv.find_symbol ge _memcmp = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some (gateway_bootstrap_signature gateway_memory_compare_api) ->
  Genv.find_symbol ge _suffix = Some suffix ->
  temporaries ! _size = Some (Vlong (Int64.repr (Z.min 4096 (Z.of_nat (length bytes))))) ->
  temporaries ! _tail = Some (Vlong (Int64.repr 30)) ->
  (30 < Z.of_nat (length bytes) <= 4095 -> hd Byte.zero bytes = Byte.repr 47 ->
    forall memory,
    gateway_setup_path backend ge result property
      (Callstate (gateway_bootstrap_signature gateway_memory_compare_api)
        [Vptr object (Ptrofs.add offset (Ptrofs.repr (Z.of_nat (length bytes) - 30)));
         Vptr suffix Ptrofs.zero; Vlong (Int64.repr 30)]
        (bootstrap_loaded_comparison_cont information resolved (Vptr object offset) temporaries) memory)) ->
  gateway_setup_path backend ge result property
    (State f_host_bootstrap bootstrap_loaded_validation
      (Kseq bootstrap_after_loaded_validation Kstop) (bootstrap_environment information resolved) temporaries memory).
Proof.
  intros CLOSED LAYOUT INFORMATION SYMBOL FUNCTION SUFFIX SIZE TAIL CONTINUE.
  destruct (Int64.cmpu Cgt (Int64.repr (Z.min 4096 (Z.of_nat (length bytes)))) (Int64.repr 4095)) eqn:BOUNDED.
  - destruct (actual_bootstrap_oversize_segment backend ge false property information resolved temporaries memory _
      CLOSED SIZE BOUNDED) as [changed SEGMENT].
    eapply gateway_setup_after_segment; [exact SEGMENT |apply bootstrap_rejected_setup; reflexivity].
  - destruct (gateway_bootstrap_length_guard (Z.of_nat (length bytes)) ltac:(lia) BOUNDED) as [BOUND MINIMUM].
    rewrite MINIMUM in SIZE, BOUNDED.
    destruct (Int64.cmpu Cle (Int64.repr (Z.of_nat (length bytes))) (Int64.repr 30)) eqn:LONG.
    + destruct (actual_bootstrap_short_name_segment backend ge false property information resolved temporaries memory _
        CLOSED SIZE TAIL BOUNDED LONG) as [changed SEGMENT].
      eapply gateway_setup_after_segment; [exact SEGMENT |apply bootstrap_rejected_setup; reflexivity].
    + assert (LENGTH : 30 < Z.of_nat (length bytes) <= 4095).
      { split; [eapply gateway_bootstrap_tail_guard; [lia |exact LONG] |exact BOUND]. }
      destruct (Byte.eq_dec (hd Byte.zero bytes) (Byte.repr 47)) as [SLASH |RELATIVE].
      * eapply gateway_setup_after_source.
        -- eapply actual_bootstrap_loaded_compare; eassumption.
        -- exact CLOSED.
        -- exact CLOSED.
        -- apply CONTINUE; assumption.
      * destruct (actual_bootstrap_relative_loaded_segment backend ge property information resolved temporaries memory
          _ object offset bytes CLOSED LAYOUT ltac:(
            intros current world GOOD; destruct (INFORMATION _ _ GOOD) as [[_ [_ FIELD]] [STRING _]];
            split; assumption) SIZE TAIL BOUNDED LONG RELATIVE) as [changed SEGMENT].
        eapply gateway_setup_after_segment; [exact SEGMENT |apply bootstrap_rejected_setup; reflexivity].
Qed.

Theorem actual_bootstrap_canonical_validation_setup {World Event} (backend : gateway_backend World Event)
    (ge : Clight.genv) io native stable discipline thread_errno
    (threads : gateway_thread_runtime backend io native stable discipline thread_errno) property result
    information resolved object offset original canonical suffix symbol temporaries memory :
  gateway_ambient_closed backend property ->
  (forall memory world, property memory world ->
    gateway_bootstrap_canonical_information native stable discipline
      information object offset original resolved canonical memory world) ->
  Genv.find_symbol ge _memcmp = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some (gateway_bootstrap_signature gateway_memory_compare_api) ->
  Genv.find_symbol ge _suffix = Some suffix ->
  temporaries ! _size = Some (Vlong (Int64.repr (Z.min 4096 (Z.of_nat (length canonical))))) ->
  temporaries ! _tail = Some (Vlong (Int64.repr 30)) ->
  (30 < Z.of_nat (length canonical) <= 4095 -> hd Byte.zero canonical = Byte.repr 47 ->
    forall memory,
    gateway_setup_path backend ge result property
      (Callstate (gateway_bootstrap_signature gateway_memory_compare_api)
        [Vptr resolved (Ptrofs.add Ptrofs.zero (Ptrofs.repr (Z.of_nat (length canonical) - 30)));
         Vptr suffix Ptrofs.zero; Vlong (Int64.repr 30)]
        (bootstrap_canonical_comparison_cont information resolved temporaries) memory)) ->
  gateway_setup_path backend ge result property
    (State f_host_bootstrap bootstrap_canonical_validation
      (Kseq bootstrap_after_canonical_validation Kstop) (bootstrap_environment information resolved) temporaries memory).
Proof.
  intros CLOSED INFORMATION SYMBOL FUNCTION SUFFIX SIZE TAIL CONTINUE.
  destruct (Int64.cmpu Cgt (Int64.repr (Z.min 4096 (Z.of_nat (length canonical)))) (Int64.repr 4095)) eqn:BOUNDED.
  - destruct (actual_bootstrap_oversize_segment backend ge true property information resolved temporaries memory _
      CLOSED SIZE BOUNDED) as [changed SEGMENT].
    eapply gateway_setup_after_segment; [exact SEGMENT |apply bootstrap_rejected_setup; reflexivity].
  - destruct (gateway_bootstrap_length_guard (Z.of_nat (length canonical)) ltac:(lia) BOUNDED) as [BOUND MINIMUM].
    rewrite MINIMUM in SIZE, BOUNDED.
    destruct (Int64.cmpu Cle (Int64.repr (Z.of_nat (length canonical))) (Int64.repr 30)) eqn:LONG.
    + destruct (actual_bootstrap_short_name_segment backend ge true property information resolved temporaries memory _
        CLOSED SIZE TAIL BOUNDED LONG) as [changed SEGMENT].
      eapply gateway_setup_after_segment; [exact SEGMENT |apply bootstrap_rejected_setup; reflexivity].
    + assert (LENGTH : 30 < Z.of_nat (length canonical) <= 4095).
      { split; [eapply gateway_bootstrap_tail_guard; [lia |exact LONG] |exact BOUND]. }
      destruct (Byte.eq_dec (hd Byte.zero canonical) (Byte.repr 47)) as [SLASH |RELATIVE].
      * eapply gateway_setup_after_source.
        -- eapply actual_bootstrap_canonical_compare; eassumption.
        -- exact CLOSED.
        -- exact CLOSED.
        -- apply CONTINUE; assumption.
      * destruct (actual_bootstrap_relative_canonical_segment backend ge property information resolved temporaries memory
          _ canonical CLOSED ltac:(
            intros current world GOOD; exact (proj1 (proj2 (proj2 (proj2 (INFORMATION _ _ GOOD))))))
          SIZE TAIL BOUNDED LONG RELATIVE) as [changed SEGMENT].
        eapply gateway_setup_after_segment; [exact SEGMENT |apply bootstrap_rejected_setup; reflexivity].
Qed.
