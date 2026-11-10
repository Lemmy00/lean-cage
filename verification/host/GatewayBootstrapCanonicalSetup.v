(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Canonical validation, five real copies and actual frees form one source path. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewaySetupPaths GatewaySetupComposition
  GatewaySourceSegments GatewaySetupResults GatewayFramedRuntime GatewayBootstrapABI GatewayBootstrapRuntime
  GatewayBootstrapSource GatewayBootstrapFilename GatewayBootstrapValidationSource GatewayBootstrapCanonicalCompare
  GatewayBootstrapCheckRules GatewayBootstrapValidationChecks GatewayBootstrapCanonicalResult
  GatewayBootstrapCheckContext GatewayBootstrapRegions GatewayBootstrapBuffers GatewayBootstrapPreparation
  GatewayBootstrapCopySource GatewayBootstrapCopyPrefix GatewayBootstrapCopies GatewayBootstrapReturn GatewayBootstrapCopyState
  GatewayBootstrapCopyPaths GatewayBootstrapPathContext GatewayBootstrapInformation
  GatewayBootstrapConstants GatewayBootstrapCompareReturn GatewayThreadRuntime
  GatewayBootstrapLengthSegments GatewayBootstrapCanonicalSource GatewayBootstrapCanonicalLength
  GatewayBootstrapRealpathSource GatewayBootstrapLoadedCompare.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_bootstrap_checked_paths {World} native discipline root engine results original canonical
    memory (world : World) : Prop :=
  30 < Z.of_nat (length canonical) <= 4095 /\ hd Byte.zero canonical = Byte.repr 47 /\
  skipn (length canonical - 30) canonical = bootstrap_suffix_bytes /\
  gateway_bootstrap_paths native discipline root engine results
    (bootstrap_path_prefix canonical) (bootstrap_path_prefix original) memory world.

Section CanonicalSetup.
Context {World Event} (backend : gateway_backend World Event) io native stable discipline thread_errno
    module_filename canonicalizes
    (threads : gateway_thread_runtime backend io native stable discipline thread_errno)
    (runtime : gateway_bootstrap_runtime backend io native stable discipline module_filename canonicalizes).
Variable ge : Clight.genv.
Variables information resolved filename root engine results suffix executable results_literal
    comparison_symbol copy_symbol : block.
Variable filename_offset : ptrofs.
Variables original canonical : list Byte.int.
Hypotheses
  (SIZE : sizeof ge gateway_loader_information_type = 32)
  (LAYOUT : gateway_bootstrap_information_layout ge)
  (DISTINCT : NoDup (bootstrap_copy_names information resolved filename root engine results executable results_literal))
  (ORIGINAL_NONZERO : ~ In Byte.zero original) (CANONICAL_NONZERO : ~ In Byte.zero canonical)
  (LOADED_SIZE : 30 < Z.of_nat (length original) <= 4095)
  (ROOT_SYMBOL : Genv.find_symbol ge _host_root = Some root)
  (ENGINE_SYMBOL : Genv.find_symbol ge _host_engine = Some engine)
  (RESULTS_SYMBOL : Genv.find_symbol ge _host_default_results = Some results)
  (SUFFIX_SYMBOL : Genv.find_symbol ge _suffix = Some suffix)
  (EXECUTABLE_SYMBOL : Genv.find_symbol ge _executable = Some executable)
  (RESULTS_LITERAL_SYMBOL : Genv.find_symbol ge _results = Some results_literal)
  (COMPARISON_SYMBOL : Genv.find_symbol ge _memcmp = Some comparison_symbol)
  (COMPARISON_FUNCTION : Genv.find_funct_ptr ge comparison_symbol = Some (gateway_bootstrap_signature gateway_memory_compare_api))
  (COPY_SYMBOL : Genv.find_symbol ge _memcpy = Some copy_symbol)
  (COPY_FUNCTION : Genv.find_funct_ptr ge copy_symbol = Some (gateway_bootstrap_signature gateway_memory_copy_api)).
Let buffers := (information, 32, Freeable) :: (resolved, 4096, Freeable) ::
  bootstrap_loaded_capacities root engine results suffix executable results_literal.
Let literals := bootstrap_loaded_literals suffix executable results_literal.
Let property := gateway_bootstrap_check_context native stable discipline buffers literals
  information filename filename_offset original resolved canonical.
Let result := gateway_bootstrap_checked_paths native discipline root engine results original canonical.

Local Lemma closed : gateway_ambient_closed backend property.
Proof. eapply gateway_bootstrap_check_context_ambient; exact threads. Qed.

Theorem actual_bootstrap_canonical_comparison_setup temporaries memory :
  temporaries ! _size = Some (Vlong (Int64.repr (Z.of_nat (length canonical)))) ->
  temporaries ! _tail = Some (Vlong (Int64.repr 30)) ->
  temporaries ! _api_size = Some (Vlong (Int64.repr (Z.of_nat (length original) - 30))) ->
  30 < Z.of_nat (length canonical) <= 4095 -> hd Byte.zero canonical = Byte.repr 47 ->
  gateway_setup_path backend ge result property
    (Callstate (gateway_bootstrap_signature gateway_memory_compare_api)
      [Vptr resolved (Ptrofs.add Ptrofs.zero (Ptrofs.repr (Z.of_nat (length canonical) - 30)));
       Vptr suffix Ptrofs.zero; Vlong (Int64.repr 30)]
      (bootstrap_canonical_comparison_cont information resolved temporaries) memory).
Proof.
  intros WORD TAIL API_WORD CANONICAL_SIZE CANONICAL_SLASH.
  eapply gateway_bootstrap_suffix_setup with (runtime := runtime).
  - exact closed.
  - reflexivity.
  - lia.
  - intros current world [BUFFERS [_ [_ [_ [_ PROTECTED]]]]].
    split; [exact (proj1 BUFFERS) |]. split; [exact PROTECTED |].
    apply (proj2 (proj2 BUFFERS)); unfold literals, bootstrap_loaded_literals; cbn [In]; auto.
  - intros before world after next observed INPUT [SIDE [ACCESS [FRAME QUIET]]].
    eapply gateway_bootstrap_check_quiet; eassumption.
  - intros SUFFIX_MATCH current.
    eapply gateway_setup_after_source.
    + eapply actual_bootstrap_guarded_root_copy;
        [exact threads |exact closed |exact COPY_SYMBOL |exact COPY_FUNCTION |exact ROOT_SYMBOL |
         exact WORD |exact TAIL |exact API_WORD |exact CANONICAL_SIZE |exact LOADED_SIZE].
    + exact closed.
    + exact closed.
    + intro copy_memory.
      pose proof (bootstrap_path_prefix_extent canonical CANONICAL_SIZE) as [ROOT_EXTENT ROOT_RANGE].
      pose proof (bootstrap_path_prefix_extent original LOADED_SIZE) as [API_EXTENT API_RANGE].
      rewrite <- ROOT_EXTENT.
      eapply gateway_setup_post with
        (result := gateway_bootstrap_paths native discipline root engine results
          (bootstrap_path_prefix canonical) (bootstrap_path_prefix original)).
      { intros final owner PATHS; split; [exact CANONICAL_SIZE |].
        split; [exact CANONICAL_SLASH |]. split; assumption. }
      eapply gateway_setup_pre.
      * eapply actual_bootstrap_copy_sequence;
          [exact threads |exact runtime |exact SIZE |exact LAYOUT |exact DISTINCT |
           apply bootstrap_path_prefix_no_zero; exact CANONICAL_NONZERO |
           apply bootstrap_path_prefix_no_zero; exact ORIGINAL_NONZERO |
           lia |lia |exact ROOT_SYMBOL |exact ENGINE_SYMBOL |exact RESULTS_SYMBOL |
           exact EXECUTABLE_SYMBOL |exact RESULTS_LITERAL_SYMBOL |exact COPY_SYMBOL |exact COPY_FUNCTION | |].
        -- unfold bootstrap_copy_temporaries; rewrite PTree.gss; rewrite ROOT_EXTENT; reflexivity.
        -- unfold bootstrap_copy_temporaries, bootstrap_compared_temporaries,
             bootstrap_canonical_comparison_temporaries;
             repeat rewrite PTree.gso by discriminate; rewrite API_WORD, API_EXTENT; reflexivity.
      * exact closed.
      * intros before world INPUT; eapply actual_bootstrap_checked_copy_context with (suffix := suffix); exact INPUT.
Qed.
Theorem actual_bootstrap_canonical_validation_copies temporaries memory :
  temporaries ! _size = Some (Vlong (Int64.repr (Z.min 4096 (Z.of_nat (length canonical))))) ->
  temporaries ! _tail = Some (Vlong (Int64.repr 30)) ->
  temporaries ! _api_size = Some (Vlong (Int64.repr (Z.of_nat (length original) - 30))) ->
  gateway_setup_path backend ge result property
    (State f_host_bootstrap bootstrap_canonical_validation
      (Kseq bootstrap_after_canonical_validation Kstop) (bootstrap_environment information resolved) temporaries memory).
Proof.
  intros WORD TAIL API_WORD.
  eapply actual_bootstrap_canonical_validation_setup;
    [exact threads |exact closed |intros before world INPUT; exact (proj2 INPUT) |
     exact COMPARISON_SYMBOL |exact COMPARISON_FUNCTION |exact SUFFIX_SYMBOL |exact WORD |exact TAIL |].
  intros CANONICAL_SIZE SLASH before; apply actual_bootstrap_canonical_comparison_setup; try assumption.
  rewrite Z.min_r in WORD by lia; exact WORD.
Qed.

Theorem actual_bootstrap_canonical_length_copies temporaries memory :
  temporaries ! _tail = Some (Vlong (Int64.repr 30)) ->
  gateway_setup_path backend ge result property
    (Callstate (gateway_bootstrap_signature gateway_bounded_length_api)
      [Vptr resolved Ptrofs.zero; Vlong (Int64.repr 4096)]
      (bootstrap_canonical_length_cont information resolved (Vptr filename filename_offset)
        (Z.of_nat (length original)) temporaries) memory).
Proof.
  intro TAIL.
  eapply gateway_bootstrap_length_setup with (runtime := runtime) (bytes := canonical).
  - exact closed.
  - intros before world [BUFFERS [_ [_ [_ [STRING PROTECTED]]]]].
    split; [exact (proj1 BUFFERS) |]. split; assumption.
  - intros before world after next observed INPUT [SIDE [ACCESS [FRAME QUIET]]].
    eapply gateway_bootstrap_check_quiet; eassumption.
  - intro returned_memory.
    eapply gateway_setup_after_segment.
    + apply actual_bootstrap_canonical_length_segment; exact closed.
    + apply actual_bootstrap_canonical_validation_copies.
      * unfold bootstrap_canonical_sized_temporaries; apply PTree.gss.
      * unfold bootstrap_canonical_sized_temporaries, bootstrap_canonical_return_temporaries,
          bootstrap_realpath_temporaries, bootstrap_compared_temporaries, bootstrap_loaded_comparison_temporaries;
          repeat rewrite PTree.gso by discriminate; exact TAIL.
      * unfold bootstrap_canonical_sized_temporaries, bootstrap_canonical_return_temporaries,
          bootstrap_realpath_temporaries; repeat rewrite PTree.gso by discriminate; apply PTree.gss.
Qed.
End CanonicalSetup.
