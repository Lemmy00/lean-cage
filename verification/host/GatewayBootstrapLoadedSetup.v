(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual loader names cross every real guard before path publication. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewaySetupPaths GatewaySetupComposition
  GatewaySetupResults GatewayFramedRuntime GatewayBootstrapABI GatewayBootstrapRuntime GatewayBootstrapSource
  GatewayBootstrapFilename GatewayBootstrapInformation GatewayBootstrapRegions GatewayBootstrapStorageNames
  GatewayBootstrapCopyState GatewayBootstrapBuffers GatewayBootstrapCheckContext GatewayBootstrapCheckRules
  GatewayBootstrapLengthSource GatewayBootstrapLengthBindings GatewayBootstrapLengthSegments
  GatewayBootstrapLoadedCompare GatewayBootstrapRealpathSource GatewayBootstrapRealpathSetup
  GatewayBootstrapValidationSource GatewayBootstrapValidationChecks GatewayBootstrapConstants GatewayThreadRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_bootstrap_loaded_paths {World} native discipline
    (canonicalizes : World -> World -> list Byte.int -> list Byte.int -> Prop)
    root engine results original memory (world : World) : Prop :=
  30 < Z.of_nat (length original) <= 4095 /\ hd Byte.zero original = Byte.repr 47 /\
  skipn (length original - 30) original = bootstrap_suffix_bytes /\
  gateway_bootstrap_resolved_paths native discipline canonicalizes root engine results original memory world.

Section LoadedSetup.
Context {World Event} (backend : gateway_backend World Event) io native stable discipline thread_errno
    module_filename canonicalizes
    (threads : gateway_thread_runtime backend io native stable discipline thread_errno)
    (runtime : gateway_bootstrap_runtime backend io native stable discipline module_filename canonicalizes).
Variable ge : Clight.genv.
Variables information resolved filename root engine results suffix executable results_literal
    length_symbol comparison_symbol realpath_symbol copy_symbol : block.
Variable filename_offset : ptrofs.
Variable original : list Byte.int.
Hypotheses
  (SIZE : sizeof ge gateway_loader_information_type = 32)
  (LAYOUT : gateway_bootstrap_information_layout ge)
  (STORAGE_DISTINCT : NoDup (information :: resolved ::
    bootstrap_storage_names root engine results suffix executable results_literal))
  (DISTINCT : NoDup (bootstrap_copy_names information resolved filename root engine results executable results_literal))
  (ORIGINAL_NONZERO : ~ In Byte.zero original)
  (ROOT_SYMBOL : Genv.find_symbol ge _host_root = Some root)
  (ENGINE_SYMBOL : Genv.find_symbol ge _host_engine = Some engine)
  (RESULTS_SYMBOL : Genv.find_symbol ge _host_default_results = Some results)
  (SUFFIX_SYMBOL : Genv.find_symbol ge _suffix = Some suffix)
  (EXECUTABLE_SYMBOL : Genv.find_symbol ge _executable = Some executable)
  (RESULTS_LITERAL_SYMBOL : Genv.find_symbol ge _results = Some results_literal)
  (LENGTH_SYMBOL : Genv.find_symbol ge _strnlen = Some length_symbol)
  (LENGTH_FUNCTION : Genv.find_funct_ptr ge length_symbol = Some (gateway_bootstrap_signature gateway_bounded_length_api))
  (COMPARISON_SYMBOL : Genv.find_symbol ge _memcmp = Some comparison_symbol)
  (COMPARISON_FUNCTION : Genv.find_funct_ptr ge comparison_symbol = Some (gateway_bootstrap_signature gateway_memory_compare_api))
  (REALPATH_SYMBOL : Genv.find_symbol ge _realpath = Some realpath_symbol)
  (REALPATH_FUNCTION : Genv.find_funct_ptr ge realpath_symbol = Some (gateway_bootstrap_signature gateway_canonical_path_api))
  (COPY_SYMBOL : Genv.find_symbol ge _memcpy = Some copy_symbol)
  (COPY_FUNCTION : Genv.find_funct_ptr ge copy_symbol = Some (gateway_bootstrap_signature gateway_memory_copy_api)).
Let buffers := (information, 32, Freeable) :: (resolved, 4096, Freeable) ::
  bootstrap_loaded_capacities root engine results suffix executable results_literal.
Let literals := bootstrap_loaded_literals suffix executable results_literal.
Let property := gateway_bootstrap_loaded_context native stable discipline buffers literals
  information (Vptr filename filename_offset) original.
Let result := gateway_bootstrap_loaded_paths native discipline canonicalizes root engine results original.

Local Lemma closed : gateway_ambient_closed backend property.
Proof. eapply gateway_bootstrap_loaded_context_ambient; exact threads. Qed.

Theorem actual_bootstrap_loaded_comparison_setup temporaries memory :
  temporaries ! _size = Some (Vlong (Int64.repr (Z.of_nat (length original)))) ->
  temporaries ! _tail = Some (Vlong (Int64.repr 30)) ->
  30 < Z.of_nat (length original) <= 4095 -> hd Byte.zero original = Byte.repr 47 ->
  gateway_setup_path backend ge result property
    (Callstate (gateway_bootstrap_signature gateway_memory_compare_api)
      [Vptr filename (Ptrofs.add filename_offset (Ptrofs.repr (Z.of_nat (length original) - 30)));
       Vptr suffix Ptrofs.zero; Vlong (Int64.repr 30)]
      (bootstrap_loaded_comparison_cont information resolved (Vptr filename filename_offset) temporaries) memory).
Proof.
  intros WORD TAIL LOADED_SIZE LOADED_SLASH.
  eapply gateway_bootstrap_suffix_setup with (runtime := runtime).
  - exact closed.
  - reflexivity.
  - lia.
  - intros current world [BUFFERS [_ [_ PROTECTED]]].
    split; [exact (proj1 BUFFERS) |]. split; [exact PROTECTED |].
    apply (proj2 (proj2 BUFFERS)); unfold literals, bootstrap_loaded_literals; cbn [In]; auto.
  - intros before world after next observed INPUT [SIDE [ACCESS [FRAME QUIET]]].
    eapply gateway_bootstrap_loaded_quiet; eassumption.
  - intros SUFFIX_MATCH current.
    eapply gateway_setup_after_source.
    + eapply actual_bootstrap_comparison_to_realpath;
        [exact LAYOUT |exact closed |intros before world INPUT; exact (proj2 INPUT) |
         exact REALPATH_SYMBOL |exact REALPATH_FUNCTION |exact WORD |exact TAIL |exact LOADED_SIZE].
    + exact closed.
    + exact closed.
    + intro called_memory; eapply gateway_setup_post with
        (result := gateway_bootstrap_resolved_paths native discipline canonicalizes root engine results original).
      * intros final owner PATHS; split; [exact LOADED_SIZE |].
        split; [exact LOADED_SLASH |]. split; assumption.
      * eapply actual_bootstrap_realpath_setup; eassumption.
Qed.

Theorem actual_bootstrap_loaded_length_setup temporaries memory :
  gateway_setup_path backend ge result property
    (Callstate (gateway_bootstrap_signature gateway_bounded_length_api)
      [Vptr filename filename_offset; Vlong (Int64.repr 4096)]
      (bootstrap_length_cont information resolved temporaries) memory).
Proof.
  eapply gateway_bootstrap_length_setup with (runtime := runtime) (bytes := original).
  - exact closed.
  - intros before world [BUFFERS [_ [STRING PROTECTED]]].
    split; [exact (proj1 BUFFERS) |]. split; assumption.
  - intros before world after next observed INPUT [SIDE [ACCESS [FRAME QUIET]]].
    eapply gateway_bootstrap_loaded_quiet; eassumption.
  - intro returned_memory; eapply gateway_setup_after_segment.
    + apply actual_bootstrap_loaded_length_segment; exact closed.
    + eapply actual_bootstrap_loaded_validation_setup;
        [exact closed |exact LAYOUT |intros before world INPUT; exact (proj2 INPUT) |
         exact COMPARISON_SYMBOL |exact COMPARISON_FUNCTION |exact SUFFIX_SYMBOL |
         unfold bootstrap_loaded_bound_temporaries; rewrite PTree.gso by discriminate; apply PTree.gss |
         unfold bootstrap_loaded_bound_temporaries; apply PTree.gss |].
      intros LOADED_SIZE SLASH current; apply actual_bootstrap_loaded_comparison_setup.
      * unfold bootstrap_loaded_bound_temporaries; rewrite PTree.gso by discriminate; rewrite PTree.gss.
        rewrite Z.min_r by lia; reflexivity.
      * unfold bootstrap_loaded_bound_temporaries; apply PTree.gss.
      * exact LOADED_SIZE.
      * exact SLASH.
Qed.

Theorem actual_bootstrap_nonnull_loader_setup status memory :
  status <> Int.zero ->
  gateway_setup_path backend ge result property
    (Returnstate (Vint status) (bootstrap_loader_cont information resolved) memory).
Proof.
  intro NONZERO; eapply gateway_setup_after_source.
  - eapply actual_bootstrap_loader_to_length;
      [exact LAYOUT |exact closed |intros before world INPUT; exact (proj2 INPUT) |
       exact NONZERO |exact LENGTH_SYMBOL |exact LENGTH_FUNCTION].
  - exact closed.
  - exact closed.
  - intro current; apply actual_bootstrap_loaded_length_setup.
Qed.
End LoadedSetup.
