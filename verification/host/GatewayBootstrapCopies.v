(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Compose the real five copies, root store and final local return. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewaySetupPaths GatewaySetupComposition GatewaySourcePaths
  GatewayFramedRuntime GatewayBootstrapABI GatewayBootstrapSource GatewayBootstrapConstants GatewayBootstrapFilename
  GatewayBootstrapCopySource GatewayBootstrapCopyPaths GatewayBootstrapCopyState GatewayBootstrapCopyRule
  GatewayBootstrapAppendPaths GatewayBootstrapResultsPath GatewayBootstrapTerminatorSource GatewayBootstrapReturn
  GatewayBootstrapPathContext GatewayBootstrapBuffers GatewayBootstrapCapacities GatewayBootstrapInformation
  GatewayBootstrapRuntime GatewayThreadRuntime.
Import ListNotations.
Open Scope Z_scope.

Section BootstrapCopies.
Context {World Event} (backend : gateway_backend World Event) io native stable discipline thread_errno
    module_filename canonicalizes
    (threads : gateway_thread_runtime backend io native stable discipline thread_errno)
    (runtime : gateway_bootstrap_runtime backend io native stable discipline module_filename canonicalizes).
Variable ge : Clight.genv.
Variables information resolved filename root engine results executable results_literal symbol : block.
Variable filename_offset : ptrofs.
Variables root_bytes api_bytes : list Byte.int.
Hypotheses
  (SIZE : sizeof ge gateway_loader_information_type = 32)
  (LAYOUT : gateway_bootstrap_information_layout ge)
  (DISTINCT : NoDup (bootstrap_copy_names information resolved filename root engine results executable results_literal))
  (ROOT_NONZERO : ~ In Byte.zero root_bytes) (API_NONZERO : ~ In Byte.zero api_bytes)
  (ROOT_SIZE : Z.of_nat (length root_bytes) <= 4065) (API_SIZE : Z.of_nat (length api_bytes) <= 4065)
  (ROOT_SYMBOL : Genv.find_symbol ge _host_root = Some root)
  (ENGINE_SYMBOL : Genv.find_symbol ge _host_engine = Some engine)
  (RESULTS_SYMBOL : Genv.find_symbol ge _host_default_results = Some results)
  (EXECUTABLE_SYMBOL : Genv.find_symbol ge _executable = Some executable)
  (RESULTS_LITERAL_SYMBOL : Genv.find_symbol ge _results = Some results_literal)
  (COPY_SYMBOL : Genv.find_symbol ge _memcpy = Some symbol)
  (COPY_FUNCTION : Genv.find_funct_ptr ge symbol = Some (gateway_bootstrap_signature gateway_memory_copy_api)).
Let buffers := bootstrap_copy_buffers information resolved root engine results.
Let spans phase := bootstrap_copy_spans phase resolved filename filename_offset root engine results executable
  results_literal root_bytes api_bytes.
Let context phase := gateway_bootstrap_path_context native stable discipline buffers information
  (Vptr filename filename_offset) (spans phase).
Let result := gateway_bootstrap_paths native discipline root engine results root_bytes api_bytes.

Local Lemma closed phase : gateway_ambient_closed backend (context phase).
Proof. eapply gateway_bootstrap_path_context_ambient; exact threads. Qed.

Local Lemma outside phase : (phase < 6)%nat ->
  forall object offset kept, In (object, offset, kept) (spans phase) ->
  forall position, Ptrofs.unsigned offset <= position < Ptrofs.unsigned offset + Z.of_nat (length kept) ->
  ~ gateway_native_region (bootstrap_copy_destination phase root engine results)
      (bootstrap_copy_offset phase root_bytes api_bytes) (bootstrap_copy_amount phase root_bytes api_bytes) object position.
Proof. intro PHASE; eapply bootstrap_copy_retained_outside; eassumption. Qed.

Local Lemma destination_pointer phase : (phase < 6)%nat ->
  forall memory world, context phase memory world ->
  native world (bootstrap_copy_destination phase root engine results) /\
  gateway_native_pointer memory (bootstrap_copy_destination phase root engine results)
    (bootstrap_copy_offset phase root_bytes api_bytes) (bootstrap_copy_amount phase root_bytes api_bytes) Writable.
Proof.
  intro PHASE; destruct phase as [|[|[|[|[|[|phase]]]]]]; try lia;
    intros memory world INPUT; cbn [bootstrap_copy_destination bootstrap_copy_offset bootstrap_copy_amount].
  all: match goal with |- native ?current_world ?object /\ _ =>
    pose proof (proj1 (proj2 (proj1 INPUT)) object 4096 Writable
      ltac:(cbn [buffers bootstrap_copy_buffers In]; auto 12)) as OWNED;
    split; [exact (proj1 OWNED) |] end.
  all: lazymatch goal with
  | |- gateway_native_pointer _ _ Ptrofs.zero _ _ =>
    eapply gateway_bootstrap_capacity_span with (amount := 4096) (low := 0)
  | |- gateway_native_pointer _ _ (Ptrofs.repr ?span_start) _ _ =>
    eapply gateway_bootstrap_capacity_span with (amount := 4096) (low := span_start)
  end;
    [exact OWNED |lia |lia |lia |change Ptrofs.modulus with 18446744073709551616; lia].
Qed.

Local Lemma remaining_copies temporaries memory :
  temporaries ! _root_size = Some (Vlong (Int64.repr (Z.of_nat (length root_bytes)))) ->
  temporaries ! _api_size = Some (Vlong (Int64.repr (Z.of_nat (length api_bytes)))) ->
  gateway_setup_path backend ge result (context 2%nat)
    (State f_host_bootstrap (bootstrap_copy_after 2) Kstop
      (bootstrap_environment information resolved) temporaries memory).
Proof.
  intros ROOT_WORD API_WORD.
  eapply gateway_bootstrap_source_copy_effect with (threads := threads) (runtime := runtime)
    (destination := engine) (destination_offset := Ptrofs.zero)
    (source := root) (source_offset := Ptrofs.zero) (bytes := root_bytes) (retained := spans 2%nat).
  - eapply actual_bootstrap_engine_prefix_path;
      [exact (closed 2%nat) |exact ENGINE_SYMBOL |exact ROOT_SYMBOL |exact COPY_SYMBOL |exact COPY_FUNCTION |exact ROOT_WORD].
  - bootstrap_storage_distinct DISTINCT.
  - cbn [spans bootstrap_copy_spans In]; auto 20.
  - left; bootstrap_storage_distinct DISTINCT.
  - change Int64.max_unsigned with 18446744073709551615; lia.
  - intros; assumption.
  - exact (outside 2%nat ltac:(lia)).
  - exact (destination_pointer 2%nat ltac:(lia)).
  - intro copied_memory.
    do 2 gateway_setup_structure (closed 3%nat).
    eapply gateway_bootstrap_source_copy_effect with (threads := threads) (runtime := runtime)
      (destination := engine) (destination_offset := Ptrofs.repr (Z.of_nat (length root_bytes)))
      (source := executable) (source_offset := Ptrofs.zero)
      (bytes := bootstrap_executable_bytes ++ [Byte.zero]) (retained := spans 3%nat).
    + eapply actual_bootstrap_append_source_path with (engine := true);
        [exact (closed 3%nat) |exact ENGINE_SYMBOL |exact EXECUTABLE_SYMBOL |exact COPY_SYMBOL |exact COPY_FUNCTION |
         exact ROOT_WORD |change Int64.max_unsigned with 18446744073709551615; lia].
    + bootstrap_storage_distinct DISTINCT.
    + cbn [spans bootstrap_copy_spans In]; auto 20.
    + left; bootstrap_storage_distinct DISTINCT.
    + vm_compute; discriminate.
    + intros; assumption.
    + exact (outside 3%nat ltac:(lia)).
    + exact (destination_pointer 3%nat ltac:(lia)).
    + intro appended_memory.
      do 2 gateway_setup_structure (closed 4%nat).
      eapply gateway_bootstrap_source_copy_effect with (threads := threads) (runtime := runtime)
        (destination := results) (destination_offset := Ptrofs.zero)
        (source := filename) (source_offset := filename_offset) (bytes := api_bytes) (retained := spans 4%nat).
      * eapply actual_bootstrap_results_prefix_path;
          [exact (closed 4%nat) |exact LAYOUT |exact RESULTS_SYMBOL |exact COPY_SYMBOL |exact COPY_FUNCTION |exact API_WORD |].
        intros before world INPUT; exact (proj2 (proj2 (proj1 (proj2 INPUT)))).
      * bootstrap_storage_distinct DISTINCT.
      * cbn [spans bootstrap_copy_spans In]; auto 20.
      * left; bootstrap_storage_distinct DISTINCT.
      * change Int64.max_unsigned with 18446744073709551615; lia.
      * intros; assumption.
      * exact (outside 4%nat ltac:(lia)).
      * exact (destination_pointer 4%nat ltac:(lia)).
      * intro results_memory.
        do 2 gateway_setup_structure (closed 5%nat).
        eapply gateway_bootstrap_source_copy_effect with (threads := threads) (runtime := runtime)
          (destination := results) (destination_offset := Ptrofs.repr (Z.of_nat (length api_bytes)))
          (source := results_literal) (source_offset := Ptrofs.zero)
          (bytes := bootstrap_results_bytes ++ [Byte.zero]) (retained := spans 5%nat).
        -- eapply actual_bootstrap_append_source_path with (engine := false);
             [exact (closed 5%nat) |exact RESULTS_SYMBOL |exact RESULTS_LITERAL_SYMBOL |exact COPY_SYMBOL |exact COPY_FUNCTION |
              |change Int64.max_unsigned with 18446744073709551615; lia].
           change ((PTree.set _t'14 (Vptr filename filename_offset) temporaries) ! _api_size =
             Some (Vlong (Int64.repr (Z.of_nat (length api_bytes))))).
           rewrite PTree.gso by discriminate; exact API_WORD.
        -- bootstrap_storage_distinct DISTINCT.
        -- cbn [spans bootstrap_copy_spans In]; auto 20.
        -- left; bootstrap_storage_distinct DISTINCT.
        -- vm_compute; discriminate.
        -- intros; assumption.
        -- exact (outside 5%nat ltac:(lia)).
        -- exact (destination_pointer 5%nat ltac:(lia)).
        -- intro completed_memory.
           do 2 gateway_setup_structure (closed 6%nat).
           eapply actual_bootstrap_copy_return_setup;
             [exact threads |exact SIZE |exact DISTINCT |exact ROOT_NONZERO |exact API_NONZERO |exact ROOT_SIZE |exact API_SIZE].
Qed.

Theorem actual_bootstrap_copy_sequence temporaries memory :
  temporaries ! _root_size = Some (Vlong (Int64.repr (Z.of_nat (length root_bytes)))) ->
  temporaries ! _api_size = Some (Vlong (Int64.repr (Z.of_nat (length api_bytes)))) ->
  gateway_setup_path backend ge result (context 0%nat)
    (Callstate (gateway_bootstrap_signature gateway_memory_copy_api)
      [Vptr root Ptrofs.zero; Vptr resolved Ptrofs.zero; Vlong (Int64.repr (Z.of_nat (length root_bytes)))]
      (bootstrap_copy_cont 0 information resolved temporaries) memory).
Proof.
  intros ROOT_WORD API_WORD.
  eapply gateway_bootstrap_source_copy_effect with (threads := threads) (runtime := runtime)
    (destination := root) (destination_offset := Ptrofs.zero)
    (source := resolved) (source_offset := Ptrofs.zero) (bytes := root_bytes) (retained := spans 0%nat).
  - constructor; intros; assumption.
  - bootstrap_storage_distinct DISTINCT.
  - cbn [spans bootstrap_copy_spans In]; auto 20.
  - left; bootstrap_storage_distinct DISTINCT.
  - change Int64.max_unsigned with 18446744073709551615; lia.
  - intros; assumption.
  - exact (outside 0%nat ltac:(lia)).
  - exact (destination_pointer 0%nat ltac:(lia)).
  - intro copied_memory.
    do 2 gateway_setup_structure (closed 1%nat).
    eapply actual_bootstrap_terminate_root;
      [exact threads |exact DISTINCT |exact ROOT_SYMBOL |exact ROOT_WORD |exact ROOT_NONZERO |exact ROOT_SIZE |exact API_SIZE |].
    intro terminated_memory; apply remaining_copies; assumption.
Qed.
Theorem actual_bootstrap_copy_return temporaries before world events after next :
  temporaries ! _root_size = Some (Vlong (Int64.repr (Z.of_nat (length root_bytes)))) ->
  temporaries ! _api_size = Some (Vlong (Int64.repr (Z.of_nat (length api_bytes)))) ->
  context 0%nat before world ->
  gateway_steps backend ge
    (gateway_live (Callstate (gateway_bootstrap_signature gateway_memory_copy_api)
      [Vptr root Ptrofs.zero; Vptr resolved Ptrofs.zero; Vlong (Int64.repr (Z.of_nat (length root_bytes)))]
      (bootstrap_copy_cont 0 information resolved temporaries) before) world)
    events (gateway_live (Returnstate (Vint Int.zero) Kstop after) next) ->
  result after next.
Proof.
  intros ROOT_WORD API_WORD INPUT RUN.
  eapply gateway_setup_return_exact with
    (source := Callstate (gateway_bootstrap_signature gateway_memory_copy_api)
      [Vptr root Ptrofs.zero; Vptr resolved Ptrofs.zero; Vlong (Int64.repr (Z.of_nat (length root_bytes)))]
      (bootstrap_copy_cont 0 information resolved temporaries) before);
    [exact INPUT |apply actual_bootstrap_copy_sequence; [exact ROOT_WORD |exact API_WORD] |exact RUN].
Qed.
End BootstrapCopies.
