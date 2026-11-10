(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: One realpath call supplies the checked canonical source, including failure. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewaySetupPaths GatewaySetupComposition GatewaySetupResults
  GatewayFramedRuntime GatewayBootstrapABI GatewayBootstrapRuntime GatewayBootstrapPrimitiveResults
  GatewayBootstrapSource GatewayBootstrapFilename GatewayBootstrapInformation GatewayBootstrapRegions
  GatewayBootstrapStorageNames GatewayBootstrapBuffers GatewayBootstrapCapacities GatewayBootstrapCopyState
  GatewayBootstrapCheckContext GatewayBootstrapCanonicalResult GatewayBootstrapCanonicalSource
  GatewayBootstrapCanonicalSetup GatewayBootstrapRealpathSource GatewayBootstrapCanonicalLength
  GatewayBootstrapRejection GatewayBootstrapValidationChecks GatewayBootstrapPreparation GatewayBootstrapReturn
  GatewayThreadRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_bootstrap_resolved_paths {World} native discipline
    (canonicalizes : World -> World -> list Byte.int -> list Byte.int -> Prop)
    root engine results original memory (world : World) : Prop :=
  exists canonical before resolved,
    canonicalizes before resolved original canonical /\
    gateway_bootstrap_checked_paths native discipline root engine results original canonical memory world.

Section RealpathSetup.
Context {World Event} (backend : gateway_backend World Event) io native stable discipline thread_errno
    module_filename canonicalizes
    (threads : gateway_thread_runtime backend io native stable discipline thread_errno)
    (runtime : gateway_bootstrap_runtime backend io native stable discipline module_filename canonicalizes).
Variable ge : Clight.genv.
Variables information resolved filename root engine results suffix executable results_literal
    length_symbol comparison_symbol copy_symbol : block.
Variable filename_offset : ptrofs.
Variable original : list Byte.int.
Hypotheses
  (SIZE : sizeof ge gateway_loader_information_type = 32)
  (LAYOUT : gateway_bootstrap_information_layout ge)
  (STORAGE_DISTINCT : NoDup (information :: resolved ::
    bootstrap_storage_names root engine results suffix executable results_literal))
  (DISTINCT : NoDup (bootstrap_copy_names information resolved filename root engine results executable results_literal))
  (ORIGINAL_NONZERO : ~ In Byte.zero original)
  (LOADED_SIZE : 30 < Z.of_nat (length original) <= 4095)
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
  (COPY_SYMBOL : Genv.find_symbol ge _memcpy = Some copy_symbol)
  (COPY_FUNCTION : Genv.find_funct_ptr ge copy_symbol = Some (gateway_bootstrap_signature gateway_memory_copy_api)).
Let buffers := (information, 32, Freeable) :: (resolved, 4096, Freeable) ::
  bootstrap_loaded_capacities root engine results suffix executable results_literal.
Let literals := bootstrap_loaded_literals suffix executable results_literal.
Let property := gateway_bootstrap_loaded_context native stable discipline buffers literals
  information (Vptr filename filename_offset) original.
Let result := gateway_bootstrap_resolved_paths native discipline canonicalizes root engine results original.

Local Lemma closed : gateway_ambient_closed backend property.
Proof. eapply gateway_bootstrap_loaded_context_ambient; exact threads. Qed.

Local Lemma literal_separate object bytes : In (object, bytes) literals -> object <> resolved.
Proof.
  unfold literals, bootstrap_loaded_literals; cbn [In]; intros [SAME |[SAME |[SAME |FALSE]]];
    try contradiction; inversion SAME; subst object bytes;
    pose proof STORAGE_DISTINCT as ALL; unfold bootstrap_storage_names in ALL;
    repeat rewrite NoDup_cons_iff in ALL; cbn [In] in ALL; intuition congruence.
Qed.

Theorem actual_bootstrap_realpath_setup temporaries memory :
  temporaries ! GatewaySource._tail = Some (Vlong (Int64.repr 30)) ->
  gateway_setup_path backend ge result property
    (Callstate (gateway_bootstrap_signature gateway_canonical_path_api)
      [Vptr filename filename_offset; Vptr resolved Ptrofs.zero]
      (bootstrap_realpath_cont information resolved (Vptr filename filename_offset)
        (Z.of_nat (length original)) temporaries) memory).
Proof.
  intro TAIL; cbn [gateway_bootstrap_signature]; apply gateway_setup_external; [exact closed |].
  intros before world returned after next observed INPUT OPERATION.
  pose proof (proj1 (proj2 (proj1 INPUT)) resolved 4096 Freeable
    ltac:(unfold buffers; cbn [In]; auto)) as RESOLVED.
  pose proof (gateway_bootstrap_capacity_weaken native before world resolved Ptrofs.zero 4096
    Freeable Writable RESOLVED ltac:(constructor)) as WRITABLE.
  assert (INFO_SEPARATE : information <> resolved) by (bootstrap_storage_distinct DISTINCT).
  assert (SOURCE_SEPARATE : filename <> resolved) by (bootstrap_storage_distinct DISTINCT).
  set (continuation := bootstrap_realpath_cont information resolved (Vptr filename filename_offset)
    (Z.of_nat (length original)) temporaries).
  assert (STEP : gateway_step backend ge
    (gateway_live (Callstate (gateway_bootstrap_signature gateway_canonical_path_api)
      [Vptr filename filename_offset; Vptr resolved Ptrofs.zero] continuation before) world)
    (gateway_primitive observed) (gateway_live (Returnstate returned continuation after) next))
    by (apply gateway_external_returned; exact OPERATION).
  destruct (gateway_bootstrap_actual_realpath_post backend io native stable discipline module_filename canonicalizes
    runtime ge (Vptr filename filename_offset) original resolved continuation before world returned after next observed
    (proj1 (proj1 INPUT)) (proj1 (proj2 (proj2 INPUT))) (proj2 (proj2 (proj2 INPUT)))
    (proj1 WRITABLE) (proj2 (proj2 WRITABLE))
    ltac:(intros object offset SAME; inversion SAME; subst; exact SOURCE_SEPARATE) STEP)
    as [POST [PERMISSIONS OBSERVATION]].
  destruct (gateway_actual_bootstrap_canonical_result backend io native stable discipline module_filename canonicalizes
    runtime ge before world information filename filename_offset original resolved continuation returned after next observed
    (proj2 INPUT) (proj1 WRITABLE) (proj2 (proj2 WRITABLE)) INFO_SEPARATE SOURCE_SEPARATE STEP)
    as [INFO [NULL |[canonical [VALUE [BOUND [CANONICAL CHECKED]]]]]].
  all: assert (BUFFERS : gateway_bootstrap_buffers native stable discipline buffers literals after next).
  all: try solve [eapply gateway_bootstrap_buffers_effect;
    [exact (proj1 INPUT) |exact (proj1 POST) |exact (proj1 (proj2 POST)) |
     exact (proj1 (proj2 (proj2 POST))) |exact PERMISSIONS |exact literal_separate]].
  - subst returned; exists property; split; [split; assumption |].
    destruct (actual_bootstrap_null_realpath_segment backend ge property information resolved (Vptr filename filename_offset)
      (Z.of_nat (length original)) temporaries after closed) as [changed SEGMENT].
    eapply gateway_setup_after_segment; [exact SEGMENT |apply bootstrap_rejected_setup; reflexivity].
  - subst returned.
    set (checked := gateway_bootstrap_check_context native stable discipline buffers literals
      information filename filename_offset original resolved canonical).
    assert (CLOSED : gateway_ambient_closed backend checked) by
      (eapply gateway_bootstrap_check_context_ambient; exact threads).
    exists checked; split; [split; assumption |].
    eapply gateway_setup_after_source.
    + eapply actual_bootstrap_canonical_to_length;
        [exact threads |exact CLOSED |intros current owner READY; exact (proj2 READY) |
         exact LENGTH_SYMBOL |exact LENGTH_FUNCTION].
    + exact CLOSED.
    + exact CLOSED.
    + intro current; eapply gateway_setup_post with
        (result := gateway_bootstrap_checked_paths native discipline root engine results original canonical).
      * intros final owner PATHS; exists canonical, world, next; split; assumption.
      * eapply actual_bootstrap_canonical_length_copies;
          [exact threads |exact runtime |exact SIZE |exact LAYOUT |exact DISTINCT |
           exact ORIGINAL_NONZERO | |exact LOADED_SIZE |exact ROOT_SYMBOL |exact ENGINE_SYMBOL |
           exact RESULTS_SYMBOL |exact SUFFIX_SYMBOL |exact EXECUTABLE_SYMBOL |exact RESULTS_LITERAL_SYMBOL |
           exact COMPARISON_SYMBOL |exact COMPARISON_FUNCTION |exact COPY_SYMBOL |exact COPY_FUNCTION |exact TAIL].
        destruct CHECKED as [_ [_ [_ [STRING _]]]].
        destruct STRING as [object [offset [POINTER [NONZERO _]]]]; exact NONZERO.
Qed.
End RealpathSetup.
