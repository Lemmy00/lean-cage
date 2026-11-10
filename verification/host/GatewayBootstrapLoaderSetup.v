(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The real dladdr result drives both rejection and all successful source checks. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayRuntime GatewaySetupPaths
  GatewaySetupComposition GatewaySetupResults GatewayFramedRuntime GatewayBootstrapABI GatewayBootstrapRuntime
  GatewayBootstrapSource GatewayBootstrapFilename GatewayBootstrapInformation GatewayBootstrapRegions
  GatewayBootstrapStorageNames GatewayBootstrapBuffers GatewayBootstrapCapacities GatewayBootstrapCopyState
  GatewayBootstrapCheckContext GatewayBootstrapLoadedSetup GatewayBootstrapRejection GatewayBootstrapValidationChecks
  GatewayThreadRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_bootstrap_named_paths {World} native discipline
    (module_filename : World -> val -> list Byte.int -> Prop) canonicalizes
    entry root engine results memory (world : World) : Prop :=
  exists original located,
    module_filename located (Vptr entry Ptrofs.zero) original /\
    gateway_bootstrap_loaded_paths native discipline canonicalizes root engine results original memory world.

Theorem bootstrap_loader_information_access {World} native memory (world : World) information :
  gateway_bootstrap_capacity native memory world information Ptrofs.zero 32 Freeable ->
  Mem.valid_access memory Mptr information 0 Writable.
Proof.
  intros [_ [_ [_ [_ [LIVE RANGE]]]]].
  split.
  - change (Mem.range_perm memory information 0 (0 + 8) Cur Writable).
    intros position INSIDE; eapply Mem.perm_implies; [apply RANGE; change (0 <= position < 0 + 32); lia |constructor].
  - change (8 | 0); apply Z.divide_0_r.
Qed.

Section LoaderSetup.
Context {World Event} (backend : gateway_backend World Event) io native stable discipline thread_errno
    module_filename canonicalizes
    (threads : gateway_thread_runtime backend io native stable discipline thread_errno)
    (runtime : gateway_bootstrap_runtime backend io native stable discipline module_filename canonicalizes).
Variable ge : Clight.genv.
Variables information resolved entry root engine results suffix executable results_literal
    length_symbol comparison_symbol realpath_symbol copy_symbol : block.
Hypotheses
  (SIZE : sizeof ge gateway_loader_information_type = 32)
  (LAYOUT : gateway_bootstrap_information_layout ge)
  (STORAGE_DISTINCT : NoDup (information :: resolved ::
    bootstrap_storage_names root engine results suffix executable results_literal))
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
Let property := gateway_bootstrap_buffers native stable discipline buffers literals.
Let result := gateway_bootstrap_named_paths native discipline module_filename canonicalizes entry root engine results.

Local Lemma closed : gateway_ambient_closed backend property.
Proof. eapply gateway_bootstrap_buffers_ambient; exact threads. Qed.

Local Lemma literal_separate object bytes : In (object, bytes) literals -> object <> information.
Proof.
  unfold literals, bootstrap_loaded_literals; cbn [In]; intros [SAME |[SAME |[SAME |FALSE]]];
    try contradiction; inversion SAME; subst object bytes;
    pose proof STORAGE_DISTINCT as ALL; unfold bootstrap_storage_names in ALL;
    repeat rewrite NoDup_cons_iff in ALL; cbn [In] in ALL; intuition congruence.
Qed.

Theorem actual_bootstrap_loader_setup memory :
  gateway_setup_path backend ge result property
    (Callstate (gateway_bootstrap_signature gateway_loader_address_api)
      [Vptr entry Ptrofs.zero; Vptr information Ptrofs.zero]
      (bootstrap_loader_cont information resolved) memory).
Proof.
  cbn [gateway_bootstrap_signature]; apply gateway_setup_external; [exact closed |].
  intros before world returned after next observed INPUT OPERATION.
  pose proof (proj1 (proj2 INPUT) information 32 Freeable ltac:(unfold buffers; cbn [In]; auto)) as INFORMATION.
  pose proof (gateway_bootstrap_capacity_weaken native before world information Ptrofs.zero 32
    Freeable Writable INFORMATION ltac:(constructor)) as WRITABLE.
  assert (ACTUAL : gateway_bootstrap_operation backend gateway_loader_address_api
    [Vptr entry Ptrofs.zero; Vptr information Ptrofs.zero] before world returned after next observed)
    by exact OPERATION.
  destruct (@gateway_loader_address_operation World Event backend io native stable discipline module_filename canonicalizes runtime before world (Vptr entry Ptrofs.zero)
    information Ptrofs.zero returned after next observed (proj1 INPUT) (proj1 WRITABLE) (proj2 (proj2 WRITABLE))
    (bootstrap_loader_information_access native before world information INFORMATION) ACTUAL)
    as [POST [PERMISSIONS [status [VALUE SUCCESS]]]].
  assert (BUFFERS : property after next).
  { eapply gateway_bootstrap_buffers_effect;
      [exact INPUT |exact (proj1 POST) |exact (proj1 (proj2 POST)) |
       exact (proj1 (proj2 (proj2 POST))) |exact PERMISSIONS |exact literal_separate]. }
  subst returned; destruct (Int.eq_dec status Int.zero) as [ZERO |NONZERO].
  - subst status; exists property; split; [exact BUFFERS |].
    destruct (actual_bootstrap_zero_loader_segment backend ge property information resolved after closed)
      as [temporaries SEGMENT].
    eapply gateway_setup_after_segment; [exact SEGMENT |apply bootstrap_rejected_setup; reflexivity].
  - destruct (SUCCESS NONZERO) as [filename [FIELD [NULL |[original [name [offset [POINTER
      [STRING [PROTECTED [PUBLIC IDENTITY]]]]]]]]]].
    + subst filename.
      set (null_information := fun memory owner =>
        property memory owner /\ gateway_bootstrap_information native discipline information Vnullptr memory owner).
      assert (CLOSED : gateway_ambient_closed backend null_information).
      { intros first owner last changed [CELLS INFO] INTERFERENCE; split.
        - eapply closed; eassumption.
        - eapply gateway_bootstrap_information_ambient; [exact threads |exact INFO |exact INTERFERENCE]. }
      exists null_information; split.
      * split; [exact BUFFERS |]. split; [exact (proj1 POST) |]. split; [|exact FIELD].
        exact (proj1 (proj1 (proj2 BUFFERS) information 32 Freeable
          ltac:(unfold buffers; cbn [In]; auto))).
      * destruct (actual_bootstrap_null_loader_name_segment backend ge null_information information resolved after status
          CLOSED LAYOUT ltac:(intros current owner [_ [_ [_ CURRENT_FIELD]]]; exact CURRENT_FIELD) NONZERO)
          as [temporaries SEGMENT].
        eapply gateway_setup_after_segment; [exact SEGMENT |apply bootstrap_rejected_setup; reflexivity].
    + subst filename.
      set (loaded := gateway_bootstrap_loaded_context native stable discipline buffers literals
        information (Vptr name offset) original).
      assert (DISTINCT : NoDup (bootstrap_copy_names information resolved name root engine results executable results_literal)).
      { eapply bootstrap_loader_copy_names; [exact BUFFERS |exact STORAGE_DISTINCT |exact PUBLIC]. }
      assert (NONZERO_BYTES : ~ In Byte.zero original).
      { destruct STRING as [object [position [SAME [NONZERO_BYTES _]]]]; exact NONZERO_BYTES. }
      exists loaded; split.
      * split; [exact BUFFERS |]. split; [|split; assumption].
        split; [exact (proj1 POST) |]. split; [|exact FIELD].
        exact (proj1 (proj1 (proj2 BUFFERS) information 32 Freeable
          ltac:(unfold buffers; cbn [In]; auto))).
      * eapply gateway_setup_post with
          (result := gateway_bootstrap_loaded_paths native discipline canonicalizes root engine results original).
        -- intros final owner PATHS; exists original, next; split; assumption.
        -- eapply actual_bootstrap_nonnull_loader_setup; eassumption.
Qed.
End LoaderSetup.
