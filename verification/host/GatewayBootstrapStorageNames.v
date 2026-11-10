(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual ELF symbols, fresh locals and the loader separate copy objects. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayBootstrapRegions GatewayBootstrapBuffers
  GatewayBootstrapCapacities GatewayBootstrapCopyState.
Import ListNotations.
Open Scope Z_scope.

Definition bootstrap_storage_names (root engine results suffix executable results_literal : block) :=
  [root; engine; results; suffix; executable; results_literal].

Theorem actual_bootstrap_global_names (ge : Clight.genv) root engine results suffix executable results_literal :
  Genv.find_symbol ge _host_root = Some root ->
  Genv.find_symbol ge _host_engine = Some engine ->
  Genv.find_symbol ge _host_default_results = Some results ->
  Genv.find_symbol ge _suffix = Some suffix ->
  Genv.find_symbol ge _executable = Some executable ->
  Genv.find_symbol ge _results = Some results_literal ->
  NoDup (bootstrap_storage_names root engine results suffix executable results_literal).
Proof.
  intros ROOT ENGINE RESULTS SUFFIX EXECUTABLE RESULTS_LITERAL.
  assert (ROOT_ENGINE : root <> engine) by
    (eapply Genv.global_addresses_distinct with (id1 := _host_root) (id2 := _host_engine);
      [discriminate |exact ROOT |exact ENGINE]).
  assert (ROOT_RESULTS : root <> results) by
    (eapply Genv.global_addresses_distinct with (id1 := _host_root) (id2 := _host_default_results);
      [discriminate |exact ROOT |exact RESULTS]).
  assert (ROOT_SUFFIX : root <> suffix) by
    (eapply Genv.global_addresses_distinct with (id1 := _host_root) (id2 := _suffix);
      [discriminate |exact ROOT |exact SUFFIX]).
  assert (ROOT_EXECUTABLE : root <> executable) by
    (eapply Genv.global_addresses_distinct with (id1 := _host_root) (id2 := _executable);
      [discriminate |exact ROOT |exact EXECUTABLE]).
  assert (ROOT_RESULTS_LITERAL : root <> results_literal) by
    (eapply Genv.global_addresses_distinct with (id1 := _host_root) (id2 := _results);
      [discriminate |exact ROOT |exact RESULTS_LITERAL]).
  assert (ENGINE_RESULTS : engine <> results) by
    (eapply Genv.global_addresses_distinct with (id1 := _host_engine) (id2 := _host_default_results);
      [discriminate |exact ENGINE |exact RESULTS]).
  assert (ENGINE_SUFFIX : engine <> suffix) by
    (eapply Genv.global_addresses_distinct with (id1 := _host_engine) (id2 := _suffix);
      [discriminate |exact ENGINE |exact SUFFIX]).
  assert (ENGINE_EXECUTABLE : engine <> executable) by
    (eapply Genv.global_addresses_distinct with (id1 := _host_engine) (id2 := _executable);
      [discriminate |exact ENGINE |exact EXECUTABLE]).
  assert (ENGINE_RESULTS_LITERAL : engine <> results_literal) by
    (eapply Genv.global_addresses_distinct with (id1 := _host_engine) (id2 := _results);
      [discriminate |exact ENGINE |exact RESULTS_LITERAL]).
  assert (RESULTS_SUFFIX : results <> suffix) by
    (eapply Genv.global_addresses_distinct with (id1 := _host_default_results) (id2 := _suffix);
      [discriminate |exact RESULTS |exact SUFFIX]).
  assert (RESULTS_EXECUTABLE : results <> executable) by
    (eapply Genv.global_addresses_distinct with (id1 := _host_default_results) (id2 := _executable);
      [discriminate |exact RESULTS |exact EXECUTABLE]).
  assert (RESULTS_RESULTS_LITERAL : results <> results_literal) by
    (eapply Genv.global_addresses_distinct with (id1 := _host_default_results) (id2 := _results);
      [discriminate |exact RESULTS |exact RESULTS_LITERAL]).
  assert (SUFFIX_EXECUTABLE : suffix <> executable) by
    (eapply Genv.global_addresses_distinct with (id1 := _suffix) (id2 := _executable);
      [discriminate |exact SUFFIX |exact EXECUTABLE]).
  assert (SUFFIX_RESULTS_LITERAL : suffix <> results_literal) by
    (eapply Genv.global_addresses_distinct with (id1 := _suffix) (id2 := _results);
      [discriminate |exact SUFFIX |exact RESULTS_LITERAL]).
  assert (EXECUTABLE_RESULTS_LITERAL : executable <> results_literal) by
    (eapply Genv.global_addresses_distinct with (id1 := _executable) (id2 := _results);
      [discriminate |exact EXECUTABLE |exact RESULTS_LITERAL]).
  unfold bootstrap_storage_names; repeat rewrite NoDup_cons_iff; cbn [In]; intuition (try constructor; congruence).
Qed.

Theorem bootstrap_loaded_storage_live {World} native stable discipline root engine results suffix executable results_literal
    memory (world : World) literals :
  gateway_bootstrap_buffers native stable discipline
    (bootstrap_loaded_capacities root engine results suffix executable results_literal) literals memory world ->
  forall object, In object (bootstrap_storage_names root engine results suffix executable results_literal) ->
    Mem.valid_block memory object.
Proof.
  intros [_ [CAPACITIES _]] object MEMBER; unfold bootstrap_storage_names in MEMBER; cbn [In] in MEMBER.
  repeat destruct MEMBER as [SAME |MEMBER]; try contradiction; subst object.
  - exact (proj1 (proj2 (proj2 (proj2 (proj2 (CAPACITIES root 4096 Writable
      ltac:(unfold bootstrap_loaded_capacities; cbn [In]; auto 12))))))).
  - exact (proj1 (proj2 (proj2 (proj2 (proj2 (CAPACITIES engine 4096 Writable
      ltac:(unfold bootstrap_loaded_capacities; cbn [In]; auto 12))))))).
  - exact (proj1 (proj2 (proj2 (proj2 (proj2 (CAPACITIES results 4096 Writable
      ltac:(unfold bootstrap_loaded_capacities; cbn [In]; auto 12))))))).
  - exact (proj1 (proj2 (proj2 (proj2 (proj2 (CAPACITIES suffix 31 Readable
      ltac:(unfold bootstrap_loaded_capacities; cbn [In]; auto 12))))))).
  - exact (proj1 (proj2 (proj2 (proj2 (proj2 (CAPACITIES executable 19 Readable
      ltac:(unfold bootstrap_loaded_capacities; cbn [In]; auto 12))))))).
  - exact (proj1 (proj2 (proj2 (proj2 (proj2 (CAPACITIES results_literal 21 Readable
      ltac:(unfold bootstrap_loaded_capacities; cbn [In]; auto 12))))))).
Qed.

Theorem bootstrap_allocated_storage_names {World} native stable discipline root engine results suffix executable results_literal
    memory (world : World) literals information resolved :
  gateway_bootstrap_buffers native stable discipline
    (bootstrap_loaded_capacities root engine results suffix executable results_literal) literals memory world ->
  NoDup (bootstrap_storage_names root engine results suffix executable results_literal) ->
  information <> resolved -> ~ Mem.valid_block memory information -> ~ Mem.valid_block memory resolved ->
  NoDup (information :: resolved :: bootstrap_storage_names root engine results suffix executable results_literal).
Proof.
  intros BUFFERS NAMES DIFFERENT INFO RESOLVED.
  pose proof (bootstrap_loaded_storage_live native stable discipline root engine results suffix executable results_literal
    memory world literals BUFFERS) as LIVE.
  constructor.
  - cbn [In]; intros [SAME |MEMBER]; [congruence |apply INFO; apply LIVE; exact MEMBER].
  - constructor; [intro MEMBER; apply RESOLVED; apply LIVE; exact MEMBER |exact NAMES].
Qed.

Theorem bootstrap_loader_copy_names {World} native stable discipline root engine results suffix executable results_literal
    memory (world : World) literals information resolved filename :
  gateway_bootstrap_buffers native stable discipline
    ((information, 32, Freeable) :: (resolved, 4096, Freeable) ::
      bootstrap_loaded_capacities root engine results suffix executable results_literal) literals memory world ->
  NoDup (information :: resolved :: bootstrap_storage_names root engine results suffix executable results_literal) ->
  ~ native world filename ->
  NoDup (bootstrap_copy_names information resolved filename root engine results executable results_literal).
Proof.
  intros [_ [CAPACITIES _]] NAMES PUBLIC.
  assert (NOTIN : ~ In filename (information :: resolved ::
    bootstrap_storage_names root engine results suffix executable results_literal)).
  { intro MEMBER; unfold bootstrap_storage_names in MEMBER; cbn [In] in MEMBER.
    repeat destruct MEMBER as [SAME |MEMBER]; try contradiction; subst filename; apply PUBLIC.
    - exact (proj1 (CAPACITIES information 32 Freeable
        ltac:(unfold bootstrap_loaded_capacities; cbn [In]; auto 15))).
    - exact (proj1 (CAPACITIES resolved 4096 Freeable
        ltac:(unfold bootstrap_loaded_capacities; cbn [In]; auto 15))).
    - exact (proj1 (CAPACITIES root 4096 Writable
        ltac:(unfold bootstrap_loaded_capacities; cbn [In]; auto 15))).
    - exact (proj1 (CAPACITIES engine 4096 Writable
        ltac:(unfold bootstrap_loaded_capacities; cbn [In]; auto 15))).
    - exact (proj1 (CAPACITIES results 4096 Writable
        ltac:(unfold bootstrap_loaded_capacities; cbn [In]; auto 15))).
    - exact (proj1 (CAPACITIES suffix 31 Readable
        ltac:(unfold bootstrap_loaded_capacities; cbn [In]; auto 15))).
    - exact (proj1 (CAPACITIES executable 19 Readable
        ltac:(unfold bootstrap_loaded_capacities; cbn [In]; auto 15))).
    - exact (proj1 (CAPACITIES results_literal 21 Readable
        ltac:(unfold bootstrap_loaded_capacities; cbn [In]; auto 15))). }
  unfold bootstrap_storage_names in NAMES, NOTIN; unfold bootstrap_copy_names.
  repeat rewrite NoDup_cons_iff in NAMES |- *; cbn [In] in *; intuition (try constructor; congruence).
Qed.
