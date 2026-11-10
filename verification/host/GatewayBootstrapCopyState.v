(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Each actual copy phase retains its exact earlier byte spans. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Clight.
From HostGateway Require Import GatewayBootstrapConstants GatewayBootstrapPathContext GatewayBootstrapSpans
  GatewayBootstrapBuffers GatewayBootstrapRuntime GatewayThreadRuntime GatewayErrorRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition bootstrap_copy_buffers information resolved root engine results : list (block * Z * permission) :=
  [(information, 32, Freeable); (resolved, 4096, Freeable); (root, 4096, Writable);
   (engine, 4096, Writable); (results, 4096, Writable)].

Definition bootstrap_copy_names information resolved filename root engine results executable results_literal : list block :=
  [information; resolved; filename; root; engine; results; executable; results_literal].

Definition bootstrap_copy_spans phase resolved filename filename_offset root engine results executable results_literal
    (root_bytes api_bytes : list Byte.int) : list (block * ptrofs * list Byte.int) :=
  let initial := [(resolved, Ptrofs.zero, root_bytes); (filename, filename_offset, api_bytes);
    (executable, Ptrofs.zero, bootstrap_executable_bytes ++ [Byte.zero]);
    (results_literal, Ptrofs.zero, bootstrap_results_bytes ++ [Byte.zero])] in
  let copied_root := (root, Ptrofs.zero, root_bytes) :: initial in
  let terminated_root := (root, Ptrofs.zero, root_bytes ++ [Byte.zero]) :: copied_root in
  let copied_engine := (engine, Ptrofs.zero, root_bytes) :: terminated_root in
  let completed_engine := (engine, Ptrofs.repr (Z.of_nat (length root_bytes)),
    bootstrap_executable_bytes ++ [Byte.zero]) :: copied_engine in
  let copied_results := (results, Ptrofs.zero, api_bytes) :: completed_engine in
  let completed_results := (results, Ptrofs.repr (Z.of_nat (length api_bytes)),
    bootstrap_results_bytes ++ [Byte.zero]) :: copied_results in
  match phase with
  | O => initial | S O => copied_root | S (S O) => terminated_root
  | S (S (S O)) => copied_engine | S (S (S (S O))) => completed_engine
  | S (S (S (S (S O)))) => copied_results | _ => completed_results end.

Ltac bootstrap_storage_distinct no_duplicates :=
  let ALL := fresh "ALL" in
  pose proof no_duplicates as ALL;
  unfold bootstrap_copy_names in ALL;
  repeat rewrite NoDup_cons_iff in ALL;
  cbn [In] in ALL;
  intuition congruence.

Theorem bootstrap_completed_copy_strings {World} native stable memory world resolved filename filename_offset
    root engine results executable results_literal root_bytes api_bytes :
  @gateway_bootstrap_spans World native stable
    (bootstrap_copy_spans 6 resolved filename filename_offset root engine results executable results_literal
      root_bytes api_bytes) memory world ->
  ~ In Byte.zero root_bytes -> ~ In Byte.zero api_bytes ->
  Z.of_nat (length root_bytes) <= 4065 -> Z.of_nat (length api_bytes) <= 4065 ->
  gateway_error_cstring memory (Vptr root Ptrofs.zero) root_bytes /\
  gateway_error_cstring memory (Vptr engine Ptrofs.zero) (root_bytes ++ bootstrap_executable_bytes) /\
  gateway_error_cstring memory (Vptr results Ptrofs.zero) (api_bytes ++ bootstrap_results_bytes).
Proof.
  intros SPANS ROOT_NONZERO API_NONZERO ROOT_SIZE API_SIZE.
  split.
  - eapply gateway_bootstrap_spans_cstring; [exact SPANS |cbn [bootstrap_copy_spans In]; auto 20 |exact ROOT_NONZERO].
  - split; eapply gateway_bootstrap_spans_joined_cstring;
      [exact SPANS |cbn [bootstrap_copy_spans In]; auto 20 |cbn [bootstrap_copy_spans In]; auto 20 |exact ROOT_NONZERO |
       vm_compute; intuition discriminate |change Ptrofs.modulus with 18446744073709551616; cbn; lia |
       exact SPANS |cbn [bootstrap_copy_spans In]; auto 20 |cbn [bootstrap_copy_spans In]; auto 20 |exact API_NONZERO |
       vm_compute; intuition discriminate |change Ptrofs.modulus with 18446744073709551616; cbn; lia].
Qed.

Definition bootstrap_copy_destination phase (root engine results : block) := match phase with
  | O | S O => root | S (S O) | S (S (S O)) => engine | _ => results end.
Definition bootstrap_copy_offset phase (root_bytes api_bytes : list Byte.int) := match phase with
  | S O | S (S (S O)) => Ptrofs.repr (Z.of_nat (length root_bytes))
  | S (S (S (S (S O)))) => Ptrofs.repr (Z.of_nat (length api_bytes))
  | _ => Ptrofs.zero end.
Definition bootstrap_copy_amount phase (root_bytes api_bytes : list Byte.int) : Z := match phase with
  | S O => 1 | S (S (S O)) => 19 | S (S (S (S O))) => Z.of_nat (length api_bytes)
  | S (S (S (S (S O)))) => 21 | _ => Z.of_nat (length root_bytes) end.

Theorem bootstrap_copy_retained_outside phase information resolved filename filename_offset
    root engine results executable results_literal root_bytes api_bytes :
  (phase < 6)%nat ->
  NoDup (bootstrap_copy_names information resolved filename root engine results executable results_literal) ->
  Z.of_nat (length root_bytes) <= 4065 -> Z.of_nat (length api_bytes) <= 4065 ->
  forall object offset kept,
    In (object, offset, kept) (bootstrap_copy_spans phase resolved filename filename_offset
      root engine results executable results_literal root_bytes api_bytes) ->
    forall position, Ptrofs.unsigned offset <= position < Ptrofs.unsigned offset + Z.of_nat (length kept) ->
    ~ gateway_native_region (bootstrap_copy_destination phase root engine results)
      (bootstrap_copy_offset phase root_bytes api_bytes) (bootstrap_copy_amount phase root_bytes api_bytes) object position.
Proof.
  intros PHASE DISTINCT ROOT_SIZE API_SIZE.
  assert (ROOT_SHIFT : Ptrofs.unsigned (Ptrofs.repr (Z.of_nat (length root_bytes))) = Z.of_nat (length root_bytes)).
  { apply Ptrofs.unsigned_repr; change Ptrofs.max_unsigned with 18446744073709551615; lia. }
  assert (API_SHIFT : Ptrofs.unsigned (Ptrofs.repr (Z.of_nat (length api_bytes))) = Z.of_nat (length api_bytes)).
  { apply Ptrofs.unsigned_repr; change Ptrofs.max_unsigned with 18446744073709551615; lia. }
  destruct phase as [|[|[|[|[|[|phase]]]]]]; try lia;
    intros object offset kept MEMBER;
    cbn [bootstrap_copy_spans In] in MEMBER.
  all: repeat match type of MEMBER with _ \/ _ => destruct MEMBER as [MEMBER |MEMBER] end.
  all: try contradiction.
  all: inversion MEMBER; subst object offset kept; clear MEMBER;
    intros position RANGE [SAME WRITE];
    cbn [bootstrap_copy_destination bootstrap_copy_offset bootstrap_copy_amount] in WRITE, SAME;
    rewrite ?ROOT_SHIFT, ?API_SHIFT in WRITE;
    change (Ptrofs.unsigned Ptrofs.zero) with 0 in RANGE, WRITE;
    rewrite ?ROOT_SHIFT, ?API_SHIFT in RANGE.
  all: first [lia | let DIFFERENT := fresh "DIFFERENT" in
    match type of SAME with ?one = ?another =>
      assert (DIFFERENT : one <> another) by (bootstrap_storage_distinct DISTINCT);
      exact (DIFFERENT SAME) end].
Qed.
