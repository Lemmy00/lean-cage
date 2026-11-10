(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual bound and absolute-name failures reach the real return. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess Readers.
From HostGateway Require Import GatewaySource GatewayMachine GatewaySourceSegments
  GatewaySourceSegmentAutomation GatewayFramedRuntime GatewayBootstrapSource
  GatewayBootstrapLengthSource GatewayBootstrapValidationSource GatewayBootstrapCopySource
  GatewayBootstrapFilename GatewayBootstrapCharacterSource GatewayBootstrapCharacter
  GatewayBootstrapInformation GatewayErrorRuntime GatewayBootstrapCopyEdges.
Import ListNotations.
Open Scope Z_scope.

Theorem actual_bootstrap_oversize_segment {World Event} (backend : gateway_backend World Event)
    (ge : Clight.genv) (canonical : bool) property information resolved temporaries memory size :
  gateway_ambient_closed backend property -> temporaries ! _size = Some (Vlong size) ->
  Int64.cmpu Cgt size (Int64.repr 4095) = true ->
  exists changed,
    gateway_source_segment backend ge property
      (State f_host_bootstrap (if canonical then bootstrap_canonical_validation else bootstrap_loaded_validation)
        (Kseq (if canonical then bootstrap_after_canonical_validation else bootstrap_after_loaded_validation) Kstop)
        (bootstrap_environment information resolved) temporaries memory)
      (State f_host_bootstrap bootstrap_path_reject
        (Kseq (if canonical then bootstrap_after_canonical_validation else bootstrap_after_loaded_validation) Kstop)
        (bootstrap_environment information resolved) changed memory) property.
Proof.
  intros CLOSED SIZE OVERSIZE; destruct canonical; eexists.
  all: let loads _ := fail "unexpected source load in oversize rejection" in
    let reduce _ :=
      cbn [sem_binary_operation sem_binarith classify_binarith cast_int_long typeof];
      try change (Int.signed (Int.repr 4095)) with 4095;
      rewrite ?OVERSIZE; cbn [bool_val classify_bool Val.of_bool]; reflexivity in
    gateway_segment_dynamic CLOSED loads reduce.
Qed.

Theorem actual_bootstrap_relative_loaded_segment {World Event} (backend : gateway_backend World Event)
    (ge : Clight.genv) property information resolved temporaries memory size object offset bytes :
  gateway_ambient_closed backend property -> gateway_bootstrap_information_layout ge ->
  (forall memory world, property memory world ->
    Mem.load Mptr memory information 0 = Some (Vptr object offset) /\
    gateway_error_cstring memory (Vptr object offset) bytes) ->
  temporaries ! _size = Some (Vlong size) -> temporaries ! _tail = Some (Vlong (Int64.repr 30)) ->
  Int64.cmpu Cgt size (Int64.repr 4095) = false -> Int64.cmpu Cle size (Int64.repr 30) = false ->
  hd Byte.zero bytes <> Byte.repr 47 ->
  exists changed,
    gateway_source_segment backend ge property
      (State f_host_bootstrap bootstrap_loaded_validation
        (Kseq bootstrap_after_loaded_validation Kstop) (bootstrap_environment information resolved) temporaries memory)
      (State f_host_bootstrap bootstrap_path_reject (Kseq bootstrap_after_loaded_validation Kstop)
        (bootstrap_environment information resolved) changed memory) property.
Proof.
  intros CLOSED LAYOUT INFORMATION SIZE TAIL BOUNDED LONG RELATIVE.
  assert (CHARACTER : Int.sign_ext 8 (Readers.byte_word (hd Byte.zero bytes)) <> Int.repr 47).
  { intro SAME; apply RELATIVE; apply (proj1 (bootstrap_signed_character_slash (hd Byte.zero bytes))); exact SAME. }
  eexists.
  let loads _ :=
    first [eapply gateway_bootstrap_filename_value; [exact LAYOUT |apply (proj1 (INFORMATION _ _ ltac:(eassumption)))]
      |eapply gateway_bootstrap_character_expression;
        [left; reflexivity |apply old_expression_value; apply value_temp; apply PTree.gss |
         apply (proj2 (INFORMATION _ _ ltac:(eassumption)))]] in
  let reduce _ :=
    cbn [sem_binary_operation sem_binarith classify_binarith cast_int_long typeof];
    try change (Int.signed (Int.repr 4095)) with 4095;
    rewrite ?BOUNDED, ?LONG;
    cbn [bool_val classify_bool Val.of_bool];
    cbn [classify_cast cast_int_int Int.cmp];
    rewrite ?(Int.eq_false _ _ CHARACTER); reflexivity in
  gateway_segment_dynamic CLOSED loads reduce.
Qed.

Theorem actual_bootstrap_relative_canonical_segment {World Event} (backend : gateway_backend World Event)
    (ge : Clight.genv) property information resolved temporaries memory size bytes :
  gateway_ambient_closed backend property ->
  (forall memory world, property memory world -> gateway_error_cstring memory (Vptr resolved Ptrofs.zero) bytes) ->
  temporaries ! _size = Some (Vlong size) -> temporaries ! _tail = Some (Vlong (Int64.repr 30)) ->
  Int64.cmpu Cgt size (Int64.repr 4095) = false -> Int64.cmpu Cle size (Int64.repr 30) = false ->
  hd Byte.zero bytes <> Byte.repr 47 ->
  exists changed,
    gateway_source_segment backend ge property
      (State f_host_bootstrap bootstrap_canonical_validation
        (Kseq bootstrap_after_canonical_validation Kstop) (bootstrap_environment information resolved) temporaries memory)
      (State f_host_bootstrap bootstrap_path_reject (Kseq bootstrap_after_canonical_validation Kstop)
        (bootstrap_environment information resolved) changed memory) property.
Proof.
  intros CLOSED INFORMATION SIZE TAIL BOUNDED LONG RELATIVE.
  assert (CHARACTER : Int.sign_ext 8 (Readers.byte_word (hd Byte.zero bytes)) <> Int.repr 47).
  { intro SAME; apply RELATIVE; apply (proj1 (bootstrap_signed_character_slash (hd Byte.zero bytes))); exact SAME. }
  eexists.
  let loads _ := eapply gateway_bootstrap_character_expression;
    [right; reflexivity |apply gateway_bootstrap_array_reference; reflexivity |eapply INFORMATION; eassumption] in
  let reduce _ :=
    cbn [sem_binary_operation sem_binarith classify_binarith cast_int_long typeof];
    try change (Int.signed (Int.repr 4095)) with 4095;
    rewrite ?BOUNDED, ?LONG; cbn [bool_val classify_bool Val.of_bool];
    cbn [classify_cast cast_int_int Int.cmp];
    rewrite ?(Int.eq_false _ _ CHARACTER); reflexivity in
  gateway_segment_dynamic CLOSED loads reduce.
Qed.
