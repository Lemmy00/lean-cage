(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The canonical path guards compare the same initialized realpath buffer. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewaySourcePaths GatewaySourceAutomation
  GatewayFramedRuntime GatewayBootstrapABI GatewayBootstrapSource GatewayBootstrapValidationSource
  GatewayBootstrapValidationPrefix GatewayBootstrapCharacterSource GatewayBootstrapSuffixSource
  GatewayBootstrapCopySource GatewayBootstrapCopyEdges GatewayBootstrapCanonicalResult
  GatewayBootstrapCanonicalAmbient GatewayThreadRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition bootstrap_canonical_comparison_temporaries temporaries :=
  PTree.set _t'11 (Vint Int.zero)
    (PTree.set _t'15 (Vint (Int.repr 47)) (PTree.set _t'10 (Vint Int.zero) temporaries)).
Definition bootstrap_canonical_comparison_cont information resolved temporaries :=
  Kcall (Some _t'13) f_host_bootstrap (bootstrap_environment information resolved)
    (bootstrap_canonical_comparison_temporaries temporaries)
    (Kseq (Sset _t'12 (Ecast (Etempvar _t'13 tint) tbool))
      (Kseq (Sifthenelse (Etempvar _t'12 tint) bootstrap_path_reject Sskip)
        (Kseq bootstrap_after_canonical_validation Kstop))).

Theorem actual_bootstrap_canonical_compare {World Event} (backend : gateway_backend World Event)
    io native stable discipline thread_errno
    (runtime : gateway_thread_runtime backend io native stable discipline thread_errno)
    (ge : Clight.genv) information resolved object offset original canonical suffix symbol temporaries memory (property : mem -> World -> Prop) :
  gateway_ambient_closed backend property ->
  (forall memory world, property memory world ->
    gateway_bootstrap_canonical_information native stable discipline
      information object offset original resolved canonical memory world) ->
  Genv.find_symbol ge _memcmp = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some (gateway_bootstrap_signature gateway_memory_compare_api) ->
  Genv.find_symbol ge _suffix = Some suffix ->
  temporaries ! _size = Some (Vlong (Int64.repr (Z.of_nat (length canonical)))) ->
  temporaries ! _tail = Some (Vlong (Int64.repr 30)) ->
  30 < Z.of_nat (length canonical) <= 4095 -> hd Byte.zero canonical = Byte.repr 47 ->
  gateway_source_path backend ge (gateway_bootstrap_signature gateway_memory_compare_api)
    [Vptr resolved (Ptrofs.add Ptrofs.zero (Ptrofs.repr (Z.of_nat (length canonical) - 30)));
     Vptr suffix Ptrofs.zero; Vlong (Int64.repr 30)]
    (bootstrap_canonical_comparison_cont information resolved temporaries)
    property
    (State f_host_bootstrap bootstrap_canonical_validation
      (Kseq bootstrap_after_canonical_validation Kstop) (bootstrap_environment information resolved)
      temporaries memory)
    property.
Proof.
  intros CLOSED INFORMATION SYMBOL FUNCTION SUFFIX SIZE TAIL LENGTH SLASH.
  assert (BOUNDED : Int64.cmpu Cgt (Int64.repr (Z.of_nat (length canonical))) (Int64.repr 4095) = false).
  { unfold Int64.cmpu, Int64.ltu; rewrite !Int64.unsigned_repr by
      (change Int64.max_unsigned with 18446744073709551615; lia).
    destruct (zlt 4095 (Z.of_nat (length canonical))); [lia |reflexivity]. }
  assert (LONG : Int64.cmpu Cle (Int64.repr (Z.of_nat (length canonical))) (Int64.repr 30) = false).
  { unfold Int64.cmpu, Int64.ltu; rewrite !Int64.unsigned_repr by
      (change Int64.max_unsigned with 18446744073709551615; lia).
    destruct (zlt 30 (Z.of_nat (length canonical))); [reflexivity |lia]. }
  rewrite (proj2 actual_bootstrap_validation_fragments).
  eapply gateway_bootstrap_validation_lengths;
    [exact CLOSED |exact SIZE |exact TAIL |exact BOUNDED |exact LONG |].
  repeat gateway_source_structure CLOSED.
  eapply gateway_source_same with (target := State f_host_bootstrap Sskip
    (Kseq (Sset _t'11 (Ecast (Ebinop One (Etempvar _t'15 tschar)
      (Econst_int (Int.repr 47) tint) tint) tbool))
      (Kseq (Sifthenelse (Etempvar _t'11 tint) (Sset _t'12 (Econst_int Int.one tint))
        (Ssequence (bootstrap_suffix_call _t'13 (Evar _resolved (tarray tschar 4096)))
          (Sset _t'12 (Ecast (Etempvar _t'13 tint) tbool))))
        (Kseq (Sifthenelse (Etempvar _t'12 tint) bootstrap_path_reject Sskip)
          (Kseq bootstrap_after_canonical_validation Kstop))))
    (bootstrap_environment information resolved)
    (PTree.set _t'15 (Vint (Int.repr 47)) (PTree.set _t'10 (Vint Int.zero) temporaries)) memory).
  - exact CLOSED.
  - cbn; tauto.
  - intros before world GOOD; destruct (INFORMATION _ _ GOOD) as [_ [_ [_ [STRING _]]]]; apply certified_set_edge.
    pose proof (gateway_bootstrap_character_expression ge (bootstrap_environment information resolved)
      (PTree.set _t'10 (Vint Int.zero) temporaries) before (Evar _resolved (tarray tschar 4096))
      resolved Ptrofs.zero canonical (or_intror eq_refl)
      (gateway_bootstrap_array_reference ge (bootstrap_environment information resolved)
        (PTree.set _t'10 (Vint Int.zero) temporaries) before _resolved 4096 resolved eq_refl) STRING) as VALUE.
    rewrite SLASH in VALUE; exact VALUE.
  - repeat gateway_source_structure CLOSED.
    eapply gateway_bootstrap_validation_character with (low := _t'10)
      (byte_setup := bootstrap_canonical_byte_setup) (prepare_compare := fun call => call)
      (path := Evar _resolved (tarray tschar 4096)); [exact CLOSED |apply PTree.gss |].
    eapply gateway_source_same with (target := Callstate
      (gateway_bootstrap_signature gateway_memory_compare_api)
      [Vptr resolved (Ptrofs.add Ptrofs.zero (Ptrofs.repr (Z.of_nat (length canonical) - 30)));
       Vptr suffix Ptrofs.zero; Vlong (Int64.repr 30)]
      (bootstrap_canonical_comparison_cont information resolved temporaries) memory).
    + exact CLOSED.
    + cbn; tauto.
    + intros; eapply gateway_bootstrap_suffix_call_edge;
        [reflexivity |exact SYMBOL |exact FUNCTION |reflexivity |exact SUFFIX |right; reflexivity |
         apply gateway_bootstrap_array_reference; reflexivity | | |lia].
      * unfold bootstrap_canonical_comparison_temporaries;
          repeat rewrite PTree.gso by discriminate; exact SIZE.
      * unfold bootstrap_canonical_comparison_temporaries;
          repeat rewrite PTree.gso by discriminate; exact TAIL.
    + constructor; intros; assumption.
Qed.
