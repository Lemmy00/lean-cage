(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual loaded-path guards reach memcmp with the same filename bytes. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess Readers.
From HostGateway Require Import GatewaySource GatewayMachine GatewaySourcePaths GatewayFramedRuntime
  GatewayBootstrapABI GatewayBootstrapSource GatewayBootstrapFilename GatewayBootstrapInformation
  GatewayBootstrapValidationSource GatewayBootstrapValidationPrefix GatewayBootstrapCharacterSource
  GatewayBootstrapSuffixSource GatewayThreadRuntime GatewayErrorRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition bootstrap_loaded_comparison_temporaries filename temporaries :=
  PTree.set _t'17 filename (PTree.set _t'5 (Vint Int.zero)
    (PTree.set _t'19 (Vint (Int.repr 47))
      (PTree.set _t'18 filename (PTree.set _t'4 (Vint Int.zero) temporaries)))).
Definition bootstrap_loaded_comparison_cont information resolved filename temporaries :=
  Kcall (Some _t'7) f_host_bootstrap (bootstrap_environment information resolved)
    (bootstrap_loaded_comparison_temporaries filename temporaries)
    (Kseq (Sset _t'6 (Ecast (Etempvar _t'7 tint) tbool))
      (Kseq (Sifthenelse (Etempvar _t'6 tint) bootstrap_path_reject Sskip)
        (Kseq bootstrap_after_loaded_validation Kstop))).

Section LoadedCompare.
Context {World Event} (backend : gateway_backend World Event) io native stable discipline thread_errno
  (runtime : gateway_thread_runtime backend io native stable discipline thread_errno).
Variable ge : Clight.genv.
Hypothesis LAYOUT : gateway_bootstrap_information_layout ge.
Variables (information resolved object suffix symbol : block) (offset : ptrofs) (bytes : list Byte.int).
Let filename := Vptr object offset.
Variable property : mem -> World -> Prop.
Hypothesis CLOSED : gateway_ambient_closed backend property.
Hypothesis INFORMATION : forall memory world, property memory world ->
  gateway_bootstrap_filename_information native stable discipline information filename bytes memory world.

Theorem actual_bootstrap_loaded_compare temporaries memory :
  Genv.find_symbol ge _memcmp = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some (gateway_bootstrap_signature gateway_memory_compare_api) ->
  Genv.find_symbol ge _suffix = Some suffix ->
  temporaries ! _size = Some (Vlong (Int64.repr (Z.of_nat (length bytes)))) ->
  temporaries ! _tail = Some (Vlong (Int64.repr 30)) ->
  30 < Z.of_nat (length bytes) <= 4095 -> hd Byte.zero bytes = Byte.repr 47 ->
  gateway_source_path backend ge (gateway_bootstrap_signature gateway_memory_compare_api)
    [Vptr object (Ptrofs.add offset (Ptrofs.repr (Z.of_nat (length bytes) - 30)));
     Vptr suffix Ptrofs.zero; Vlong (Int64.repr 30)]
    (bootstrap_loaded_comparison_cont information resolved filename temporaries) property
    (State f_host_bootstrap bootstrap_loaded_validation (Kseq bootstrap_after_loaded_validation Kstop)
      (bootstrap_environment information resolved) temporaries memory) property.
Proof.
  intros SYMBOL FUNCTION SUFFIX SIZE TAIL LENGTH SLASH.
  assert (BOUNDED : Int64.cmpu Cgt (Int64.repr (Z.of_nat (length bytes))) (Int64.repr 4095) = false).
  { unfold Int64.cmpu, Int64.ltu; rewrite !Int64.unsigned_repr by
      (change Int64.max_unsigned with 18446744073709551615; lia).
    destruct (zlt 4095 (Z.of_nat (length bytes))); [lia |reflexivity]. }
  assert (LONG : Int64.cmpu Cle (Int64.repr (Z.of_nat (length bytes))) (Int64.repr 30) = false).
  { unfold Int64.cmpu, Int64.ltu; rewrite !Int64.unsigned_repr by
      (change Int64.max_unsigned with 18446744073709551615; lia).
    destruct (zlt 30 (Z.of_nat (length bytes))); [reflexivity |lia]. }
  rewrite (proj1 actual_bootstrap_validation_fragments).
  eapply gateway_bootstrap_validation_lengths;
    [exact CLOSED |exact SIZE |exact TAIL |exact BOUNDED |exact LONG |].
  eapply actual_bootstrap_loaded_character; [exact LAYOUT |exact CLOSED |exact INFORMATION |].
  rewrite SLASH.
  eapply gateway_bootstrap_validation_character; [exact CLOSED |apply PTree.gss |].
  eapply gateway_source_same with (target := State f_host_bootstrap
    (Sset _t'17 bootstrap_filename_expression)
    (Kseq (bootstrap_suffix_call _t'7 (Etempvar _t'17 (tptr tschar)))
      (Kseq (Sset _t'6 (Ecast (Etempvar _t'7 tint) tbool))
        (Kseq (Sifthenelse (Etempvar _t'6 tint) bootstrap_path_reject Sskip)
          (Kseq bootstrap_after_loaded_validation Kstop))))
    (bootstrap_environment information resolved)
    (PTree.set _t'5 (Vint Int.zero) (PTree.set _t'19 (Vint (Int.repr 47))
      (PTree.set _t'18 filename (PTree.set _t'4 (Vint Int.zero) temporaries)))) memory);
    [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_seq |].
  eapply gateway_source_same with (target := State f_host_bootstrap Sskip
    (Kseq (bootstrap_suffix_call _t'7 (Etempvar _t'17 (tptr tschar)))
      (Kseq (Sset _t'6 (Ecast (Etempvar _t'7 tint) tbool))
        (Kseq (Sifthenelse (Etempvar _t'6 tint) bootstrap_path_reject Sskip)
          (Kseq bootstrap_after_loaded_validation Kstop))))
    (bootstrap_environment information resolved)
    (bootstrap_loaded_comparison_temporaries filename temporaries) memory).
  - exact CLOSED.
  - cbn; tauto.
  - intros before world GOOD; destruct (INFORMATION _ _ GOOD) as [[_ [_ LOAD]] _]; apply certified_set_edge, gateway_bootstrap_filename_value;
      [exact LAYOUT |exact LOAD].
  - eapply gateway_source_same with (target := State f_host_bootstrap
      (bootstrap_suffix_call _t'7 (Etempvar _t'17 (tptr tschar)))
      (Kseq (Sset _t'6 (Ecast (Etempvar _t'7 tint) tbool))
        (Kseq (Sifthenelse (Etempvar _t'6 tint) bootstrap_path_reject Sskip)
          (Kseq bootstrap_after_loaded_validation Kstop)))
      (bootstrap_environment information resolved)
      (bootstrap_loaded_comparison_temporaries filename temporaries) memory);
      [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_skip_seq |].
    eapply gateway_source_same with (target := Callstate
      (gateway_bootstrap_signature gateway_memory_compare_api)
      [Vptr object (Ptrofs.add offset (Ptrofs.repr (Z.of_nat (length bytes) - 30)));
       Vptr suffix Ptrofs.zero; Vlong (Int64.repr 30)]
      (bootstrap_loaded_comparison_cont information resolved filename temporaries) memory).
    + exact CLOSED.
    + cbn; tauto.
    + intros; eapply gateway_bootstrap_suffix_call_edge;
        [reflexivity |exact SYMBOL |exact FUNCTION |reflexivity |exact SUFFIX |left; reflexivity |
         apply old_expression_value, value_temp, PTree.gss | | |lia].
      * unfold bootstrap_loaded_comparison_temporaries; repeat rewrite PTree.gso by discriminate; exact SIZE.
      * unfold bootstrap_loaded_comparison_temporaries; repeat rewrite PTree.gso by discriminate; exact TAIL.
    + constructor; intros; assumption.
Qed.
End LoadedCompare.
