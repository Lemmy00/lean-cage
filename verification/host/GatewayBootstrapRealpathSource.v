(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual successful suffix guard supplies realpath's original filename. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewaySourcePaths GatewayFramedRuntime
  GatewaySourceAutomation GatewayBootstrapABI GatewayBootstrapSource GatewayBootstrapFilename
  GatewayBootstrapInformation GatewayBootstrapValidationSource GatewayBootstrapLoadedCompare
  GatewayBootstrapCompareReturn GatewayBootstrapCopyEdges GatewayThreadRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition bootstrap_realpath_first := match bootstrap_realpath_sequence with
  Ssequence first _ => first | _ => Sskip end.
Definition bootstrap_realpath_guard := match bootstrap_realpath_sequence with
  Ssequence _ rest => rest | _ => Sskip end.
Definition bootstrap_realpath_call := match bootstrap_realpath_first with
  Ssequence _ rest => rest | _ => Sskip end.
Definition bootstrap_realpath_temporaries filename size temporaries :=
  PTree.set _t'16 filename
    (PTree.set _api_size (Vlong (Int64.repr (size - 30)))
      (bootstrap_compared_temporaries _t'7 _t'6 Int.zero
        (bootstrap_loaded_comparison_temporaries filename temporaries))).
Definition bootstrap_realpath_cont information resolved filename size temporaries :=
  Kcall (Some _t'8) f_host_bootstrap (bootstrap_environment information resolved)
    (bootstrap_realpath_temporaries filename size temporaries)
    (Kseq bootstrap_realpath_guard (Kseq bootstrap_after_realpath Kstop)).

Section RealpathSource.
Context {World Event} (backend : gateway_backend World Event) io native stable discipline thread_errno
  (runtime : gateway_thread_runtime backend io native stable discipline thread_errno).
Variable ge : Clight.genv.
Hypothesis LAYOUT : gateway_bootstrap_information_layout ge.
Variables (information resolved object symbol : block) (offset : ptrofs) (bytes : list Byte.int).
Let filename := Vptr object offset.
Variable property : mem -> World -> Prop.
Hypothesis CLOSED : gateway_ambient_closed backend property.
Hypothesis INFORMATION : forall memory world, property memory world ->
  gateway_bootstrap_filename_information native stable discipline information filename bytes memory world.

Theorem actual_bootstrap_comparison_to_realpath temporaries memory :
  Genv.find_symbol ge _realpath = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some (gateway_bootstrap_signature gateway_canonical_path_api) ->
  temporaries ! _size = Some (Vlong (Int64.repr (Z.of_nat (length bytes)))) ->
  temporaries ! _tail = Some (Vlong (Int64.repr 30)) ->
  30 < Z.of_nat (length bytes) <= 4095 ->
  gateway_source_path backend ge (gateway_bootstrap_signature gateway_canonical_path_api)
    [filename; Vptr resolved Ptrofs.zero]
    (bootstrap_realpath_cont information resolved filename (Z.of_nat (length bytes)) temporaries) property
    (Returnstate (Vint Int.zero)
      (bootstrap_loaded_comparison_cont information resolved filename temporaries) memory) property.
Proof.
  intros SYMBOL FUNCTION SIZE TAIL LENGTH.
  eapply gateway_bootstrap_comparison_success; [exact CLOSED |].
  gateway_source_structure CLOSED.
  repeat gateway_source_structure CLOSED.
  eapply gateway_source_same with (target := State f_host_bootstrap Sskip
    (Kseq bootstrap_after_api_size Kstop) (bootstrap_environment information resolved)
    (PTree.set _api_size (Vlong (Int64.repr (Z.of_nat (length bytes) - 30)))
      (bootstrap_compared_temporaries _t'7 _t'6 Int.zero
        (bootstrap_loaded_comparison_temporaries filename temporaries))) memory).
  - exact CLOSED.
  - cbn; tauto.
  - intros; apply certified_set_edge; eapply binary_expression_value with
      (v := Vlong (Int64.repr (Z.of_nat (length bytes)))) (w := Vlong (Int64.repr 30)).
    + apply old_expression_value, value_temp.
      unfold bootstrap_compared_temporaries, bootstrap_loaded_comparison_temporaries;
        repeat rewrite PTree.gso by discriminate; exact SIZE.
    + apply old_expression_value, value_temp.
      unfold bootstrap_compared_temporaries, bootstrap_loaded_comparison_temporaries;
        repeat rewrite PTree.gso by discriminate; exact TAIL.
    + change (Some (Vlong (Int64.sub (Int64.repr (Z.of_nat (length bytes))) (Int64.repr 30))) =
        Some (Vlong (Int64.repr (Z.of_nat (length bytes) - 30)))).
      unfold Int64.sub; rewrite !Int64.unsigned_repr by
        (change Int64.max_unsigned with 18446744073709551615; lia); reflexivity.
  - repeat gateway_source_structure CLOSED.
    eapply gateway_source_same with (target := State f_host_bootstrap Sskip
      (Kseq bootstrap_realpath_call (Kseq bootstrap_realpath_guard (Kseq bootstrap_after_realpath Kstop)))
      (bootstrap_environment information resolved)
      (bootstrap_realpath_temporaries filename (Z.of_nat (length bytes)) temporaries) memory).
    + exact CLOSED.
    + cbn; tauto.
    + intros before world GOOD; destruct (INFORMATION _ _ GOOD) as [[_ [_ LOAD]] _]; apply certified_set_edge, gateway_bootstrap_filename_value;
        [exact LAYOUT |exact LOAD].
    + repeat gateway_source_structure CLOSED.
      eapply gateway_source_same with (target := Callstate
        (gateway_bootstrap_signature gateway_canonical_path_api) [filename; Vptr resolved Ptrofs.zero]
        (bootstrap_realpath_cont information resolved filename (Z.of_nat (length bytes)) temporaries) memory).
      * exact CLOSED.
      * cbn; tauto.
      * intros; eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero).
        -- reflexivity.
        -- apply old_expression_value; eapply value_function;
             [reflexivity |exact SYMBOL |reflexivity].
        -- eapply cons_argument_values with (v := filename).
           ++ apply old_expression_value, value_temp, PTree.gss.
           ++ reflexivity.
           ++ eapply cons_argument_values with (v := Vptr resolved Ptrofs.zero).
              ** apply gateway_bootstrap_array_reference; reflexivity.
              ** reflexivity.
              ** apply no_argument_values.
        -- cbn; exact FUNCTION.
        -- reflexivity.
      * constructor; intros; assumption.
Qed.
End RealpathSource.
