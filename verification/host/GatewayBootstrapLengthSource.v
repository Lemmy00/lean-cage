(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A successful loader result supplies the actual bounded length call. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayBootstrapSource GatewayBootstrapABI GatewayBootstrapFilename
  GatewayBootstrapInformation GatewayBootstrapRetention GatewayMachine GatewayThreadRuntime GatewayFramedRuntime GatewaySourcePaths.
Import ListNotations.
Open Scope Z_scope.

Definition bootstrap_length_sequence := match bootstrap_after_first with Ssequence first _ => first | _ => Sskip end.
Definition bootstrap_after_length := match bootstrap_after_first with Ssequence _ rest => rest | _ => Sskip end.
Definition bootstrap_length_first := match bootstrap_length_sequence with Ssequence first _ => first | _ => Sskip end.
Definition bootstrap_length_bind_size := match bootstrap_length_sequence with Ssequence _ rest => rest | _ => Sskip end.
Definition bootstrap_length_load := match bootstrap_length_first with Ssequence first _ => first | _ => Sskip end.
Definition bootstrap_length_call := match bootstrap_length_first with Ssequence _ rest => rest | _ => Sskip end.
Definition bootstrap_loader_nonzero := match bootstrap_loader_bind with Sifthenelse _ _ selected => selected | _ => Sskip end.
Definition bootstrap_loader_name_load := match bootstrap_loader_nonzero with Ssequence first _ => first | _ => Sskip end.
Definition bootstrap_loader_name_test := match bootstrap_loader_nonzero with Ssequence _ rest => rest | _ => Sskip end.
Definition bootstrap_length_cont information resolved temporaries :=
  Kcall (Some _t'3) f_host_bootstrap (bootstrap_environment information resolved) temporaries
    (Kseq bootstrap_length_bind_size (Kseq bootstrap_after_length Kstop)).

Section LengthPrefix.
Context {World Event} (backend : gateway_backend World Event) io native stable discipline thread_errno
  (runtime : gateway_thread_runtime backend io native stable discipline thread_errno).
Variable ge : Clight.genv.
Hypothesis LAYOUT : gateway_bootstrap_information_layout ge.
Variables (information resolved filename_block : block) (filename_offset : ptrofs) (status : int).
Variable bytes : list Byte.int.
Let filename := Vptr filename_block filename_offset.
Variable property : mem -> World -> Prop.
Hypothesis CLOSED : gateway_ambient_closed backend property.
Hypothesis INFORMATION : forall memory world, property memory world ->
  gateway_bootstrap_filename_information native stable discipline information filename bytes memory world.
Let after_status := PTree.set _t'1 (Vint status) bootstrap_temporaries.
Let after_name := PTree.set _t'21 filename after_status.
Let after_check := PTree.set _t'2 (Vint Int.zero) after_name.
Let after_load := PTree.set _t'20 filename after_check.

Theorem actual_bootstrap_loader_to_length memory symbol :
  status <> Int.zero ->
  Genv.find_symbol ge _strnlen = Some symbol ->
  Genv.find_funct_ptr ge symbol =
    Some (gateway_bootstrap_signature gateway_bounded_length_api) ->
  gateway_source_path backend ge
    (gateway_bootstrap_signature gateway_bounded_length_api) [filename; Vlong (Int64.repr 4096)]
    (bootstrap_length_cont information resolved after_load) property
    (Returnstate (Vint status) (bootstrap_loader_cont information resolved) memory) property.
Proof.
  intros NONZERO SYMBOL FUNCTION.
  eapply gateway_source_same with (target := State f_host_bootstrap Sskip
    (Kseq bootstrap_loader_bind (Kseq bootstrap_loader_test (Kseq bootstrap_after_first Kstop)))
    (bootstrap_environment information resolved) after_status memory);
    [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_returnstate |].
  eapply gateway_source_same with (target := State f_host_bootstrap bootstrap_loader_bind
    (Kseq bootstrap_loader_test (Kseq bootstrap_after_first Kstop))
    (bootstrap_environment information resolved) after_status memory);
    [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_skip_seq |].
  eapply gateway_source_same with (target := State f_host_bootstrap bootstrap_loader_nonzero
    (Kseq bootstrap_loader_test (Kseq bootstrap_after_first Kstop))
    (bootstrap_environment information resolved) after_status memory).
  - exact CLOSED.
  - cbn; tauto.
  - intros before world GOOD; apply certified_if_edge with (v := Vint Int.zero) (b := false).
    + apply old_expression_value; eapply value_unary.
      * apply value_temp, PTree.gss.
      * cbn; rewrite (Int.eq_false status Int.zero NONZERO); reflexivity.
    + reflexivity.
  - eapply gateway_source_same with (target := State f_host_bootstrap bootstrap_loader_name_load
      (Kseq bootstrap_loader_name_test (Kseq bootstrap_loader_test (Kseq bootstrap_after_first Kstop)))
      (bootstrap_environment information resolved) after_status memory);
      [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_seq |].
    eapply gateway_source_same with (target := State f_host_bootstrap Sskip
      (Kseq bootstrap_loader_name_test (Kseq bootstrap_loader_test (Kseq bootstrap_after_first Kstop)))
      (bootstrap_environment information resolved) after_name memory).
    + exact CLOSED.
    + cbn; tauto.
    + intros before world GOOD; destruct (INFORMATION _ _ GOOD) as [[_ [_ LOAD]] _]; apply certified_set_edge, gateway_bootstrap_filename_value;
        [exact LAYOUT |exact LOAD].
    + eapply gateway_source_same with (target := State f_host_bootstrap bootstrap_loader_name_test
        (Kseq bootstrap_loader_test (Kseq bootstrap_after_first Kstop))
        (bootstrap_environment information resolved) after_name memory);
        [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_skip_seq |].
      eapply gateway_source_same with (target := State f_host_bootstrap Sskip
        (Kseq bootstrap_loader_test (Kseq bootstrap_after_first Kstop))
        (bootstrap_environment information resolved) after_check memory).
      * exact CLOSED.
      * cbn; tauto.
      * intros before world GOOD; destruct (INFORMATION _ _ GOOD) as [_ [STRING PROTECTED]]; apply certified_set_edge;
          eapply cast_expression_value with (v := Vint Int.zero).
        -- apply old_expression_value; eapply value_unary with (v := filename).
           ++ apply value_temp, PTree.gss.
           ++ pose proof (gateway_bootstrap_cstring_pointer before filename_block filename_offset bytes STRING) as LIVE.
              change (option_map (fun b : bool => Val.of_bool (negb b))
                (if Mem.weak_valid_pointer before filename_block (Ptrofs.unsigned filename_offset)
                 then Some true else None) = Some (Vint Int.zero)).
              rewrite LIVE; reflexivity.
        -- reflexivity.
      * eapply gateway_source_same with (target := State f_host_bootstrap bootstrap_loader_test
          (Kseq bootstrap_after_first Kstop) (bootstrap_environment information resolved) after_check memory);
          [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_skip_seq |].
        eapply gateway_source_same with (target := State f_host_bootstrap Sskip (Kseq bootstrap_after_first Kstop)
          (bootstrap_environment information resolved) after_check memory).
        -- exact CLOSED.
        -- cbn; tauto.
        -- intros; apply certified_if_edge with (v := Vint Int.zero) (b := false);
             [apply old_expression_value, value_temp, PTree.gss |reflexivity].
        -- eapply gateway_source_same with (target := State f_host_bootstrap bootstrap_after_first Kstop
            (bootstrap_environment information resolved) after_check memory);
            [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_skip_seq |].
           eapply gateway_source_same with (target := State f_host_bootstrap bootstrap_length_sequence
             (Kseq bootstrap_after_length Kstop) (bootstrap_environment information resolved) after_check memory);
             [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_seq |].
           eapply gateway_source_same with (target := State f_host_bootstrap bootstrap_length_first
             (Kseq bootstrap_length_bind_size (Kseq bootstrap_after_length Kstop))
             (bootstrap_environment information resolved) after_check memory);
             [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_seq |].
           eapply gateway_source_same with (target := State f_host_bootstrap bootstrap_length_load
             (Kseq bootstrap_length_call (Kseq bootstrap_length_bind_size (Kseq bootstrap_after_length Kstop)))
             (bootstrap_environment information resolved) after_check memory);
             [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_seq |].
           eapply gateway_source_same with (target := State f_host_bootstrap Sskip
             (Kseq bootstrap_length_call (Kseq bootstrap_length_bind_size (Kseq bootstrap_after_length Kstop)))
             (bootstrap_environment information resolved) after_load memory).
           ++ exact CLOSED.
           ++ cbn; tauto.
           ++ intros before world GOOD; destruct (INFORMATION _ _ GOOD) as [[_ [_ LOAD]] _]; apply certified_set_edge, gateway_bootstrap_filename_value;
                [exact LAYOUT |exact LOAD].
           ++ eapply gateway_source_same with (target := State f_host_bootstrap bootstrap_length_call
               (Kseq bootstrap_length_bind_size (Kseq bootstrap_after_length Kstop))
               (bootstrap_environment information resolved) after_load memory);
               [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_skip_seq |].
              eapply gateway_source_same with (target := Callstate (gateway_bootstrap_signature gateway_bounded_length_api)
                [filename; Vlong (Int64.repr 4096)] (bootstrap_length_cont information resolved after_load) memory).
              ** exact CLOSED.
              ** cbn; tauto.
              ** intros before world GOOD; eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero).
                 --- reflexivity.
                 --- apply old_expression_value; eapply value_function; [reflexivity |exact SYMBOL |reflexivity].
                 --- eapply cons_argument_values with (v := filename).
                     +++ apply old_expression_value, value_temp, PTree.gss.
                     +++ reflexivity.
                     +++ eapply cons_argument_values with (v := Vint (Int.repr 4096)).
                         *** apply old_expression_value; eapply value_binary; [constructor |constructor |reflexivity].
                         *** reflexivity.
                         *** apply no_argument_values.
                 --- cbn; exact FUNCTION.
                 --- reflexivity.
              ** constructor; intros; assumption.
Qed.
End LengthPrefix.
