(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Realpath's actual successful buffer supplies the next bounded-length call. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewaySourcePaths GatewaySourceAutomation
  GatewayFramedRuntime GatewayBootstrapABI GatewayBootstrapSource GatewayBootstrapRetention
  GatewayBootstrapRealpathSource GatewayBootstrapCanonicalResult GatewayBootstrapCanonicalAmbient
  GatewayBootstrapValidationSource GatewayBootstrapLengthBindings GatewayBootstrapCopyEdges GatewayThreadRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition bootstrap_canonical_length_call := match bootstrap_canonical_length_sequence with
  Ssequence first _ => first | _ => Sskip end.
Definition bootstrap_canonical_length_bind := match bootstrap_canonical_length_sequence with
  Ssequence _ rest => rest | _ => Sskip end.
Definition bootstrap_canonical_return_temporaries resolved filename loaded_size temporaries :=
  PTree.set _t'8 (Vptr resolved Ptrofs.zero)
    (bootstrap_realpath_temporaries filename loaded_size temporaries).
Definition bootstrap_canonical_length_cont information resolved filename loaded_size temporaries :=
  Kcall (Some _t'9) f_host_bootstrap (bootstrap_environment information resolved)
    (bootstrap_canonical_return_temporaries resolved filename loaded_size temporaries)
    (Kseq bootstrap_canonical_length_bind (Kseq bootstrap_after_canonical_length Kstop)).

Theorem actual_bootstrap_canonical_to_length {World Event} (backend : gateway_backend World Event)
    io native stable discipline thread_errno
    (runtime : gateway_thread_runtime backend io native stable discipline thread_errno)
    (ge : Clight.genv) information resolved object offset original canonical symbol loaded_size temporaries memory (property : mem -> World -> Prop) :
  gateway_ambient_closed backend property ->
  (forall memory world, property memory world ->
    gateway_bootstrap_canonical_information native stable discipline
      information object offset original resolved canonical memory world) ->
  Genv.find_symbol ge _strnlen = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some (gateway_bootstrap_signature gateway_bounded_length_api) ->
  gateway_source_path backend ge (gateway_bootstrap_signature gateway_bounded_length_api)
    [Vptr resolved Ptrofs.zero; Vlong (Int64.repr 4096)]
    (bootstrap_canonical_length_cont information resolved (Vptr object offset) loaded_size temporaries)
    property
    (Returnstate (Vptr resolved Ptrofs.zero)
      (bootstrap_realpath_cont information resolved (Vptr object offset) loaded_size temporaries) memory)
    property.
Proof.
  intros CLOSED INFORMATION SYMBOL FUNCTION.
  unfold bootstrap_realpath_cont.
  repeat gateway_source_structure CLOSED.
  eapply gateway_source_same with (target := State f_host_bootstrap Sskip
    (Kseq bootstrap_after_realpath Kstop) (bootstrap_environment information resolved)
    (bootstrap_canonical_return_temporaries resolved (Vptr object offset) loaded_size temporaries) memory).
  - exact CLOSED.
  - cbn; tauto.
  - intros before world GOOD; destruct (INFORMATION _ _ GOOD) as [_ [_ [_ [STRING _]]]];
      apply certified_if_edge with (v := Vint Int.zero) (b := false).
    + apply old_expression_value; eapply value_unary with (v := Vptr resolved Ptrofs.zero).
      * apply value_temp, PTree.gss.
      * pose proof (gateway_bootstrap_cstring_pointer before resolved Ptrofs.zero canonical STRING) as LIVE.
        change (option_map (fun b : bool => Val.of_bool (negb b))
          (if Mem.weak_valid_pointer before resolved 0 then Some true else None) = Some (Vint Int.zero)).
        change (Mem.weak_valid_pointer before resolved 0 = true) in LIVE.
        rewrite LIVE; reflexivity.
    + reflexivity.
  - repeat gateway_source_structure CLOSED.
    eapply gateway_source_same with (target := Callstate
      (gateway_bootstrap_signature gateway_bounded_length_api)
      [Vptr resolved Ptrofs.zero; Vlong (Int64.repr 4096)]
      (bootstrap_canonical_length_cont information resolved (Vptr object offset) loaded_size temporaries) memory).
    + exact CLOSED.
    + cbn; tauto.
    + intros; eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero).
      * reflexivity.
      * apply old_expression_value; eapply value_function;
          [reflexivity |exact SYMBOL |reflexivity].
      * eapply cons_argument_values with (v := Vptr resolved Ptrofs.zero).
        -- apply gateway_bootstrap_array_reference; reflexivity.
        -- reflexivity.
        -- eapply cons_argument_values with (v := Vlong (Int64.repr 4096)).
           ++ apply gateway_bootstrap_sizeof_expression.
           ++ reflexivity.
           ++ apply no_argument_values.
      * cbn; exact FUNCTION.
      * reflexivity.
    + constructor; intros; assumption.
Qed.
