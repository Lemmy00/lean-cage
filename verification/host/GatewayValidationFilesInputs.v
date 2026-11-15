(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual file checks retain both the original data and its files dictionary. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayOutcomeFilesSource GatewayOutcomeFilesIteration
  GatewayOutcomeValidationPaths GatewaySourcePaths GatewaySourceSegmentAutomation GatewayFramedRuntime GatewayObjectAddresses.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_validation_file_name_inputs {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) environment parameters before key name name_offset unicode symbol :
  gateway_ambient_closed backend property ->
  environment ! _key = Some (key, tptr (Tstruct __object noattr)) ->
  (forall memory world, property memory world -> Mem.load Mptr memory key 0 = Some (Vptr name name_offset)) ->
  environment ! _host_has_type = None -> environment ! _PyUnicode_Type = None ->
  Genv.find_symbol ge _host_has_type = Some symbol -> Genv.find_funct_ptr ge symbol = Some (Internal f_host_has_type) ->
  Genv.find_symbol ge _PyUnicode_Type = Some unicode ->
  exists selected, gateway_source_path backend ge (Internal f_host_has_type)
    [Vptr name name_offset; Vptr unicode Ptrofs.zero; Vint Int.zero]
    (gateway_validation_name_cont environment selected) property
    (Returnstate (Vint Int.one) (gateway_validation_next_cont environment parameters) before) property /\
    selected ! _files = parameters ! _files /\ selected ! _data = parameters ! _data.
Proof.
  intros CLOSED KEY LOAD LOCAL TYPE_LOCAL SYMBOL FUNCTION UNICODE; eexists; split.
  - gateway_validation_source_call CLOSED
      ltac:(fun _ => eapply location_read_value;
        [apply local_location_value; exact KEY |eapply deref_loc_value;
          [reflexivity |eapply LOAD; eassumption]]) ltac:(fun _ => reflexivity).
    eapply gateway_source_same with (target := Callstate (Internal f_host_has_type)
      [Vptr name name_offset; Vptr unicode Ptrofs.zero; Vint Int.zero]
      (gateway_validation_name_cont environment _) before).
    + exact CLOSED.
    + cbn; tauto.
    + intros; eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero).
      * reflexivity.
      * apply old_expression_value, value_function; [exact LOCAL |exact SYMBOL |reflexivity].
      * apply cons_argument_values with (v := Vptr name name_offset).
        -- gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
        -- reflexivity.
        -- apply cons_argument_values with (v := Vptr unicode Ptrofs.zero).
           ++ apply gateway_global_address_expression; assumption.
           ++ reflexivity.
           ++ apply cons_argument_values with (v := Vint Int.zero);
                [apply old_expression_value; constructor |reflexivity |apply no_argument_values].
      * change (Genv.find_funct_ptr ge symbol = Some (Internal f_host_has_type)); exact FUNCTION.
      * reflexivity.
    + apply gateway_source_reached; auto.
  - split; unfold set_opttemp; repeat rewrite PTree.gso by discriminate; reflexivity.
Qed.

Theorem gateway_validation_file_bytes_inputs {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) environment parameters before slot value value_offset bytes symbol :
  gateway_ambient_closed backend property ->
  environment ! _value__1 = Some (slot, tptr (Tstruct __object noattr)) ->
  (forall memory world, property memory world -> Mem.load Mptr memory slot 0 = Some (Vptr value value_offset)) ->
  environment ! _host_has_type = None -> environment ! _PyBytes_Type = None ->
  Genv.find_symbol ge _host_has_type = Some symbol -> Genv.find_funct_ptr ge symbol = Some (Internal f_host_has_type) ->
  Genv.find_symbol ge _PyBytes_Type = Some bytes ->
  exists selected, gateway_source_path backend ge (Internal f_host_has_type)
    [Vptr value value_offset; Vptr bytes Ptrofs.zero; Vint Int.zero]
    (gateway_validation_bytes_cont environment selected) property
    (Returnstate (Vint Int.one) (gateway_validation_name_cont environment parameters) before) property /\
    selected ! _files = parameters ! _files /\ selected ! _data = parameters ! _data.
Proof.
  intros CLOSED SLOT LOAD LOCAL TYPE_LOCAL SYMBOL FUNCTION BYTES; eexists; split.
  - gateway_validation_source_call CLOSED
      ltac:(fun _ => eapply location_read_value;
        [apply local_location_value; exact SLOT |eapply deref_loc_value;
          [reflexivity |eapply LOAD; eassumption]])
      ltac:(fun _ => first [apply gateway_validation_positive_gt; change (0 < 1); lia |reflexivity]).
    eapply gateway_source_same with (target := Callstate (Internal f_host_has_type)
      [Vptr value value_offset; Vptr bytes Ptrofs.zero; Vint Int.zero]
      (gateway_validation_bytes_cont environment _) before).
    + exact CLOSED.
    + cbn; tauto.
    + intros; eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero).
      * reflexivity.
      * apply old_expression_value, value_function; [exact LOCAL |exact SYMBOL |reflexivity].
      * apply cons_argument_values with (v := Vptr value value_offset).
        -- gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
        -- reflexivity.
        -- apply cons_argument_values with (v := Vptr bytes Ptrofs.zero).
           ++ apply gateway_global_address_expression; assumption.
           ++ reflexivity.
           ++ apply cons_argument_values with (v := Vint Int.zero);
                [apply old_expression_value; constructor |reflexivity |apply no_argument_values].
      * change (Genv.find_funct_ptr ge symbol = Some (Internal f_host_has_type)); exact FUNCTION.
      * reflexivity.
    + apply gateway_source_reached; auto.
  - split; unfold set_opttemp; repeat rewrite PTree.gso by discriminate; reflexivity.
Qed.
