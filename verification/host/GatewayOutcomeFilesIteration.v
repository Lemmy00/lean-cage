(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual iterator decisions lead to their real checks or private copy. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayOutcomeConstruction GatewayOutcomeCopySource
  GatewayOutcomeFilesSource GatewayOutcomeValidationSource GatewayOutcomeValidationPaths GatewayOutcomeValidationMetadata GatewaySourcePaths
  GatewaySourceSegmentAutomation GatewayFramedRuntime GatewayObjectAddresses GatewayFailurePaths GatewaySourceCuts GatewayValueReturns GatewayPrefix.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_validation_after_name :=
  match gateway_validation_files_checks with Ssequence _ rest => rest | _ => Sskip end.
Definition gateway_validation_data_guard :=
  match gateway_validation_after_name with Ssequence _ guard => guard | _ => Sskip end.
Definition gateway_validation_name_cont environment parameters :=
  Kcall (Some _t'16) f_host_outcome_from environment parameters
    (Kseq (Sset _name_type (Etempvar _t'16 tint))
      (Kseq gateway_validation_after_name gateway_validation_files_cont)).
Definition gateway_validation_bytes_cont environment parameters :=
  Kcall (Some _t'18) f_host_outcome_from environment parameters
    (Kseq (Sset _t'17 (Ecast (Etempvar _t'18 tint) tint))
      (Kseq (Sset _data_type (Etempvar _t'17 tint))
        (Kseq gateway_validation_data_guard gateway_validation_files_cont))).

Theorem gateway_validation_iterator_copy {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) environment parameters before data data_offset symbol definition :
  gateway_ambient_closed backend property -> parameters ! _data = Some (Vptr data data_offset) ->
  environment ! _PyDict_Copy = None ->
  Genv.find_symbol ge _PyDict_Copy = Some symbol -> Genv.find_funct_ptr ge symbol = Some definition ->
  type_of_fundef definition = Tfunction [tptr (Tstruct __object noattr)] (tptr (Tstruct __object noattr)) cc_default ->
  gateway_source_path backend ge definition [Vptr data data_offset]
    (gateway_outcome_copy_cont environment (set_opttemp (Some _t'15) (Vint Int.zero) parameters)) property
    (Returnstate (Vint Int.zero) (gateway_validation_next_cont environment parameters) before) property.
Proof.
  intros CLOSED DATA LOCAL SYMBOL FUNCTION TYPE.
  gateway_validation_source_call CLOSED ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
  eapply gateway_source_same with (target := Callstate definition [Vptr data data_offset]
    (gateway_outcome_copy_cont environment (set_opttemp (Some _t'15) (Vint Int.zero) parameters)) before).
  - exact CLOSED.
  - cbn; tauto.
  - intros; eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero).
    + reflexivity.
    + apply old_expression_value, value_function; [exact LOCAL |exact SYMBOL |reflexivity].
    + apply cons_argument_values with (v := Vptr data data_offset);
        [gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity) |reflexivity |apply no_argument_values].
    + change (Genv.find_funct_ptr ge symbol = Some definition); exact FUNCTION.
    + exact TYPE.
  - apply gateway_source_reached; auto.
Qed.

Theorem gateway_validation_bad_file_name {World Event} (backend : gateway_backend World Event) ge
    environment parameters before word : Int.signed word <= 0 ->
  gateway_failure_when backend ge (fun _ _ => True)
    (Returnstate (Vint word) (gateway_validation_name_cont environment parameters) before).
Proof.
  intro NONPOSITIVE.
  assert (CLOSED : gateway_ambient_closed backend (fun _ _ => True)) by (unfold gateway_ambient_closed; intros; exact I).
  assert (POINTER : gateway_pointer_return f_host_outcome_from) by (repeat eexists).
  gateway_validation_failure CLOSED ltac:(fun _ => fail)
    ltac:(fun _ => first [apply gateway_nonpositive_gt; exact NONPOSITIVE |
      apply gateway_nonpositive_le; exact NONPOSITIVE |reflexivity]) POINTER.
Qed.

Theorem gateway_validation_bad_file_bytes {World Event} (backend : gateway_backend World Event) ge
    environment parameters before word : Int.signed word <= 0 ->
  gateway_failure_when backend ge (fun _ _ => True)
    (Returnstate (Vint word) (gateway_validation_bytes_cont environment parameters) before).
Proof.
  intro NONPOSITIVE.
  assert (CLOSED : gateway_ambient_closed backend (fun _ _ => True)) by (unfold gateway_ambient_closed; intros; exact I).
  assert (POINTER : gateway_pointer_return f_host_outcome_from) by (repeat eexists).
  gateway_validation_failure CLOSED ltac:(fun _ => fail)
    ltac:(fun _ => first [apply gateway_nonpositive_le; exact NONPOSITIVE |reflexivity]) POINTER.
Qed.

Theorem gateway_validation_iterator_again {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) environment parameters before word files files_offset position key value symbol definition :
  gateway_ambient_closed backend property -> 0 < Int.signed word -> parameters ! _files = Some (Vptr files files_offset) ->
  environment ! _position = Some (position, tlong) ->
  environment ! _key = Some (key, tptr (Tstruct __object noattr)) ->
  environment ! _value__1 = Some (value, tptr (Tstruct __object noattr)) ->
  environment ! _PyDict_Next = None ->
  Genv.find_symbol ge _PyDict_Next = Some symbol -> Genv.find_funct_ptr ge symbol = Some definition ->
  type_of_fundef definition = Tfunction [tptr (Tstruct __object noattr); tptr tlong;
    tptr (tptr (Tstruct __object noattr)); tptr (tptr (Tstruct __object noattr))] tint cc_default ->
  exists selected, gateway_source_path backend ge definition
    [Vptr files files_offset; Vptr position Ptrofs.zero; Vptr key Ptrofs.zero; Vptr value Ptrofs.zero]
    (gateway_validation_next_cont environment selected) property
    (Returnstate (Vint word) (gateway_validation_bytes_cont environment parameters) before) property /\
    selected ! _files = parameters ! _files /\ selected ! _data = parameters ! _data.
Proof.
  intros CLOSED POSITIVE FILES POSITION KEY VALUE LOCAL SYMBOL FUNCTION TYPE; eexists; split.
  - gateway_validation_source_call CLOSED ltac:(fun _ => fail)
      ltac:(fun _ => first [apply gateway_validation_positive_le; exact POSITIVE |reflexivity]).
    eapply gateway_source_same with (target := Callstate definition
      [Vptr files files_offset; Vptr position Ptrofs.zero; Vptr key Ptrofs.zero; Vptr value Ptrofs.zero]
      (gateway_validation_next_cont environment _) before).
    + exact CLOSED.
    + cbn; tauto.
    + intros; eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero).
      * reflexivity.
      * apply old_expression_value, value_function; [exact LOCAL |exact SYMBOL |reflexivity].
      * apply cons_argument_values with (v := Vptr files files_offset).
        -- gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
        -- reflexivity.
        -- apply cons_argument_values with (v := Vptr position Ptrofs.zero).
           ++ apply GatewayPrefix.local_address_expression; exact POSITION.
           ++ reflexivity.
           ++ apply cons_argument_values with (v := Vptr key Ptrofs.zero).
              ** apply GatewayPrefix.local_address_expression; exact KEY.
              ** reflexivity.
              ** apply cons_argument_values with (v := Vptr value Ptrofs.zero);
                   [apply GatewayPrefix.local_address_expression; exact VALUE |reflexivity |apply no_argument_values].
      * change (Genv.find_funct_ptr ge symbol = Some definition); exact FUNCTION.
      * exact TYPE.
    + apply gateway_source_reached; auto.
  - split; unfold set_opttemp; repeat rewrite PTree.gso by discriminate; reflexivity.
Qed.

Theorem gateway_validation_iterator_name {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
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
    selected ! _t'32 = Some (Vptr name name_offset) /\ selected ! _files = parameters ! _files.
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
  - split; unfold set_opttemp; repeat rewrite PTree.gso by discriminate; first [reflexivity |apply PTree.gss].
Qed.

Theorem gateway_validation_iterator_bytes {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) environment parameters before word slot value value_offset bytes symbol :
  gateway_ambient_closed backend property -> 0 < Int.signed word ->
  environment ! _value__1 = Some (slot, tptr (Tstruct __object noattr)) ->
  (forall memory world, property memory world -> Mem.load Mptr memory slot 0 = Some (Vptr value value_offset)) ->
  environment ! _host_has_type = None -> environment ! _PyBytes_Type = None ->
  Genv.find_symbol ge _host_has_type = Some symbol -> Genv.find_funct_ptr ge symbol = Some (Internal f_host_has_type) ->
  Genv.find_symbol ge _PyBytes_Type = Some bytes ->
  exists selected, gateway_source_path backend ge (Internal f_host_has_type)
    [Vptr value value_offset; Vptr bytes Ptrofs.zero; Vint Int.zero]
    (gateway_validation_bytes_cont environment selected) property
    (Returnstate (Vint word) (gateway_validation_name_cont environment parameters) before) property /\
    selected ! _t'31 = Some (Vptr value value_offset) /\ selected ! _files = parameters ! _files.
Proof.
  intros CLOSED POSITIVE SLOT LOAD LOCAL TYPE_LOCAL SYMBOL FUNCTION BYTES; eexists; split.
  - gateway_validation_source_call CLOSED
      ltac:(fun _ => eapply location_read_value;
        [apply local_location_value; exact SLOT |eapply deref_loc_value;
          [reflexivity |eapply LOAD; eassumption]])
      ltac:(fun _ => first [eapply gateway_validation_positive_gt; exact POSITIVE |reflexivity]).
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
  - split; unfold set_opttemp; repeat rewrite PTree.gso by discriminate; first [reflexivity |apply PTree.gss].
Qed.
