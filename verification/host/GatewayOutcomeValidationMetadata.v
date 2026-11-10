(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual json validation precedes the required files lookup. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayOutcomeEntry GatewayOutcomeValidationSource
  GatewayOutcomeValidationPaths GatewayOutcomeLookupSource GatewaySourcePaths GatewaySourceSegmentAutomation
  GatewayFramedRuntime GatewayObjectAddresses GatewayValueReturns.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_validation_json_type_call :=
  match gateway_outcome_after_field_validation with
  | Ssequence (Sifthenelse _ (Ssequence (Ssequence _ call) _) _) _ => call | _ => Sskip end.
Definition gateway_validation_json_lookup_cont environment parameters :=
  Kcall (Some _t'11) f_host_outcome_from environment parameters
    (Kseq gateway_validation_json_type_call
      (Kseq (Sset _valid (Etempvar _t'12 tint)) (Kseq gateway_outcome_after_json_validation Kstop))).

Lemma gateway_validation_positive_le (ge : Clight.genv) memory word :
  0 < Int.signed word ->
  sem_binary_operation ge Ole (Vint word) tint (Vint Int.zero) tint memory = Some (Vint Int.zero).
Proof.
  intro POSITIVE; change (Some (Val.of_bool (negb (Int.lt Int.zero word))) = Some (Vint Int.zero)).
  assert (LESS : Int.lt Int.zero word = true).
  { unfold Int.lt; change ((if zlt 0 (Int.signed word) then true else false) = true).
    destruct zlt; [reflexivity |lia]. }
  rewrite LESS; reflexivity.
Qed.

Theorem gateway_validation_exhausted_json {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) environment parameters before word data data_offset name symbol definition :
  gateway_ambient_closed backend property -> parameters ! _valid = Some (Vint word) -> 0 < Int.signed word ->
  parameters ! _index = Some (Vint (Int.repr 14)) -> parameters ! _data = Some (Vptr data data_offset) ->
  environment ! _PyDict_GetItemString = None -> environment ! ___stringlit_51 = None ->
  Genv.find_symbol ge _PyDict_GetItemString = Some symbol -> Genv.find_funct_ptr ge symbol = Some definition ->
  Genv.find_symbol ge ___stringlit_51 = Some name ->
  type_of_fundef definition = Tfunction [tptr (Tstruct __object noattr); tptr tschar] (tptr (Tstruct __object noattr)) cc_default ->
  exists selected, gateway_source_path backend ge definition [Vptr data data_offset; Vptr name Ptrofs.zero]
    (gateway_validation_json_lookup_cont environment selected) property
    (State f_host_outcome_from gateway_outcome_validation_loop_body gateway_validation_iteration_cont environment parameters before) property /\
    selected ! _data = parameters ! _data /\ selected ! _valid = parameters ! _valid.
Proof.
  intros CLOSED VALID POSITIVE INDEX DATA LOCAL NAME_LOCAL SYMBOL FUNCTION NAME TYPE; eexists; split.
  - gateway_validation_source_call CLOSED ltac:(fun _ => fail)
      ltac:(fun _ => first [eapply gateway_validation_positive_gt; exact POSITIVE |reflexivity]).
    eapply gateway_source_same with (target := Callstate definition [Vptr data data_offset; Vptr name Ptrofs.zero]
      (gateway_validation_json_lookup_cont environment _) before).
    + exact CLOSED.
    + cbn; tauto.
    + intros; eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero).
      * reflexivity.
      * apply old_expression_value, value_function; [exact LOCAL |exact SYMBOL |reflexivity].
      * apply cons_argument_values with (v := Vptr data data_offset).
        -- gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
        -- reflexivity.
        -- apply cons_argument_values with (v := Vptr name Ptrofs.zero);
             [apply old_expression_value, value_function; [exact NAME_LOCAL |exact NAME |reflexivity] |
              reflexivity |apply no_argument_values].
      * change (Genv.find_funct_ptr ge symbol = Some definition); exact FUNCTION.
      * exact TYPE.
    + apply gateway_source_reached; auto.
  - split; repeat rewrite PTree.gso by discriminate; reflexivity.
Qed.

Ltac gateway_validation_two_arguments data name :=
  apply cons_argument_values with (v := data);
    [gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity) |reflexivity |
     apply cons_argument_values with (v := Vptr name Ptrofs.zero);
       [apply old_expression_value, value_function; [assumption |assumption |reflexivity] |
        reflexivity |apply no_argument_values]].

Theorem gateway_validation_json_getter {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) environment parameters before word data data_offset name symbol definition :
  gateway_ambient_closed backend property -> parameters ! _valid = Some (Vint word) -> 0 < Int.signed word ->
  parameters ! _data = Some (Vptr data data_offset) ->
  environment ! _PyDict_GetItemString = None -> environment ! ___stringlit_51 = None ->
  Genv.find_symbol ge _PyDict_GetItemString = Some symbol -> Genv.find_funct_ptr ge symbol = Some definition ->
  Genv.find_symbol ge ___stringlit_51 = Some name ->
  type_of_fundef definition = Tfunction [tptr (Tstruct __object noattr); tptr tschar] (tptr (Tstruct __object noattr)) cc_default ->
  exists selected, gateway_source_path backend ge definition [Vptr data data_offset; Vptr name Ptrofs.zero]
    (gateway_validation_json_lookup_cont environment selected) property
    (State f_host_outcome_from gateway_outcome_after_field_validation Kstop environment parameters before) property /\
    selected ! _data = parameters ! _data /\ selected ! _valid = parameters ! _valid.
Proof.
  intros CLOSED VALID POSITIVE DATA LOCAL NAME_LOCAL SYMBOL FUNCTION NAME TYPE; eexists; split.
  - gateway_validation_source_call CLOSED ltac:(fun _ => fail)
      ltac:(fun _ => first [eapply gateway_validation_positive_gt; exact POSITIVE |reflexivity]).
    eapply gateway_source_same with (target := Callstate definition [Vptr data data_offset; Vptr name Ptrofs.zero]
      (gateway_validation_json_lookup_cont environment _) before).
    + exact CLOSED.
    + cbn; tauto.
    + intros; eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero).
      * reflexivity.
      * apply old_expression_value, value_function; [exact LOCAL |exact SYMBOL |reflexivity].
      * gateway_validation_two_arguments (Vptr data data_offset) name.
      * change (Genv.find_funct_ptr ge symbol = Some definition); exact FUNCTION.
      * exact TYPE.
    + apply gateway_source_reached; auto.
  - split; repeat rewrite PTree.gso by discriminate; reflexivity.
Qed.

Theorem gateway_validation_json_type {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) environment parameters before value dictionary symbol :
  gateway_ambient_closed backend property -> gateway_object_pointer_value value ->
  environment ! _host_has_type = None -> environment ! _PyDict_Type = None ->
  Genv.find_symbol ge _host_has_type = Some symbol -> Genv.find_funct_ptr ge symbol = Some (Internal f_host_has_type) ->
  Genv.find_symbol ge _PyDict_Type = Some dictionary ->
  gateway_source_path backend ge (Internal f_host_has_type) [value; Vptr dictionary Ptrofs.zero; Vint Int.zero]
    (gateway_outcome_json_type_cont environment (set_opttemp (Some _t'11) value parameters)) property
    (Returnstate value (gateway_validation_json_lookup_cont environment parameters) before) property.
Proof.
  intros CLOSED POINTER LOCAL TYPE_LOCAL SYMBOL FUNCTION DICTIONARY.
  assert (CAST : forall memory, sem_cast value (tptr (Tstruct __object noattr))
    (tptr (Tstruct __object noattr)) memory = Some value).
  { intro memory; destruct POINTER as [NULL |[object [offset SAME]]]; subst value; reflexivity. }
  gateway_validation_source_call CLOSED ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
  eapply gateway_source_same with (target := Callstate (Internal f_host_has_type)
    [value; Vptr dictionary Ptrofs.zero; Vint Int.zero]
    (gateway_outcome_json_type_cont environment (set_opttemp (Some _t'11) value parameters)) before).
  - exact CLOSED.
  - cbn; tauto.
  - intros; eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero).
    + reflexivity.
    + apply old_expression_value, value_function; [exact LOCAL |exact SYMBOL |reflexivity].
    + apply cons_argument_values with (v := value).
      * gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
      * apply CAST.
      * apply cons_argument_values with (v := Vptr dictionary Ptrofs.zero).
        -- apply gateway_global_address_expression; assumption.
        -- reflexivity.
        -- apply cons_argument_values with (v := Vint Int.zero);
             [apply old_expression_value; constructor |reflexivity |apply no_argument_values].
    + change (Genv.find_funct_ptr ge symbol = Some (Internal f_host_has_type)); exact FUNCTION.
    + reflexivity.
  - apply gateway_source_reached; auto.
Qed.

Theorem gateway_validation_files_getter {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) environment parameters before word data data_offset name symbol definition :
  gateway_ambient_closed backend property -> 0 < Int.signed word ->
  parameters ! _data = Some (Vptr data data_offset) ->
  environment ! _PyDict_GetItemString = None -> environment ! ___stringlit_41 = None ->
  Genv.find_symbol ge _PyDict_GetItemString = Some symbol -> Genv.find_funct_ptr ge symbol = Some definition ->
  Genv.find_symbol ge ___stringlit_41 = Some name ->
  type_of_fundef definition = Tfunction [tptr (Tstruct __object noattr); tptr tschar] (tptr (Tstruct __object noattr)) cc_default ->
  exists selected, gateway_source_path backend ge definition [Vptr data data_offset; Vptr name Ptrofs.zero]
    (gateway_outcome_files_lookup_cont environment selected) property
    (Returnstate (Vint word) (gateway_outcome_json_type_cont environment parameters) before) property /\
    selected ! _data = parameters ! _data /\ selected ! _valid = Some (Vint word).
Proof.
  intros CLOSED POSITIVE DATA LOCAL NAME_LOCAL SYMBOL FUNCTION NAME TYPE; eexists; split.
  - gateway_validation_source_call CLOSED ltac:(fun _ => fail)
      ltac:(fun _ => first [eapply gateway_validation_positive_le; exact POSITIVE |reflexivity]).
    eapply gateway_source_same with (target := Callstate definition [Vptr data data_offset; Vptr name Ptrofs.zero]
      (gateway_outcome_files_lookup_cont environment _) before).
    + exact CLOSED.
    + cbn; tauto.
    + intros; eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero).
      * reflexivity.
      * apply old_expression_value, value_function; [exact LOCAL |exact SYMBOL |reflexivity].
      * gateway_validation_two_arguments (Vptr data data_offset) name.
      * change (Genv.find_funct_ptr ge symbol = Some definition); exact FUNCTION.
      * exact TYPE.
    + apply gateway_source_reached; auto.
  - split; unfold set_opttemp; repeat rewrite PTree.gso by discriminate; first [reflexivity |apply PTree.gss].
Qed.
