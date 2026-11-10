(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The real files iterator receives the actual allocated local slots. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayOutcomeConstruction GatewayOutcomeEntry
  GatewayOutcomeLookupSource GatewayOutcomeValidationSource GatewayOutcomeValidationPaths
  GatewaySourceSegments GatewaySourcePaths GatewaySourceSegmentAutomation GatewayFramedRuntime GatewayUnaryExpressions GatewayPrefix.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_validation_position_statement :=
  match gateway_outcome_right_suffix 6 (fn_body f_host_outcome_from) with Ssequence first _ => first | _ => Sskip end.
Definition gateway_validation_after_position := gateway_outcome_right_suffix 7 (fn_body f_host_outcome_from).
Definition gateway_validation_files_loop :=
  match gateway_validation_after_position with Ssequence loop _ => loop | _ => Sskip end.
Definition gateway_validation_files_body :=
  match gateway_validation_files_loop with Sloop body _ => body | _ => Sskip end.
Definition gateway_validation_after_files := gateway_outcome_right_suffix 8 (fn_body f_host_outcome_from).
Definition gateway_validation_files_cont := Kloop1 gateway_validation_files_body Sskip (Kseq gateway_validation_after_files Kstop).
Definition gateway_validation_files_checks :=
  match gateway_validation_files_body with Ssequence _ rest => rest | _ => Sskip end.
Definition gateway_validation_next_cont environment parameters :=
  Kcall (Some _t'15) f_host_outcome_from environment parameters
    (Kseq (Sifthenelse (Etempvar _t'15 tint) Sskip Sbreak)
      (Kseq gateway_validation_files_checks gateway_validation_files_cont)).

Lemma gateway_validation_live_not memory object offset :
  Mem.weak_valid_pointer memory object (Ptrofs.unsigned offset) = true ->
  sem_unary_operation Onotbool (Vptr object offset) (tptr (Tstruct __object noattr)) memory = Some (Vint Int.zero).
Proof.
  intro LIVE; change (option_map (fun flag => Val.of_bool (negb flag))
    (if Mem.weak_valid_pointer memory object (Ptrofs.unsigned offset) then Some true else None) = Some (Vint Int.zero)).
  rewrite LIVE; reflexivity.
Qed.

Theorem gateway_validation_files_position {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) environment parameters before files files_offset :
  gateway_ambient_closed backend property ->
  (forall memory world, property memory world -> Mem.weak_valid_pointer memory files (Ptrofs.unsigned files_offset) = true) ->
  gateway_source_segment backend ge property
    (Returnstate (Vptr files files_offset) (gateway_outcome_files_lookup_cont environment parameters) before)
    (State f_host_outcome_from gateway_validation_position_statement (Kseq gateway_validation_after_position Kstop)
      environment (PTree.set _files (Vptr files files_offset)
        (set_opttemp (Some _t'14) (Vptr files files_offset) parameters)) before) property.
Proof.
  intros CLOSED LIVE.
  gateway_segment_dynamic CLOSED
    ltac:(fun _ => eapply gateway_unary_expression_value with (value := Vptr files files_offset) (result := Vint Int.zero);
      [gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity) |
       apply gateway_validation_live_not; eapply LIVE; eassumption]) ltac:(fun _ => reflexivity).
Qed.

Theorem gateway_validation_position_store ge environment parameters before after position :
  environment ! _position = Some (position, tlong) ->
  Mem.store Mint64 before position 0 (Vlong Int64.zero) = Some after ->
  store_edge ge
    (State f_host_outcome_from gateway_validation_position_statement (Kseq gateway_validation_after_position Kstop)
      environment parameters before)
    (State f_host_outcome_from Sskip (Kseq gateway_validation_after_position Kstop) environment parameters after).
Proof.
  intros POSITION STORE.
  eapply assignment_source_edge with (b := position) (ofs := Ptrofs.zero) (v := Vint Int.zero) (w := Vlong Int64.zero).
  - apply local_location_value; exact POSITION.
  - apply old_expression_value; constructor.
  - reflexivity.
  - eapply assign_loc_value; [reflexivity |exact STORE].
Qed.

Theorem gateway_validation_next_source {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) environment parameters before files files_offset position key value symbol definition :
  gateway_ambient_closed backend property -> parameters ! _files = Some (Vptr files files_offset) ->
  environment ! _position = Some (position, tlong) ->
  environment ! _key = Some (key, tptr (Tstruct __object noattr)) ->
  environment ! _value__1 = Some (value, tptr (Tstruct __object noattr)) ->
  environment ! _PyDict_Next = None ->
  Genv.find_symbol ge _PyDict_Next = Some symbol -> Genv.find_funct_ptr ge symbol = Some definition ->
  type_of_fundef definition = Tfunction [tptr (Tstruct __object noattr); tptr tlong;
    tptr (tptr (Tstruct __object noattr)); tptr (tptr (Tstruct __object noattr))] tint cc_default ->
  gateway_source_path backend ge definition
    [Vptr files files_offset; Vptr position Ptrofs.zero; Vptr key Ptrofs.zero; Vptr value Ptrofs.zero]
    (gateway_validation_next_cont environment parameters) property
    (State f_host_outcome_from Sskip (Kseq gateway_validation_after_position Kstop) environment parameters before) property.
Proof.
  intros CLOSED FILES POSITION KEY VALUE LOCAL SYMBOL FUNCTION TYPE.
  gateway_validation_source_call CLOSED ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
  eapply gateway_source_same with (target := Callstate definition
    [Vptr files files_offset; Vptr position Ptrofs.zero; Vptr key Ptrofs.zero; Vptr value Ptrofs.zero]
    (gateway_validation_next_cont environment parameters) before).
  - exact CLOSED.
  - cbn; tauto.
  - intros; eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero).
    + reflexivity.
    + apply old_expression_value, value_function; [exact LOCAL |exact SYMBOL |reflexivity].
    + apply cons_argument_values with (v := Vptr files files_offset).
      * apply old_expression_value, value_temp; exact FILES.
      * reflexivity.
      * apply cons_argument_values with (v := Vptr position Ptrofs.zero).
        -- apply local_address_expression; exact POSITION.
        -- reflexivity.
        -- apply cons_argument_values with (v := Vptr key Ptrofs.zero).
           ++ apply local_address_expression; exact KEY.
           ++ reflexivity.
           ++ apply cons_argument_values with (v := Vptr value Ptrofs.zero);
                [apply local_address_expression; exact VALUE |reflexivity |apply no_argument_values].
    + change (Genv.find_funct_ptr ge symbol = Some definition); exact FUNCTION.
    + exact TYPE.
  - apply gateway_source_reached; auto.
Qed.
