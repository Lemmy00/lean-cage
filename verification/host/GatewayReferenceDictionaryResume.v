(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The same second child is inserted, released, then the actual dictionary loop advances. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayValueEntry GatewayContainerLoopSource
  GatewayContainerDictionarySource GatewayContainerArrayRelease GatewaySourceBoundCalls GatewaySourceSegmentAutomation
  GatewaySourcePaths GatewaySourceSegments GatewayFramedRuntime GatewayUnaryExpressions.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_dictionary_insert_source_path {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) slots parameters parent parent_offset key key_offset child child_offset memory symbol definition :
  gateway_ambient_closed backend property -> parameters ! _container = Some (Vptr parent parent_offset) ->
  parameters ! _first = Some (Vptr key key_offset) ->
  (forall memory world, property memory world -> Mem.weak_valid_pointer memory child (Ptrofs.unsigned child_offset) = true) ->
  Genv.find_symbol ge _PyDict_SetItem = Some symbol -> Genv.find_funct_ptr ge symbol = Some definition ->
  type_of_fundef definition = Tfunction [tptr (Tstruct __object noattr); tptr (Tstruct __object noattr);
    tptr (Tstruct __object noattr)] tint cc_default ->
  exists called_parameters,
    gateway_source_path backend ge definition [Vptr parent parent_offset; Vptr key key_offset; Vptr child child_offset]
      (gateway_dictionary_insert_cont slots called_parameters) property
      (Returnstate (Vptr child child_offset) (gateway_dictionary_second_cont slots parameters) memory) property /\
    called_parameters ! _value__1 = Some (Vptr child child_offset) /\
    called_parameters ! _container = parameters ! _container /\ called_parameters ! _first = parameters ! _first /\
    called_parameters ! _stream = parameters ! _stream /\ called_parameters ! _depth = parameters ! _depth /\
    called_parameters ! _index__1 = parameters ! _index__1.
Proof.
  intros CLOSED PARENT KEY POINTER SYMBOL FUNCTION TYPE; eexists; split.
  - gateway_bound_source_call CLOSED
      ltac:(fun _ => eapply gateway_unary_expression_value with (value := Vptr child child_offset) (result := Vint Int.zero);
        [gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity) |
         match goal with GOOD : property ?current ?world |- _ =>
           change (option_map (fun flag => Val.of_bool (negb flag))
             (if Mem.weak_valid_pointer current child (Ptrofs.unsigned child_offset) then Some true else None) = Some (Vint Int.zero));
           rewrite (POINTER current world GOOD); reflexivity end]) ltac:(fun _ => reflexivity).
    eapply gateway_source_same with (target := Callstate definition
      [Vptr parent parent_offset; Vptr key key_offset; Vptr child child_offset]
      (gateway_dictionary_insert_cont slots _) memory).
    + exact CLOSED.
    + cbn; tauto.
    + intros; eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero).
      * reflexivity.
      * apply old_expression_value; eapply value_function; [reflexivity |exact SYMBOL |reflexivity].
      * apply cons_argument_values with (v := Vptr parent parent_offset).
        -- gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
        -- reflexivity.
        -- apply cons_argument_values with (v := Vptr key key_offset).
           ++ gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
           ++ reflexivity.
           ++ apply cons_argument_values with (v := Vptr child child_offset).
              ** gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
              ** reflexivity.
              ** apply no_argument_values.
      * change (Genv.find_funct_ptr ge symbol = Some definition); exact FUNCTION.
      * exact TYPE.
    + apply gateway_source_reached; auto.
  - unfold set_opttemp; repeat split; repeat rewrite PTree.gso by discriminate;
      first [apply PTree.gss |reflexivity].
Qed.

Theorem gateway_dictionary_release_key_source_path {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) slots parameters status key key_offset memory symbol definition :
  gateway_ambient_closed backend property -> parameters ! _first = Some (Vptr key key_offset) ->
  Genv.find_symbol ge _Py_DecRef = Some symbol -> Genv.find_funct_ptr ge symbol = Some definition ->
  type_of_fundef definition = Tfunction [tptr (Tstruct __object noattr)] tvoid cc_default ->
  exists called_parameters,
    gateway_source_path backend ge definition [Vptr key key_offset]
      (gateway_dictionary_release_key_cont slots called_parameters) property
      (Returnstate (Vint status) (gateway_dictionary_insert_cont slots parameters) memory) property /\
    called_parameters ! _result__1 = Some (Vint status) /\
    called_parameters ! _container = parameters ! _container /\ called_parameters ! _first = parameters ! _first /\
    called_parameters ! _value__1 = parameters ! _value__1 /\ called_parameters ! _stream = parameters ! _stream /\
    called_parameters ! _depth = parameters ! _depth /\ called_parameters ! _index__1 = parameters ! _index__1.
Proof.
  intros CLOSED KEY SYMBOL FUNCTION TYPE; eexists; split.
  - gateway_bound_source_call CLOSED ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
    eapply gateway_source_same with (target := Callstate definition [Vptr key key_offset]
      (gateway_dictionary_release_key_cont slots _) memory).
    + exact CLOSED.
    + cbn; tauto.
    + intros; eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero).
      * reflexivity.
      * apply old_expression_value; eapply value_function; [reflexivity |exact SYMBOL |reflexivity].
      * apply cons_argument_values with (v := Vptr key key_offset).
        -- gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
        -- reflexivity.
        -- apply no_argument_values.
      * change (Genv.find_funct_ptr ge symbol = Some definition); exact FUNCTION.
      * exact TYPE.
    + apply gateway_source_reached; auto.
  - unfold set_opttemp; repeat split; repeat rewrite PTree.gso by discriminate;
      first [apply PTree.gss |reflexivity].
Qed.

Theorem gateway_dictionary_release_child_source_path {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) slots parameters ignored child child_offset memory symbol definition :
  gateway_ambient_closed backend property -> parameters ! _value__1 = Some (Vptr child child_offset) ->
  Genv.find_symbol ge _Py_DecRef = Some symbol -> Genv.find_funct_ptr ge symbol = Some definition ->
  type_of_fundef definition = Tfunction [tptr (Tstruct __object noattr)] tvoid cc_default ->
  gateway_source_path backend ge definition [Vptr child child_offset]
    (gateway_dictionary_release_child_cont slots parameters) property
    (Returnstate ignored (gateway_dictionary_release_key_cont slots parameters) memory) property.
Proof.
  intros CLOSED CHILD SYMBOL FUNCTION TYPE.
  gateway_bound_source_call CLOSED ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
  eapply gateway_source_same with (target := Callstate definition [Vptr child child_offset]
    (gateway_dictionary_release_child_cont slots parameters) memory).
  - exact CLOSED.
  - cbn; tauto.
  - intros; eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero).
    + reflexivity.
    + apply old_expression_value; eapply value_function; [reflexivity |exact SYMBOL |reflexivity].
    + apply cons_argument_values with (v := Vptr child child_offset).
      * gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
      * reflexivity.
      * apply no_argument_values.
    + change (Genv.find_funct_ptr ge symbol = Some definition); exact FUNCTION.
    + exact TYPE.
  - apply gateway_source_reached; auto.
Qed.

Definition gateway_dictionary_next_parameters index parameters :=
  PTree.set _index__1 (Vlong (Int64.add index Int64.one)) parameters.

Theorem gateway_dictionary_next_source_segment {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) slots parameters ignored index memory :
  gateway_ambient_closed backend property -> parameters ! _result__1 = Some (Vint Int.zero) ->
  parameters ! _index__1 = Some (Vlong index) ->
  gateway_source_segment backend ge property
    (Returnstate ignored (gateway_dictionary_release_child_cont slots parameters) memory)
    (State f_host_value gateway_container_loop gateway_container_loop_cont (gateway_value_environment slots)
      (gateway_dictionary_next_parameters index parameters) memory) property.
Proof.
  intros CLOSED STATUS INDEX.
  unfold gateway_dictionary_release_child_cont, gateway_dictionary_iteration_cont.
  gateway_array_next_segment CLOSED.
  eapply gateway_segment_same with (next := State f_host_value Sskip
    (Kloop1 gateway_container_loop_body gateway_container_loop_increment gateway_container_loop_cont)
    (gateway_value_environment slots) parameters memory).
  - exact CLOSED.
  - cbn; tauto.
  - intros; eapply certified_if_edge with (b := false).
    + apply old_expression_value, value_temp; exact STATUS.
    + reflexivity.
  - gateway_array_next_segment CLOSED.
    eapply gateway_segment_same with (next := State f_host_value Sskip
      (Kloop2 gateway_container_loop_body gateway_container_loop_increment gateway_container_loop_cont)
      (gateway_value_environment slots) (gateway_dictionary_next_parameters index parameters) memory).
    + exact CLOSED.
    + cbn; tauto.
    + intros; apply certified_set_edge.
      eapply binary_expression_value with (v := Vlong index) (w := Vint Int.one).
      * apply old_expression_value, value_temp; exact INDEX.
      * apply old_expression_value; constructor.
      * change (Some (Vlong (Int64.add index (Int64.repr (Int.signed Int.one)))) =
          Some (Vlong (Int64.add index Int64.one))); reflexivity.
    + gateway_array_next_segment CLOSED.
Qed.
