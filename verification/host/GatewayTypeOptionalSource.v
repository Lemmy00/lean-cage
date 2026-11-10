(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Optional non-None values reach the same actual builtin test. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayObjects GatewayFunctionEntry GatewayBuiltinTypeSource GatewayTypeLiteralSource
  GatewaySourceSegments GatewaySourcePaths GatewaySourceCuts GatewaySourceSegmentAutomation GatewaySourceBoundCalls
  GatewayFramedRuntime GatewayUnaryExpressions GatewayObjectAddresses GatewayInstructions GatewayCalls GatewaySourceObjectReceipt.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_has_type_comparison := Ecast
  (Ebinop Oeq (Etempvar _value (tptr (Tstruct __object noattr)))
    (Eaddrof (Evar __Py_NoneStruct (Tstruct __object noattr)) (tptr (Tstruct __object noattr))) tint) tbool.
Definition gateway_has_type_comparison_cont :=
  Kseq gateway_has_type_optional_tail (Kseq gateway_has_type_instance_tail Kstop).

(* Undefined pointer comparisons remain possible in the machine. This lemma
   describes only the value of an actual defined comparison, without adding a
   runtime pointer-validity premise or presuming a future helper return. *)
Lemma gateway_type_defined_pointer_equality (ge : Clight.genv) memory object offset none result :
  sem_binary_operation ge Oeq (Vptr object offset) (tptr (Tstruct __object noattr))
    (Vptr none Ptrofs.zero) (tptr (Tstruct __object noattr)) memory = Some result ->
  result = Vint (if Val.eq (Vptr object offset) (Vptr none Ptrofs.zero) then Int.one else Int.zero).
Proof.
  change (option_map Val.of_bool
    (if eq_block object none then
      if Mem.weak_valid_pointer memory object (Ptrofs.unsigned offset) && Mem.weak_valid_pointer memory none 0
      then Some (Ptrofs.cmpu Ceq offset Ptrofs.zero) else None
     else if Mem.valid_pointer memory object (Ptrofs.unsigned offset) && Mem.valid_pointer memory none 0
      then Some false else None) = Some result ->
    result = Vint (if Val.eq (Vptr object offset) (Vptr none Ptrofs.zero) then Int.one else Int.zero)).
  destruct (eq_block object none) as [SAME |DIFFERENT].
  - subst none; destruct (_ && _) eqn:LIVE; [|discriminate].
    change (Some (Val.of_bool (Ptrofs.eq offset Ptrofs.zero)) = Some result ->
      result = Vint (if Val.eq (Vptr object offset) (Vptr object Ptrofs.zero) then Int.one else Int.zero)).
    destruct (Ptrofs.eq_dec offset Ptrofs.zero) as [ZERO |NONZERO].
    + subst offset; rewrite Ptrofs.eq_true; destruct (Val.eq (Vptr object Ptrofs.zero) (Vptr object Ptrofs.zero));
        [intros SAME; inversion SAME; reflexivity |contradiction].
    + rewrite Ptrofs.eq_false by exact NONZERO; destruct (Val.eq (Vptr object offset) (Vptr object Ptrofs.zero));
        [congruence |intros SAME; inversion SAME; reflexivity].
  - destruct (_ && _) eqn:LIVE; [|discriminate].
    destruct (Val.eq (Vptr object offset) (Vptr none Ptrofs.zero)); [congruence |].
    intros SAME; inversion SAME; reflexivity.
Qed.



Theorem gateway_type_comparison_actual (ge : Clight.genv) parameters memory object offset none result :
  parameters ! _value = Some (Vptr object offset) -> Genv.find_symbol ge __Py_NoneStruct = Some none ->
  eval_expr ge empty_env parameters memory gateway_has_type_comparison result ->
  result = Vint (if Val.eq (Vptr object offset) (Vptr none Ptrofs.zero) then Int.one else Int.zero).
Proof.
  intros VALUE NONE EVALUATION; unfold gateway_has_type_comparison in EVALUATION.
  inversion EVALUATION; subst.
  - match goal with BINARY : eval_expr _ _ _ _ (Ebinop Oeq _ _ _) _ |- _ => inversion BINARY; subst end.
    + match goal with TEMP : eval_expr _ _ _ _ (Etempvar _value _) _ |- _ =>
        pose proof (evaluated_unique _ _ _ _ _ _ (value_temp _ _ _ _ _ (tptr (Tstruct __object noattr)) _ VALUE) _ TEMP) as SAME; subst end.
      match goal with ADDRESS : eval_expr _ _ _ _ (Eaddrof _ _) _ |- _ =>
        pose proof (proj2 (gateway_global_address_expression ge empty_env parameters memory __Py_NoneStruct (Tstruct __object noattr)
          none ltac:(apply PTree.gempty) NONE) _ ADDRESS) as SAME; subst end.
      match goal with COMPARE : sem_binary_operation _ Oeq _ _ _ _ _ = Some ?actual |- _ =>
        pose proof (gateway_type_defined_pointer_equality ge memory object offset none actual COMPARE) as SAME; subst actual end.
      destruct (Val.eq (Vptr object offset) (Vptr none Ptrofs.zero)); cbn in *;
        match goal with CAST : Some _ = Some result |- _ => inversion CAST; reflexivity end.
    + match goal with LOCATION : eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion LOCATION end.
  - match goal with LOCATION : eval_lvalue _ _ _ _ (Ecast _ _) _ _ _ |- _ => inversion LOCATION end.
Qed.

Theorem gateway_has_type_optional_comparison {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) parameters before object offset :
  gateway_ambient_closed backend property -> parameters ! _value = Some (Vptr object offset) ->
  parameters ! _optional = Some (Vint Int.one) ->
  (forall memory world, property memory world -> Mem.weak_valid_pointer memory object (Ptrofs.unsigned offset) = true) ->
  gateway_source_segment backend ge property
    (State f_host_has_type (fn_body f_host_has_type) Kstop empty_env parameters before)
    (State f_host_has_type (Sset _t'1 gateway_has_type_comparison) gateway_has_type_comparison_cont empty_env parameters before) property.
Proof.
  intros CLOSED VALUE OPTIONAL LIVE.
  gateway_segment_dynamic CLOSED
    ltac:(fun _ => eapply gateway_unary_expression_value with (value := Vptr object offset) (result := Vint Int.zero);
      [gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity) |
       match goal with GOOD : property ?memory ?world |- _ =>
         change (option_map (fun flag => Val.of_bool (negb flag))
           (if Mem.weak_valid_pointer memory object (Ptrofs.unsigned offset) then Some true else None) = Some (Vint Int.zero));
         rewrite (LIVE memory world GOOD); reflexivity end]) ltac:(fun _ => reflexivity).
Qed.

Theorem gateway_has_type_after_optional {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) parameters before object offset class class_offset symbol definition :
  gateway_ambient_closed backend property -> parameters ! _value = Some (Vptr object offset) ->
  parameters ! _type = Some (Vptr class class_offset) ->
  Genv.find_symbol ge _PyObject_IsInstance = Some symbol -> Genv.find_funct_ptr ge symbol = Some definition ->
  type_of_fundef definition = Tfunction [tptr (Tstruct __object noattr); tptr (Tstruct __object noattr)] tint cc_default ->
  exists selected,
    gateway_source_path backend ge definition [Vptr object offset; Vptr class class_offset]
      (gateway_has_type_instance_cont selected) property
      (State f_host_has_type Sskip gateway_has_type_comparison_cont empty_env (PTree.set _t'1 (Vint Int.zero) parameters) before) property.
Proof.
  intros CLOSED VALUE CLASS SYMBOL FUNCTION TYPE; eexists.
  unfold gateway_has_type_comparison_cont.
  gateway_bound_source_call CLOSED ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
  eapply gateway_source_same with (target := Callstate definition [Vptr object offset; Vptr class class_offset]
    (gateway_has_type_instance_cont _) before).
  - exact CLOSED.
  - cbn; tauto.
  - intros; eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero).
    + reflexivity.
    + apply old_expression_value, value_function; [reflexivity |exact SYMBOL |reflexivity].
    + apply cons_argument_values with (v := Vptr object offset).
      * gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
      * reflexivity.
      * apply cons_argument_values with (v := Vptr class class_offset).
        -- gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
        -- reflexivity.
        -- apply no_argument_values.
    + change (Genv.find_funct_ptr ge symbol = Some definition); exact FUNCTION.
    + exact TYPE.
  - apply gateway_source_reached; auto.
Qed.


Theorem gateway_actual_optional_type_check {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) (post : int -> mem -> World -> Prop)
    object offset class class_offset none before world events value after next symbol definition :
  gateway_ambient_closed backend property -> (forall status, gateway_ambient_closed backend (post status)) ->
  property before world -> Vptr object offset <> Vptr none Ptrofs.zero ->
  (forall memory current, property memory current -> Mem.weak_valid_pointer memory object (Ptrofs.unsigned offset) = true) ->
  Genv.find_symbol ge __Py_NoneStruct = Some none ->
  Genv.find_symbol ge _PyObject_IsInstance = Some symbol -> Genv.find_funct_ptr ge symbol = Some definition ->
  gateway_object_api_definition gateway_api_is_instance = Some definition ->
  type_of_fundef definition = Tfunction [tptr (Tstruct __object noattr); tptr (Tstruct __object noattr)] tint cc_default ->
  (forall memory current result changed following observed, property memory current ->
    gateway_object_operation backend gateway_api_is_instance [Vptr object offset; Vptr class class_offset]
      memory current result changed following observed ->
    exists status, result = Vint status /\ post status changed following) ->
  gateway_steps backend ge
    (gateway_live (Callstate (Internal f_host_has_type) [Vptr object offset; Vptr class class_offset; Vint Int.one] Kstop before) world) events
    (gateway_live (Returnstate value Kstop after) next) ->
  exists status, value = Vint status /\ post status after next.
Proof.
  intros CLOSED POST_CLOSED INPUT DIFFERENT POINTER NONE SYMBOL FUNCTION DEFINITION TYPE OBSERVER RUN.
  destruct (actual_gateway_function_entry_ambient backend ge f_host_has_type
    [Vptr object offset; Vptr class class_offset; Vint Int.one] Kstop before world events value Kstop after next RUN)
    as (pending &rest &entry_memory &entry_world &environment &temporaries &allocated &EVENTS &AMBIENT &PREFIX &ENTRY &REST).
  destruct (gateway_has_type_entry_parameters ge _ _ _ _ _ _ _ ENTRY) as [ENV [MEMORY [VALUE [CLASS OPTIONAL]]]].
  subst environment allocated.
  assert (READY : property entry_memory entry_world).
  { exact (gateway_ambient_run_ready backend ge property CLOSED
      (Callstate (Internal f_host_has_type) [Vptr object offset; Vptr class class_offset; Vint Int.one] Kstop before)
      before world pending entry_memory entry_world INPUT AMBIENT PREFIX). }
  pose proof (gateway_has_type_optional_comparison backend ge property temporaries entry_memory object offset
    CLOSED VALUE OPTIONAL POINTER) as SEGMENT.
  destruct (gateway_source_segment_cut backend ge property _ _ property SEGMENT entry_memory entry_world rest value after next READY REST)
    as (prefix &suffix &memory &current &TAIL &QUIET &TO_COMPARISON &AT_COMPARISON &CONTINUE).
  destruct (gateway_set_result_cut backend ge f_host_has_type _t'1 gateway_has_type_comparison gateway_has_type_comparison_cont
    empty_env temporaries memory current suffix value after next CONTINUE)
    as (waiting &following &compared &owner &result &SUFFIX &WAITING &TO_SET &EVALUATION &RESUME).
  assert (COMPARED : property compared owner).
  { exact (gateway_ambient_run_ready backend ge property CLOSED
      (State f_host_has_type (Sset _t'1 gateway_has_type_comparison) gateway_has_type_comparison_cont empty_env temporaries memory)
      memory current waiting compared owner AT_COMPARISON WAITING TO_SET). }
  pose proof (gateway_type_comparison_actual ge temporaries compared object offset none result VALUE NONE EVALUATION) as RESULT.
  destruct (Val.eq (Vptr object offset) (Vptr none Ptrofs.zero)) as [SAME |OTHER]; [contradiction |subst result].
  destruct (gateway_has_type_after_optional backend ge property temporaries compared object offset class class_offset symbol definition
    CLOSED VALUE CLASS SYMBOL FUNCTION TYPE) as [selected PATH].
  destruct (gateway_source_object_receipt backend ge gateway_api_is_instance definition [Vptr object offset; Vptr class class_offset]
    (gateway_has_type_instance_cont selected) property _ compared owner following value after next
    DEFINITION ltac:(cbn; exact I) ltac:(cbn; lia) CLOSED PATH COMPARED RESUME)
    as (prelude &tail &called &called_world &returned &changed &changed_world &observed &REMAINING &CALLED &TO_CALL &OPERATION &RETURN).
  destruct (OBSERVER called called_world returned changed changed_world observed CALLED OPERATION) as [status [SAME POST]].
  subst returned; destruct (gateway_has_type_instance_return backend ge (post status) selected status changed changed_world tail value after next
    (POST_CLOSED status) POST RETURN) as [SAME FINAL].
  exists status; auto.
Qed.
