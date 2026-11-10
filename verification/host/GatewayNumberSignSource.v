(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual final integer sign path releases exactly the retained base and old value. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayNumberIntegerStructure GatewayNumberIntegerCalls
  GatewayJsonNumberSource GatewayNumberConstruction GatewaySourcePaths GatewaySourceBoundCalls GatewaySourceSegmentAutomation
  GatewaySourceCuts GatewaySourceSegments GatewayReturns GatewayReturnIdentity GatewayReturnTypes GatewayValueReturns
  GatewayObjects GatewayFramedRuntime.
Import ListNotations.

Definition number_sign_base_release := json_number_first number_integer_after_loop.
Definition number_sign_after_base := json_number_rest number_integer_after_loop.
Definition number_sign_select := json_number_first number_sign_after_base.
Definition number_sign_after := json_number_rest number_sign_after_base.
Definition number_sign_branch := json_number_then number_sign_select.
Definition number_sign_group := json_number_first number_sign_branch.
Definition number_sign_assign := json_number_rest number_sign_group.
Definition number_sign_after_negative := json_number_rest number_sign_branch.
Definition number_sign_old_release := json_number_first number_sign_after_negative.
Definition number_sign_value_assign := json_number_rest number_sign_after_negative.
Definition number_sign_return := json_number_first number_sign_after.
Definition number_sign_base_cont parameters := Kcall None f_host_json_number empty_env parameters (Kseq number_sign_after_base Kstop).
Definition number_sign_negative_cont parameters := Kcall (Some _t'21) f_host_json_number empty_env parameters
  (Kseq number_sign_assign (Kseq number_sign_after_negative (Kseq number_sign_after Kstop))).
Definition number_sign_old_cont parameters := Kcall None f_host_json_number empty_env parameters
  (Kseq number_sign_value_assign (Kseq number_sign_after Kstop)).

Theorem actual_number_sign_source_shapes :
  number_sign_base_release = Scall None
    (Evar _Py_DecRef (Tfunction [tptr (Tstruct __object noattr)] tvoid cc_default))
    [Etempvar _base (tptr (Tstruct __object noattr))] /\
  number_sign_select = Sifthenelse (Etempvar _negative tint) number_sign_branch Sskip /\
  number_sign_return = Sreturn (Some (Etempvar _value__1 (tptr (Tstruct __object noattr)))).
Proof. repeat split; reflexivity. Qed.

Theorem gateway_number_final_base_release_path {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) parameters base memory symbol definition :
  gateway_ambient_closed backend property -> parameters ! _base = Some base -> gateway_object_pointer_value base ->
  Genv.find_symbol ge _Py_DecRef = Some symbol -> Genv.find_funct_ptr ge symbol = Some definition ->
  type_of_fundef definition = Tfunction [tptr (Tstruct __object noattr)] tvoid cc_default ->
  gateway_source_path backend ge definition [base] (number_sign_base_cont parameters) property
    (State f_host_json_number Sskip number_integer_loop_cont empty_env parameters memory) property.
Proof.
  intros CLOSED BASE POINTER SYMBOL FUNCTION TYPE; unfold number_integer_loop_cont.
  gateway_bound_source_call CLOSED ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
  number_sdk_reached CLOSED symbol _Py_DecRef SYMBOL FUNCTION TYPE
    ltac:(fun _ => apply cons_argument_values with (v := base);
      [gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity) |
        destruct POINTER as [NULL |[object [offset SAME]]]; subst base; reflexivity |apply no_argument_values]).
Qed.

Theorem gateway_number_negative_source_path {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) parameters current ignored memory symbol definition :
  gateway_ambient_closed backend property -> parameters ! _negative = Some (Vint Int.one) ->
  parameters ! _value__1 = Some current -> gateway_object_pointer_value current ->
  Genv.find_symbol ge _PyNumber_Negative = Some symbol -> Genv.find_funct_ptr ge symbol = Some definition ->
  type_of_fundef definition = Tfunction [tptr (Tstruct __object noattr)] (tptr (Tstruct __object noattr)) cc_default ->
  gateway_source_path backend ge definition [current] (number_sign_negative_cont parameters) property
    (Returnstate ignored (number_sign_base_cont parameters) memory) property.
Proof.
  intros CLOSED NEGATIVE CURRENT POINTER SYMBOL FUNCTION TYPE.
  gateway_bound_source_call CLOSED ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
  number_sdk_reached CLOSED symbol _PyNumber_Negative SYMBOL FUNCTION TYPE
    ltac:(fun _ => apply cons_argument_values with (v := current);
      [gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity) |
        destruct POINTER as [NULL |[object [offset SAME]]]; subst current; reflexivity |apply no_argument_values]).
Qed.

Theorem gateway_number_negative_release_path {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) parameters current returned memory symbol definition :
  gateway_ambient_closed backend property -> parameters ! _value__1 = Some current -> gateway_object_pointer_value current ->
  Genv.find_symbol ge _Py_DecRef = Some symbol -> Genv.find_funct_ptr ge symbol = Some definition ->
  type_of_fundef definition = Tfunction [tptr (Tstruct __object noattr)] tvoid cc_default ->
  exists called_parameters,
    gateway_source_path backend ge definition [current] (number_sign_old_cont called_parameters) property
      (Returnstate returned (number_sign_negative_cont parameters) memory) property /\
    called_parameters ! _signed_value = Some returned /\
    (forall identifier, identifier <> _signed_value -> identifier <> _t'21 ->
      called_parameters ! identifier = parameters ! identifier).
Proof.
  intros CLOSED CURRENT POINTER SYMBOL FUNCTION TYPE; eexists; split.
  - gateway_bound_source_call CLOSED ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
    number_sdk_reached CLOSED symbol _Py_DecRef SYMBOL FUNCTION TYPE
      ltac:(fun _ => apply cons_argument_values with (v := current);
        [gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity) |
          destruct POINTER as [NULL |[object [offset SAME]]]; subst current; reflexivity |apply no_argument_values]).
  - split; [apply PTree.gss |]. intros identifier A B; unfold set_opttemp;
      repeat rewrite PTree.gso by congruence; reflexivity.
Qed.

Theorem gateway_number_positive_return_path {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) parameters ignored memory :
  gateway_ambient_closed backend property -> parameters ! _negative = Some (Vint Int.zero) ->
  gateway_source_segment backend ge property
    (Returnstate ignored (number_sign_base_cont parameters) memory)
    (State f_host_json_number number_sign_return
      (Kseq (json_number_rest number_sign_after) Kstop) empty_env parameters memory) property.
Proof.
  intros CLOSED POSITIVE; unfold number_sign_base_cont.
  gateway_segment_dynamic CLOSED ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
Qed.

Theorem gateway_number_negative_return_path {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) parameters selected ignored memory :
  gateway_ambient_closed backend property -> parameters ! _signed_value = Some selected ->
  gateway_source_segment backend ge property
    (Returnstate ignored (number_sign_old_cont parameters) memory)
    (State f_host_json_number number_sign_return
      (Kseq (json_number_rest number_sign_after) Kstop) empty_env
      (PTree.set _value__1 selected parameters) memory) property.
Proof.
  intros CLOSED SELECTED; unfold number_sign_old_cont.
  gateway_segment_dynamic CLOSED ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
Qed.

Theorem gateway_number_sign_return_identity {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    parameters selected before world events value after next :
  parameters ! _value__1 = Some selected ->
  gateway_steps backend ge
    (gateway_live (State f_host_json_number number_sign_return
      (Kseq (json_number_rest number_sign_after) Kstop) empty_env parameters before) world) events
    (gateway_live (Returnstate value Kstop after) next) -> value = selected.
Proof.
  intros SELECTED RUN.
  eapply (gateway_return_expression_identity backend ge f_host_json_number
    (Etempvar _value__1 (tptr (Tstruct __object noattr)))
    (Kseq (json_number_rest number_sign_after) Kstop) empty_env parameters before world selected events value after next).
  - reflexivity.
  - intros; apply old_expression_value, value_temp; exact SELECTED.
  - intros memory converted CAST; eapply gateway_pointer_cast_identity;
      [eexists; reflexivity |eexists; reflexivity |exact CAST].
  - exact RUN.
Qed.

Theorem gateway_number_positive_return_identity {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    parameters selected ignored before world events value after next :
  parameters ! _negative = Some (Vint Int.zero) -> parameters ! _value__1 = Some selected ->
  gateway_steps backend ge (gateway_live (Returnstate ignored (number_sign_base_cont parameters) before) world) events
    (gateway_live (Returnstate value Kstop after) next) -> value = selected.
Proof.
  intros POSITIVE SELECTED RUN.
  assert (CLOSED : gateway_ambient_closed backend (fun _ _ => True)) by (unfold gateway_ambient_closed; intros; exact I).
  pose proof (gateway_number_positive_return_path backend ge (fun _ _ => True) parameters ignored before CLOSED POSITIVE) as PATH.
  destruct (gateway_source_segment_cut backend ge _ _ _ _ PATH before world events value after next I RUN)
    as (prefix & suffix & middle & current & EVENTS & QUIET & PREFIX & READY & SUFFIX).
  exact (gateway_number_sign_return_identity backend ge parameters selected middle current suffix value after next SELECTED SUFFIX).
Qed.

Theorem gateway_number_negative_return_identity {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    parameters selected ignored before world events value after next :
  parameters ! _signed_value = Some selected ->
  gateway_steps backend ge (gateway_live (Returnstate ignored (number_sign_old_cont parameters) before) world) events
    (gateway_live (Returnstate value Kstop after) next) -> value = selected.
Proof.
  intros SELECTED RUN.
  assert (CLOSED : gateway_ambient_closed backend (fun _ _ => True)) by (unfold gateway_ambient_closed; intros; exact I).
  pose proof (gateway_number_negative_return_path backend ge (fun _ _ => True) parameters selected ignored before CLOSED SELECTED) as PATH.
  destruct (gateway_source_segment_cut backend ge _ _ _ _ PATH before world events value after next I RUN)
    as (prefix & suffix & middle & current & EVENTS & QUIET & PREFIX & READY & SUFFIX).
  apply (gateway_number_sign_return_identity backend ge (PTree.set _value__1 selected parameters) selected middle current suffix value after next);
    [apply PTree.gss |exact SUFFIX].
Qed.
