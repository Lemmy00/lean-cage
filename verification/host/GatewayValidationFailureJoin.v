(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A failed real lookup cannot return a constructed Outcome. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayFramedRuntime GatewaySourcePaths
  GatewayOutcomeValidationPaths GatewayOutcomeValidationSource GatewayOutcomeValidationMetadata GatewayOutcomeFilesSource
  GatewayTypeLiteralSource GatewayValueReturns.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_validation_missing_field_returns_null {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    environment parameters index dictionary integer bytes unicode symbol before world events value after next :
  (index < 14)%nat -> parameters ! _index = Some (Vint (Int.repr (Z.of_nat index))) ->
  (forall identifier, In identifier [_host_has_type; _PyDict_Type; _PyLong_Type; _PyBytes_Type; _PyUnicode_Type] ->
    environment ! identifier = None) ->
  Genv.find_symbol ge _host_has_type = Some symbol -> Genv.find_funct_ptr ge symbol = Some (Internal f_host_has_type) ->
  Genv.find_symbol ge _PyDict_Type = Some dictionary -> Genv.find_symbol ge _PyLong_Type = Some integer ->
  Genv.find_symbol ge _PyBytes_Type = Some bytes -> Genv.find_symbol ge _PyUnicode_Type = Some unicode ->
  gateway_steps backend ge
    (gateway_live (Returnstate Vnullptr (gateway_validation_lookup_cont environment parameters) before) world) events
    (gateway_live (Returnstate value Kstop after) next) -> value = Vnullptr.
Proof.
  intros BOUND INDEX LOCAL SYMBOL FUNCTION DICTIONARY INTEGER BYTES UNICODE RUN.
  assert (CLOSED : gateway_ambient_closed backend (fun _ _ => True)) by (unfold gateway_ambient_closed; auto).
  destruct (gateway_validation_lookup_type backend ge (fun _ _ => True) environment parameters before index Vnullptr
    dictionary integer bytes unicode symbol CLOSED BOUND ltac:(left; reflexivity) INDEX LOCAL SYMBOL FUNCTION DICTIONARY INTEGER BYTES UNICODE)
    as [selected [PATH [SELECTED_INDEX [SELECTED_DATA SELECTED_VALUE]]]].
  destruct (gateway_source_path_cut backend ge _ _ _ _ _ _ PATH before world events value after next I RUN)
    as (prefix &suffix &called &current &EVENTS &QUIET &TO_CALL &READY &REST).
  destruct (gateway_return_cut backend ge (Internal f_host_has_type) _ (gateway_outcome_field_type_cont environment selected)
    called current suffix (Returnstate value Kstop after) next ltac:(reflexivity) ltac:(cbn; lia) REST)
    as (checked &tail &status &changed &following &TAIL &CHECK &RETURN).
  destruct (gateway_actual_null_type_check backend ge (fun _ _ => True) _ _ called current checked status changed following CLOSED I CHECK)
    as [STATUS GOOD]; subst status.
  eapply (gateway_outcome_field_nonpositive_null backend ge environment selected changed Int.zero
    (Int.repr (Z.of_nat index)) ltac:(rewrite SELECTED_INDEX; exact INDEX) ltac:(change (0 <= 0); lia)); [exact I |exact RETURN].
Qed.

Theorem gateway_validation_missing_json_returns_null {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    environment parameters dictionary symbol before world events value after next :
  environment ! _host_has_type = None -> environment ! _PyDict_Type = None ->
  Genv.find_symbol ge _host_has_type = Some symbol -> Genv.find_funct_ptr ge symbol = Some (Internal f_host_has_type) ->
  Genv.find_symbol ge _PyDict_Type = Some dictionary ->
  gateway_steps backend ge
    (gateway_live (Returnstate Vnullptr (gateway_validation_json_lookup_cont environment parameters) before) world) events
    (gateway_live (Returnstate value Kstop after) next) -> value = Vnullptr.
Proof.
  intros LOCAL TYPE SYMBOL FUNCTION DICTIONARY RUN.
  assert (CLOSED : gateway_ambient_closed backend (fun _ _ => True)) by (unfold gateway_ambient_closed; auto).
  pose proof (gateway_validation_json_type backend ge (fun _ _ => True) environment parameters before Vnullptr dictionary symbol
    CLOSED ltac:(left; reflexivity) LOCAL TYPE SYMBOL FUNCTION DICTIONARY) as PATH.
  destruct (gateway_source_path_cut backend ge _ _ _ _ _ _ PATH before world events value after next I RUN)
    as (prefix &suffix &called &current &EVENTS &QUIET &TO_CALL &READY &REST).
  destruct (gateway_return_cut backend ge (Internal f_host_has_type) _
    (gateway_outcome_json_type_cont environment (set_opttemp (Some _t'11) Vnullptr parameters))
    called current suffix (Returnstate value Kstop after) next ltac:(reflexivity) ltac:(cbn; lia) REST)
    as (checked &tail &status &changed &following &TAIL &CHECK &RETURN).
  destruct (gateway_actual_null_type_check backend ge (fun _ _ => True) _ _ called current checked status changed following CLOSED I CHECK)
    as [STATUS GOOD]; subst status.
  eapply (gateway_outcome_json_nonpositive_null backend ge environment _ changed Int.zero ltac:(change (0 <= 0); lia));
    [exact I |exact RETURN].
Qed.
