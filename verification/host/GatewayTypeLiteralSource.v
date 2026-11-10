(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: NULL and optional None select their real constant type-check returns. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBuiltinTypeSource GatewayOutcomeFilesSource
  GatewaySourceSegments GatewaySourceSegmentAutomation GatewayFramedRuntime GatewayUnaryExpressions GatewayObjectAddresses
  GatewayFunctionEntry GatewayCalls.
Import ListNotations.
Open Scope Z_scope.

Lemma gateway_segment_then_runtime {World Event} (backend : gateway_backend World Event) ge
    property source target middle value result :
  gateway_source_segment backend ge property source target middle ->
  gateway_runtime_path backend ge middle target value result ->
  gateway_runtime_path backend ge property source value result.
Proof.
  intro SEGMENT; induction SEGMENT; intro RETURN; [exact RETURN |].
  eapply gateway_runtime_next; [exact H |exact H0 |exact H1 |apply IHSEGMENT; exact RETURN].
Qed.



Definition gateway_has_type_after_null := match fn_body f_host_has_type with Ssequence _ rest => rest | _ => Sskip end.
Definition gateway_has_type_optional_tail :=
  match gateway_has_type_after_null with Ssequence (Ssequence _ tail) _ => tail | _ => Sskip end.
Definition gateway_has_type_instance_tail :=
  match gateway_has_type_after_null with Ssequence _ tail => tail | _ => Sskip end.
Definition gateway_has_type_none_return_cont := Kseq gateway_has_type_instance_tail Kstop.

Theorem gateway_has_type_null_path {World Event} (backend : gateway_backend World Event) ge
    (property : mem -> World -> Prop) parameters before :
  gateway_ambient_closed backend property -> parameters ! _value = Some Vnullptr ->
  gateway_runtime_path backend ge property
    (State f_host_has_type (fn_body f_host_has_type) Kstop empty_env parameters before) (Vint Int.zero) property.
Proof.
  intros CLOSED VALUE.
  eapply gateway_segment_then_runtime with
    (target := State f_host_has_type (Sreturn (Some (Econst_int Int.zero tint)))
      (Kseq gateway_has_type_after_null Kstop) empty_env parameters before) (middle := property).
  - gateway_segment_dynamic CLOSED
      ltac:(fun _ => eapply gateway_unary_expression_value with (value := Vnullptr) (result := Vint Int.one);
        [gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity) |reflexivity])
      ltac:(fun _ => reflexivity).
  - eapply gateway_runtime_same with (next := Returnstate (Vint Int.zero) Kstop before).
    + exact CLOSED.
    + cbn; tauto.
    + intros; apply unchanged_store_edge; eapply edge_return; [constructor |reflexivity].
    + apply gateway_runtime_return; [exact CLOSED |auto].
Qed.

Lemma gateway_type_same_pointer (ge : Clight.genv) memory object :
  Mem.weak_valid_pointer memory object 0 = true ->
  sem_binary_operation ge Oeq (Vptr object Ptrofs.zero) (tptr (Tstruct __object noattr))
    (Vptr object Ptrofs.zero) (tptr (Tstruct __object noattr)) memory = Some (Vint Int.one).
Proof.
  intro LIVE.
  change (option_map Val.of_bool
    (if eq_block object object then
      if Mem.weak_valid_pointer memory object 0 && Mem.weak_valid_pointer memory object 0
      then Some (Ptrofs.cmpu Ceq Ptrofs.zero Ptrofs.zero) else None
     else if Mem.valid_pointer memory object 0 && Mem.valid_pointer memory object 0
      then Val.cmp_different_blocks Ceq else None) = Some (Vint Int.one)).
  destruct (eq_block object object); [rewrite LIVE; reflexivity |congruence].
Qed.

Theorem gateway_has_type_none_path {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) parameters before none :
  gateway_ambient_closed backend property -> parameters ! _value = Some (Vptr none Ptrofs.zero) ->
  parameters ! _optional = Some (Vint Int.one) -> Genv.find_symbol ge __Py_NoneStruct = Some none ->
  (forall memory world, property memory world -> Mem.weak_valid_pointer memory none 0 = true) ->
  gateway_runtime_path backend ge property
    (State f_host_has_type (fn_body f_host_has_type) Kstop empty_env parameters before) (Vint Int.one) property.
Proof.
  intros CLOSED VALUE OPTIONAL NONE LIVE.
  eapply gateway_segment_then_runtime with
    (target := State f_host_has_type (Sreturn (Some (Econst_int Int.one tint)))
      gateway_has_type_none_return_cont empty_env (PTree.set _t'1 (Vint Int.one) parameters) before) (middle := property).
  - gateway_segment_dynamic CLOSED
      ltac:(fun _ => first [
        eapply gateway_unary_expression_value with (value := Vptr none Ptrofs.zero) (result := Vint Int.zero);
          [gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity) |
           apply gateway_validation_live_not; eapply LIVE; eassumption] |
        eapply gateway_global_address_expression; [apply PTree.gempty |exact NONE]])
      ltac:(fun _ => first [apply gateway_type_same_pointer; eapply LIVE; eassumption |reflexivity]).
  - eapply gateway_runtime_same with (next := Returnstate (Vint Int.one) Kstop before).
    + exact CLOSED.
    + cbn; tauto.
    + intros; apply unchanged_store_edge; eapply edge_return; [constructor |reflexivity].
    + apply gateway_runtime_return; [exact CLOSED |auto].
Qed.


Theorem gateway_actual_null_type_check {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) class optional before world events value after next :
  gateway_ambient_closed backend property -> property before world ->
  gateway_steps backend ge
    (gateway_live (Callstate (Internal f_host_has_type) [Vnullptr; class; Vint optional] Kstop before) world) events
    (gateway_live (Returnstate value Kstop after) next) -> value = Vint Int.zero /\ property after next.
Proof.
  intros CLOSED INPUT RUN.
  destruct (actual_gateway_function_entry_ambient backend ge f_host_has_type
    [Vnullptr; class; Vint optional] Kstop before world events value Kstop after next RUN)
    as (pending &rest &memory &current &environment &parameters &allocated &EVENTS &AMBIENT &PREFIX &ENTRY &REST).
  destruct (gateway_has_type_entry_parameters ge _ _ _ _ _ _ _ ENTRY) as [ENV [MEMORY [VALUE [CLASS OPTIONAL]]]].
  subst environment allocated.
  assert (READY : property memory current).
  { exact (gateway_ambient_run_ready backend ge property CLOSED
      (Callstate (Internal f_host_has_type) [Vnullptr; class; Vint optional] Kstop before)
      before world pending memory current INPUT AMBIENT PREFIX). }
  exact (gateway_runtime_path_return_exact backend ge property
    (State f_host_has_type (fn_body f_host_has_type) Kstop empty_env parameters memory) (Vint Int.zero) property
    memory current rest value after next READY
    (gateway_has_type_null_path backend ge property parameters memory CLOSED VALUE) REST).
Qed.

Theorem gateway_actual_none_type_check {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) class none before world events value after next :
  gateway_ambient_closed backend property -> property before world -> Genv.find_symbol ge __Py_NoneStruct = Some none ->
  (forall memory current, property memory current -> Mem.weak_valid_pointer memory none 0 = true) ->
  gateway_steps backend ge
    (gateway_live (Callstate (Internal f_host_has_type) [Vptr none Ptrofs.zero; class; Vint Int.one] Kstop before) world) events
    (gateway_live (Returnstate value Kstop after) next) -> value = Vint Int.one /\ property after next.
Proof.
  intros CLOSED INPUT NONE LIVE RUN.
  destruct (actual_gateway_function_entry_ambient backend ge f_host_has_type
    [Vptr none Ptrofs.zero; class; Vint Int.one] Kstop before world events value Kstop after next RUN)
    as (pending &rest &memory &current &environment &parameters &allocated &EVENTS &AMBIENT &PREFIX &ENTRY &REST).
  destruct (gateway_has_type_entry_parameters ge _ _ _ _ _ _ _ ENTRY) as [ENV [MEMORY [VALUE [CLASS OPTIONAL]]]].
  subst environment allocated.
  assert (READY : property memory current).
  { exact (gateway_ambient_run_ready backend ge property CLOSED
      (Callstate (Internal f_host_has_type) [Vptr none Ptrofs.zero; class; Vint Int.one] Kstop before)
      before world pending memory current INPUT AMBIENT PREFIX). }
  exact (gateway_runtime_path_return_exact backend ge property
    (State f_host_has_type (fn_body f_host_has_type) Kstop empty_env parameters memory) (Vint Int.one) property
    memory current rest value after next READY
    (gateway_has_type_none_path backend ge property parameters memory none CLOSED VALUE OPTIONAL NONE LIVE) REST).
Qed.
