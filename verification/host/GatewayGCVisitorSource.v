(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: The maintained traverse body reaches its genuine nonempty SDK visitor. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewaySDKCapabilities GatewayLinkedSource GatewayOutcome
  GatewaySourcePaths GatewaySourcePathExecution GatewaySourceBoundCalls GatewaySourceSegmentAutomation GatewayFramedRuntime.
Import ListNotations.
Local Opaque Clight.globalenv.

Lemma gateway_gc_data_true memory object offset :
  Mem.weak_valid_pointer memory object (Ptrofs.unsigned offset) = true ->
  bool_val (Vptr object offset) (tptr (Tstruct __object noattr)) memory = Some true.
Proof.
  intro LIVE; change ((if Mem.weak_valid_pointer memory object (Ptrofs.unsigned offset)
    then Some true else None) = Some true); rewrite LIVE; reflexivity.
Qed.

Definition gateway_gc_visit_cont parameters :=
  Kcall (Some _t'2) f_host_outcome_traverse empty_env parameters
    (Kseq (Sset _t'1 (Ecast (Etempvar _t'2 tint) tint))
      (Kseq (Sreturn (Some (Etempvar _t'1 tint))) Kstop)).

Theorem gateway_actual_gc_visitor_source {World Event} (backend : gateway_backend World Event)
    (ge : Clight.genv) (property : mem -> World -> Prop) parameters memory self self_offset data data_offset argument argument_offset visitor :
  gateway_ambient_closed backend property -> gateway_outcome_member_layout ge ->
  parameters ! _self = Some (Vptr self self_offset) -> parameters ! _visit = Some (Vptr visitor Ptrofs.zero) ->
  parameters ! _argument = Some (Vptr argument argument_offset) ->
  Genv.find_funct_ptr ge visitor = Some gateway_sdk_visitor_definition ->
  (forall memory world, property memory world ->
    Mem.loadv Mptr memory (gateway_outcome_slot self self_offset) = Some (Vptr data data_offset)) ->
  (forall memory world, property memory world -> Mem.weak_valid_pointer memory data (Ptrofs.unsigned data_offset) = true) ->
  exists selected,
    gateway_source_path backend ge
      gateway_sdk_visitor_definition [Vptr data data_offset; Vptr argument argument_offset]
      (gateway_gc_visit_cont selected) property
      (State f_host_outcome_traverse (fn_body f_host_outcome_traverse) Kstop empty_env parameters memory) property.
Proof.
  intros CLOSED LAYOUT SELF VISITOR ARGUMENT FUNCTION LOAD LIVE; eexists.
  gateway_bound_source_call CLOSED
    ltac:(fun _ => eapply gateway_actual_outcome_member_read;
      [repeat rewrite PTree.gso by discriminate; exact SELF |exact LAYOUT |eapply LOAD; eassumption])
    ltac:(fun _ => first [reflexivity |eapply gateway_gc_data_true; eapply LIVE; eassumption]).
  eapply gateway_source_same with
    (target := Callstate gateway_sdk_visitor_definition [Vptr data data_offset; Vptr argument argument_offset]
      (gateway_gc_visit_cont _) memory).
  - exact CLOSED.
  - cbn; tauto.
  - intros; eapply certified_call_edge with (vf := Vptr visitor Ptrofs.zero).
    + reflexivity.
    + apply old_expression_value, value_temp.
      repeat rewrite PTree.gso by discriminate; exact VISITOR.
    + apply cons_argument_values with (v := Vptr data data_offset).
      * gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
      * reflexivity.
      * apply cons_argument_values with (v := Vptr argument argument_offset).
        -- gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
        -- reflexivity.
        -- apply no_argument_values.
    + change (Genv.find_funct_ptr ge visitor = Some gateway_sdk_visitor_definition); exact FUNCTION.
    + reflexivity.
  - apply gateway_source_reached; auto.
Qed.

Theorem gateway_actual_gc_visitor_reachable {World Event} (backend : gateway_backend World Event)
    (property : mem -> World -> Prop) parameters before world self self_offset data data_offset argument argument_offset :
  gateway_ambient_closed backend property -> property before world ->
  parameters ! _self = Some (Vptr self self_offset) -> parameters ! _argument = Some (Vptr argument argument_offset) ->
  (forall memory world, property memory world ->
    Mem.loadv Mptr memory (gateway_outcome_slot self self_offset) = Some (Vptr data data_offset)) ->
  (forall memory world, property memory world -> Mem.weak_valid_pointer memory data (Ptrofs.unsigned data_offset) = true) ->
  exists visitor selected events after,
    Genv.find_symbol (Clight.globalenv (gateway_linked_program gateway_sdk_capabilities)) gateway_sdk_visitor_identifier = Some visitor /\
    gateway_steps backend (Clight.globalenv (gateway_linked_program gateway_sdk_capabilities))
      (gateway_live (State f_host_outcome_traverse (fn_body f_host_outcome_traverse) Kstop empty_env
        (PTree.set _visit (Vptr visitor Ptrofs.zero) parameters) before) world) events
      (gateway_live (Callstate gateway_sdk_visitor_definition [Vptr data data_offset; Vptr argument argument_offset]
        (gateway_gc_visit_cont selected) after) world).
Proof.
  intros CLOSED READY SELF ARGUMENT LOAD LIVE.
  destruct gateway_sdk_visitor_callable as [visitor [SYMBOL FUNCTION]].
  destruct (gateway_actual_gc_visitor_source backend (Clight.globalenv (gateway_linked_program gateway_sdk_capabilities))
    property (PTree.set _visit (Vptr visitor Ptrofs.zero) parameters)
    before self self_offset data data_offset argument argument_offset visitor CLOSED gateway_sdk_outcome_layout
    ltac:(rewrite PTree.gso by discriminate; exact SELF) (PTree.gss _ _ _)
    ltac:(rewrite PTree.gso by discriminate; exact ARGUMENT) FUNCTION LOAD LIVE) as [selected SCRIPT].
  destruct (gateway_source_path_execution backend _ _ _ _ _ _ _ SCRIPT before world READY)
    as [events [after [RUN RESULT]]].
  exists visitor, selected, events, after; split; [exact SYMBOL |exact RUN].
Qed.
