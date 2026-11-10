(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Two individual non-callback interpreter queries retain the entry guard. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayInterpreterSource GatewayBindings
  GatewayNoStoreControl GatewayNoStoreAutomation GatewaySourceSegmentAutomation GatewayFramedRuntime.
Import ListNotations.

(* These are individual CPython C-ABI observations. Get/GetID do not invoke
   application callbacks; a returned value has its declared pointer/int64 shape.
   Only the specified guard property is retained. Error, pending and process
   loss are still source transitions and require no future return. *)
Record gateway_initialization_query_laws {World Event} (backend : gateway_backend World Event)
    (property : mem -> World -> Prop) : Prop := {
  gateway_initialization_get_guard : forall before world result after next observed,
    property before world ->
    gateway_external backend
      (EF_external "PyInterpreterState_Get" (mksignature [] Xptr cc_default)) []
      (tptr (Tstruct __is noattr)) cc_default [] before world result after next observed ->
    (exists object offset, result = Vptr object offset) /\ property after next;
  gateway_initialization_id_guard : forall before world object offset result after next observed,
    property before world ->
    gateway_external backend
      (EF_external "PyInterpreterState_GetID" (mksignature [Xptr] Xlong cc_default))
      [tptr (Tstruct __is noattr)] tlong cc_default [Vptr object offset]
      before world result after next observed ->
    (exists identifier, result = Vlong identifier) /\ property after next
}.

Theorem gateway_initialization_id_no_stores {World Event} (backend : gateway_backend World Event)
    ge (property : mem -> World -> Prop) parameters memory object offset :
  gateway_ambient_closed backend property -> gateway_initialization_query_laws backend property ->
  gateway_function_binding ge _PyInterpreterState_GetID gateway_interpreter_id_definition ->
  (forall parameters memory identifier, gateway_nostore_control backend ge property
    (Returnstate (Vlong identifier) (gateway_interpreter_id_cont true parameters) memory)) ->
  gateway_nostore_control backend ge property
    (Returnstate (Vptr object offset) (gateway_interpreter_get_cont true parameters) memory).
Proof.
  intros CLOSED QUERIES [symbol [SYMBOL FUNCTION]] RESUME.
  gateway_nostore_dynamic CLOSED ltac:(fun _ => fail) ltac:(fun _ => reflexivity) ltac:(fun _ => fail).
  eapply gateway_nostore_source_same with
    (target := Callstate gateway_interpreter_id_definition [Vptr object offset]
      (gateway_interpreter_id_cont true (PTree.set _t'1 (Vptr object offset) parameters)) memory).
  - exact CLOSED.
  - cbn; tauto.
  - exact I.
  - intros; eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero).
    + reflexivity.
    + apply old_expression_value; eapply value_function; [reflexivity |exact SYMBOL |reflexivity].
    + apply cons_argument_values with (v := Vptr object offset).
      * gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
      * reflexivity.
      * apply no_argument_values.
    + change (Genv.find_funct_ptr ge symbol = Some gateway_interpreter_id_definition); exact FUNCTION.
    + reflexivity.
  - apply gateway_nostore_external; [exact CLOSED |].
    intros before world result after next observed READY OPERATION.
    destruct (gateway_initialization_id_guard _ _ QUERIES before world object offset result after next observed
      READY OPERATION) as [[identifier SAME] POST]; subst result.
    exists property; split; [exact POST |apply RESUME].
Qed.

Theorem gateway_initialization_queries_no_stores {World Event} (backend : gateway_backend World Event)
    ge (property : mem -> World -> Prop) parameters memory :
  gateway_ambient_closed backend property -> gateway_initialization_query_laws backend property ->
  gateway_function_binding ge _PyInterpreterState_Get gateway_interpreter_get_definition ->
  gateway_function_binding ge _PyInterpreterState_GetID gateway_interpreter_id_definition ->
  (forall parameters memory identifier, gateway_nostore_control backend ge property
    (Returnstate (Vlong identifier) (gateway_interpreter_id_cont true parameters) memory)) ->
  gateway_nostore_control backend ge property
    (State f_PyInit__host (fn_body f_PyInit__host) Kstop empty_env parameters memory).
Proof.
  intros CLOSED QUERIES [symbol [SYMBOL FUNCTION]] ID RESUME.
  gateway_nostore_dynamic CLOSED ltac:(fun _ => fail) ltac:(fun _ => reflexivity) ltac:(fun _ => fail).
  eapply gateway_nostore_source_same with
    (target := Callstate gateway_interpreter_get_definition [] (gateway_interpreter_get_cont true parameters) memory).
  - exact CLOSED.
  - cbn; tauto.
  - exact I.
  - intros; eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero).
    + reflexivity.
    + apply old_expression_value; eapply value_function; [reflexivity |exact SYMBOL |reflexivity].
    + apply no_argument_values.
    + change (Genv.find_funct_ptr ge symbol = Some gateway_interpreter_get_definition); exact FUNCTION.
    + reflexivity.
  - apply gateway_nostore_external; [exact CLOSED |].
    intros before world result after next observed READY OPERATION.
    destruct (gateway_initialization_get_guard _ _ QUERIES before world result after next observed READY OPERATION)
      as [[object [offset SAME]] POST]; subst result.
    exists property; split; [exact POST |].
    eapply gateway_initialization_id_no_stores; eassumption.
Qed.
