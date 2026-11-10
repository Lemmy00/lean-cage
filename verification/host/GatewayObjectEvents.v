(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Observe direct gateway calls without erasing callback effects. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayRuntime GatewayRuntimeABI GatewayRegistry
  GatewayObjects GatewayStreamInterface.
Import ListNotations.

(* This classifier observes the direct primitive call represented by this event.
   It does not classify all I/O inside arbitrary Python callbacks or nested calls. *)
Record gateway_direct_io_projection {World Event}(backend:gateway_backend World Event)
    (io:Event->option gateway_native_io) :Prop:={
  gateway_direct_external_nonio:forall external types result_type convention arguments before world result after next observed,
    gateway_external backend external types result_type convention arguments before world result after next observed ->
    External external types result_type convention<>gateway_receive_definition ->
    External external types result_type convention<>gateway_send_definition ->io observed=None
}.

Theorem gateway_object_api_not_direct_io api definition :
  gateway_object_api_definition api=Some definition ->
  definition<>gateway_receive_definition /\definition<>gateway_send_definition.
Proof.
  destruct api;cbn[gateway_object_api_definition gateway_object_api_ident gateway_program_definition];
    intro DEFINITION;inversion DEFINITION;subst definition;split;discriminate.
Qed.

Theorem gateway_object_operation_direct_event {World Event}(backend:gateway_backend World Event)io
    api arguments before world result after next observed :
  gateway_direct_io_projection backend io ->
  gateway_object_operation backend api arguments before world result after next observed ->io observed=None.
Proof.
  intros PROJECTION[definition[DEFINITION OPERATION]].
  destruct(gateway_object_api_not_direct_io _ _ DEFINITION)as[NOT_RECEIVE NOT_SEND].
  destruct definition;[contradiction|].
  eapply gateway_direct_external_nonio;[exact PROJECTION|exact OPERATION|exact NOT_RECEIVE|exact NOT_SEND].
Qed.

Theorem gateway_object_operation_no_direct_receive {World Event}(backend:gateway_backend World Event)io descriptor
    api arguments before world result after next observed :
  gateway_direct_io_projection backend io ->
  gateway_object_operation backend api arguments before world result after next observed ->
  gateway_received_event io descriptor(gateway_primitive observed)=[].
Proof.
  intros PROJECTION OPERATION;unfold gateway_received_event.
  rewrite(gateway_object_operation_direct_event backend io api arguments before world result after next observed
    PROJECTION OPERATION);reflexivity.
Qed.
