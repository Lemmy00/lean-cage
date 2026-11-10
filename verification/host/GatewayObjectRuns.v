(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Actual direct object-call traces contain no direct gateway receive. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayRegistry GatewayMachine GatewayContexts GatewayOperations GatewayReadonly GatewayPathEvents
  GatewayObjects GatewayObjectEvents GatewayStreamInterface.
Import ListNotations.

Lemma gateway_pending_received_empty {Event}(io:Event->option gateway_native_io)descriptor events :
  Forall gateway_pending_event events ->gateway_received_bytes io descriptor events=[].
Proof.
  intro PENDING;induction PENDING;[reflexivity|].
  destruct H as[SAME|SAME];subst x;cbn[gateway_received_bytes gateway_received_event flat_map];exact IHPENDING.
Qed.

Theorem gateway_object_run_no_direct_receive {World Event}(backend:gateway_backend World Event)ge io
    api definition arguments before world events returned after next descriptor :
  gateway_direct_io_projection backend io ->gateway_object_api_definition api=Some definition ->
  gateway_steps backend ge(gateway_live(Callstate definition arguments Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->gateway_received_bytes io descriptor events=[].
Proof.
  intros PROJECTION DEFINITION RUN.
  pose proof DEFINITION as EXTERNAL;unfold gateway_object_api_definition in EXTERNAL.
  destruct(gateway_program_definition(gateway_object_api_ident api)global_definitions)as[global|]eqn:GLOBAL;
    [|discriminate].
  destruct global as[function|variable];[|discriminate].
  destruct function as[function|external types result_type convention];[discriminate|].
  inversion EXTERNAL;subst definition.
  destruct(gateway_external_operation_of_run backend ge _ _ _ _ _ _ _ _ _ _ _ RUN)
    as(prefix &suffix &called &called_world &changed &changed_world &observed &EVENTS &PENDING &PREFIX &OPERATION &SUFFIX).
  assert(NONIO:io observed=None)by
    (eapply gateway_object_operation_direct_event with(api:=api);[exact PROJECTION|];
      eexists;split;[exact DEFINITION|exact OPERATION]).
  assert(QUIET:Forall gateway_quiet_event suffix)by
    (eapply(gateway_readonly_run_events backend ge(Returnstate returned Kstop changed)changed_world suffix returned after next);
      [exact I|exact SUFFIX]).
  rewrite EVENTS,gateway_received_append,(gateway_pending_received_empty io descriptor prefix PENDING).
  change(gateway_received_event io descriptor(gateway_primitive observed)++gateway_received_bytes io descriptor suffix=[]).
  unfold gateway_received_event;rewrite NONIO,(gateway_quiet_received io descriptor suffix QUIET);reflexivity.
Qed.
