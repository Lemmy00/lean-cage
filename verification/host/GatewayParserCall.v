(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The same original successful caller supplies the actual parser run. *)
From Stdlib Require Import List Lia.
From compcert Require Import Integers AST Values Memory Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayResponseParserSource GatewayParserReturn.
Import ListNotations.

Theorem actual_successful_parser_call {World Event}(backend:gateway_backend World Event)ge
    environment temporaries stream before world events value after next:
  value<>Vnullptr->
  gateway_steps backend ge
    (gateway_live(Callstate(Internal f_host_value)(response_parser_arguments stream)
      (response_parser_cont environment temporaries)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists body suffix parsed memory current,
    events=body++suffix /\parsed<>Vnullptr /\
    gateway_steps backend ge
      (gateway_live(Callstate(Internal f_host_value)(response_parser_arguments stream)Kstop before)world)body
      (gateway_live(Returnstate parsed Kstop memory)current) /\
    gateway_steps backend ge
      (gateway_live(Returnstate parsed(response_parser_cont environment temporaries)memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros NONNULL RUN.
  destruct(gateway_return_cut backend ge(Internal f_host_value)(response_parser_arguments stream)
    (response_parser_cont environment temporaries)before world events(Returnstate value Kstop after)next I ltac:(cbn;lia)RUN)
    as(body&suffix&parsed&memory&current&EVENTS&BODY&SUFFIX).
  exists body,suffix,parsed,memory,current;split;[exact EVENTS|]. split.
  - eapply actual_successful_parser_return;[exact NONNULL|exact SUFFIX].
  - split;assumption.
Qed.
