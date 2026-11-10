(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: Pair occurrences keep their actual index in the whole caller run. *)
From Stdlib Require Import List Lia.
From compcert Require Import AST Values Memory Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPairContext GatewayPairPosition
  GatewayExchangeEntryPrepared GatewayExchangePrepared.
Import ListNotations.

Theorem gateway_source_pair_at_prefix {World Event}(backend:gateway_backend World Event)resources ipc
    object source world prefix middle current events identity ordinal:
  gateway_steps backend(Clight.globalenv prog)(gateway_live source world)prefix(gateway_live middle current)->
  gateway_source_pair_at backend resources ipc object middle current events identity ordinal->
  gateway_source_pair_at backend resources ipc object source world(prefix++events)identity(length prefix+ordinal).
Proof.
  intros PREFIX(local_prefix & suffix & continuation & called & call_world & born & born_world & observed & receipt &
    IDENTITY & INDEX & EVENTS & SELECTED & OPERATION).
  exists(prefix++local_prefix),suffix,continuation,called,call_world,born,born_world,observed,receipt.
  split;[exact IDENTITY|]. split;[rewrite length_app,INDEX;reflexivity|]. split.
  - rewrite EVENTS,app_assoc;reflexivity.
  - split;[eapply gateway_steps_append;[exact PREFIX|exact SELECTED]|exact OPERATION].
Qed.

Theorem gateway_source_pairs_ordered_prefix {World Event}(backend:gateway_backend World Event)resources ipc
    data control source world prefix middle current events data_identity control_identity:
  gateway_steps backend(Clight.globalenv prog)(gateway_live source world)prefix(gateway_live middle current)->
  gateway_source_pairs_ordered backend resources ipc data control middle current events data_identity control_identity->
  gateway_source_pairs_ordered backend resources ipc data control source world(prefix++events)data_identity control_identity.
Proof.
  intros PREFIX(data_ordinal & control_ordinal & BEFORE & DATA & CONTROL).
  exists(length prefix+data_ordinal),(length prefix+control_ordinal);split;[lia|]. split;
    eapply gateway_source_pair_at_prefix;[exact PREFIX|exact DATA|exact PREFIX|exact CONTROL].
Qed.

Theorem actual_exchange_entry_pair_occurrences {World Event}(backend:gateway_backend World Event)
    native stable discipline resources ipc builders genuine readonly reference owner environment temporaries
    data control actions attributes blocks symbols before world events target_arguments target_continuation target_memory target_world:
  gateway_exchange_entry_frontier backend native stable discipline resources ipc builders genuine readonly reference owner
    environment temporaries data control actions attributes blocks symbols before world events
    target_arguments target_continuation target_memory target_world->
  exists(data_identity control_identity:gateway_pair_identity ipc),
    gateway_source_pairs_ordered backend resources ipc data control
      (State f_host_exchange(fn_body f_host_exchange)Kstop environment temporaries before)world events data_identity control_identity /\
    pair_right_object ipc data_identity<>pair_right_object ipc control_identity.
Proof.
  intros[value prefix body_events memory current EVENTS QUIET PREFIX BODY].
  destruct BODY as[began flags data_identity control_identity data_left data_right control_left control_right
    source_prefix source_suffix source_memory source_world BODY_EVENTS ORDER SEPARATE DL DR CL CR SOURCE CONTEXT VECTORS TAIL].
  exists data_identity,control_identity;split;[|exact SEPARATE].
  rewrite EVENTS;eapply gateway_source_pairs_ordered_prefix;[exact PREFIX|exact ORDER].
Qed.
