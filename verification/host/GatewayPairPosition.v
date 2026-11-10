(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Source pair births retain their actual ordered event indices. *)
From Stdlib Require Import List Lia.
From compcert Require Import Integers AST Values Memory Events Ctypes Clight.
Require Import CallContexts.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewaySpawnABI GatewaySpawnResources
  GatewaySpawnRuntime GatewayPairContext GatewayPairSource GatewayExchangePairContext GatewayPairOccurrence.
Import ListNotations.

Definition gateway_source_pair_at {World Event}(backend:gateway_backend World Event)
    (resources:World->gateway_resource_state)ipc object source world events(identity:gateway_pair_identity ipc)ordinal:Prop:=
  exists prefix suffix continuation called call_world born born_world observed
    (receipt:gateway_socketpair_receipt ipc(resources call_world)(resources born_world)),
    identity=gateway_pair_receipt_identity ipc(resources call_world)(resources born_world)receipt /\
    length prefix=ordinal /\events=prefix++gateway_primitive observed::suffix /\
    gateway_steps backend(Clight.globalenv prog)(gateway_live source world)prefix
      (gateway_live(Callstate(gateway_spawn_signature gateway_socketpair_api)(pair_socket_arguments object Ptrofs.zero)
        continuation called)call_world) /\
    gateway_spawn_operation backend gateway_socketpair_api(pair_socket_arguments object Ptrofs.zero)
      called call_world(Vint Int.zero)born born_world observed.

Lemma gateway_source_pair_at_forget {World Event}(backend:gateway_backend World Event)resources ipc
    object source world events identity ordinal:
  gateway_source_pair_at backend resources ipc object source world events identity ordinal->
  gateway_source_pair_birth backend resources ipc object source world events identity.
Proof.
  intros(prefix&suffix&continuation&called&call_world&born&born_world&observed&receipt&IDENTITY&INDEX&EVENTS&PREFIX&OPERATION).
  exists prefix,suffix,continuation,called,call_world,born,born_world,observed,receipt.
  split;[exact IDENTITY|]. split;[exact EVENTS|]. split;assumption.
Qed.

Theorem gateway_pair_positioned_in_caller {World Event}(backend:gateway_backend World Event)resources ipc
    object source world prefix helper_events suffix continuation before called_world after next identity events:
  is_call_cont continuation->events=prefix++helper_events++suffix->
  gateway_steps backend(Clight.globalenv prog)(gateway_live source world)prefix
    (gateway_live(Callstate(Internal f_host_private_pair)[Vptr object Ptrofs.zero]continuation before)called_world)->
  gateway_pair_birth_in_run backend resources ipc object before called_world helper_events after next identity->
  exists ordinal,(length prefix<=ordinal<length prefix+length helper_events)%nat /\
    gateway_source_pair_at backend resources ipc object source world events identity ordinal.
Proof.
  intros CONTINUATION EVENTS PREFIX
    (local_prefix&local_suffix&called&call_world&born&born_world&observed&receipt&IDENTITY&LOCAL_EVENTS&LOCAL_PREFIX&OPERATION&REST).
  exists(length prefix+length local_prefix)%nat;split.
  - rewrite LOCAL_EVENTS,app_length;cbn;lia.
  - exists(prefix++local_prefix),(local_suffix++suffix),
      (plug_cont(pair_socket_cont(Vptr object Ptrofs.zero))continuation),called,call_world,born,born_world,observed,receipt.
    split;[exact IDENTITY|]. split;[apply app_length|]. split.
    + rewrite EVENTS,LOCAL_EVENTS;repeat rewrite <-app_assoc;reflexivity.
    + split;[|exact OPERATION]. eapply gateway_steps_append;[exact PREFIX|].
      exact(gateway_plug_steps backend(Clight.globalenv prog)_ _ _ continuation CONTINUATION LOCAL_PREFIX).
Qed.

Definition gateway_source_pairs_ordered {World Event}(backend:gateway_backend World Event)resources ipc
    data control source world events(data_identity control_identity:gateway_pair_identity ipc):Prop:=
  exists data_ordinal control_ordinal,(data_ordinal<control_ordinal)%nat /\
    gateway_source_pair_at backend resources ipc data source world events data_identity data_ordinal /\
    gateway_source_pair_at backend resources ipc control source world events control_identity control_ordinal.
