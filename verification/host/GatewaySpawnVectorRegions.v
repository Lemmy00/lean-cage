(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Source allocation keeps launch vectors outside the live SDK struct blocks. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps AST Values Memory Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayStackAllocation GatewayLocalRuntime GatewaySpawnABI
  GatewaySpawnActions GatewaySpawnFrames GatewaySpawnVectorMemory GatewaySpawnVectorStores GatewaySpawnVectorContext.
Import ListNotations.

Theorem actual_spawn_vector_regions {World} (ge : Clight.genv) environment memory world
    (native : World -> block -> Prop) (builders : World -> gateway_spawn_builders)
    blocks symbols actions attributes plan settings :
  gateway_stack_environment memory environment -> gateway_native_environment native world memory environment ->
  gateway_spawn_vector_locations ge environment blocks symbols ->
  environment ! _actions = Some (actions, gateway_actions_type) ->
  environment ! _attributes = Some (attributes, gateway_attributes_type) ->
  gateway_builder_actions (builders world) = Some (Vptr actions Integers.Ptrofs.zero, plan) ->
  gateway_builder_attributes (builders world) = Some (Vptr attributes Integers.Ptrofs.zero, settings) ->
  forall object, gateway_spawn_local_block blocks object ->
    Mem.valid_block memory object /\ native world object /\ gateway_not_builder_block builders world object.
Proof.
  intros [ALIVE DISTINCT] NATIVE
    [CHILD ARGUMENTS ENVIRONMENT ENGINE_LOCAL PATH_LOCAL LOCALE_LOCAL ENGINE PATH LOCALE]
    ACTIONS ATTRIBUTES BUILT_ACTIONS BUILT_ATTRIBUTES
    object LOCAL.
  assert (SOURCE : exists identifier ty, environment ! identifier = Some (object, ty) /\
    identifier <> _actions /\ identifier <> _attributes).
  { destruct LOCAL as [SAME | [SAME | SAME]]; subst object.
    - exists _child, Ctypesdefs.tint; repeat split; assumption || discriminate.
    - exists _arguments; exists (Ctypesdefs.tarray (Ctypesdefs.tptr Ctypesdefs.tschar) 2);
        repeat split; assumption || discriminate.
    - exists _environment; exists (Ctypesdefs.tarray (Ctypesdefs.tptr Ctypesdefs.tschar) 3);
        repeat split; assumption || discriminate. }
  destruct SOURCE as [identifier [ty [LOOK [NOT_ACTIONS NOT_ATTRIBUTES]]]].
  destruct (NATIVE _ _ _ LOOK) as [LIVE PRIVATE]; split; [exact LIVE |]. split; [exact PRIVATE |].
  assert (AWAY_ACTIONS : object <> actions).
  { eapply DISTINCT; [exact LOOK |exact ACTIONS |exact NOT_ACTIONS]. }
  assert (AWAY_ATTRIBUTES : object <> attributes).
  { eapply DISTINCT; [exact LOOK |exact ATTRIBUTES |exact NOT_ATTRIBUTES]. }
  split.
  - intros offset recorded SAME; rewrite BUILT_ACTIONS in SAME; inversion SAME; congruence.
  - intros offset recorded SAME; rewrite BUILT_ATTRIBUTES in SAME; inversion SAME; congruence.
Qed.

Theorem actual_spawn_vector_base {World} (ge : Clight.genv) environment memory world
    (native : World -> block -> Prop) (discipline : option val -> mem -> World -> Prop)
    (builders : World -> gateway_spawn_builders) (genuine : mem -> World -> Prop)
    (state : World -> Prop) blocks symbols actions attributes plan settings :
  discipline None memory world -> genuine memory world -> state world ->
  gateway_stack_environment memory environment -> gateway_native_environment native world memory environment ->
  gateway_spawn_vector_locations ge environment blocks symbols ->
  environment ! _actions = Some (actions, gateway_actions_type) ->
  environment ! _attributes = Some (attributes, gateway_attributes_type) ->
  gateway_builder_actions (builders world) = Some (Vptr actions Integers.Ptrofs.zero, plan) ->
  gateway_builder_attributes (builders world) = Some (Vptr attributes Integers.Ptrofs.zero, settings) ->
  gateway_spawn_vector_base native discipline builders genuine blocks state memory world.
Proof.
  intros SIDE GENUINE STATE STACK NATIVE LOCATIONS ACTIONS ATTRIBUTES BUILT_ACTIONS BUILT_ATTRIBUTES.
  split; [exact SIDE |]. split; [exact GENUINE |]. split; [exact STATE |].
  eapply actual_spawn_vector_regions; eassumption.
Qed.
