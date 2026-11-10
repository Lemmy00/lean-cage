(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: Real exchange allocation selects its fresh SDK header lifetimes. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Maps AST Values Memory Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayExchangeEntry GatewaySpawnABI GatewaySpawnActions GatewayBuilderScopes
  GatewayBuilderHistory GatewayNativeRoots GatewayLocalRuntime GatewayCallerBuffers GatewayCallerFamily GatewayStackAllocation.
Import ListNotations.

Definition exchange_selected_block(environment:env)(object:block):Prop:=
  exists identifier ty,environment!identifier=Some(object,ty).

Theorem actual_exchange_entry_owns_sdk ge before environment after:
  sizeof ge gateway_actions_type=80%Z->sizeof ge gateway_attributes_type=336%Z->
  exchange_stack_buffers ge before environment after->
  exists actions attributes,
    environment!_actions=Some(actions,gateway_actions_type) /\
    environment!_attributes=Some(attributes,gateway_attributes_type) /\actions<>attributes /\
    ~Mem.valid_block before actions /\~Mem.valid_block before attributes /\
    Mem.range_perm after actions 0 80 Cur Freeable /\Mem.range_perm after attributes 0 336 Cur Freeable.
Proof.
  intros ACTION_SIZE ATTRIBUTE_SIZE[BUFFERS[[LIVE DISTINCT]FRAME]].
  destruct(BUFFERS _actions gateway_actions_type ltac:(cbn;auto 12))as[actions[ACTIONS[FRESH_ACTIONS ACTION_ACCESS]]].
  destruct(BUFFERS _attributes gateway_attributes_type ltac:(cbn;auto 12))as[attributes[ATTRIBUTES[FRESH_ATTRIBUTES ATTR_ACCESS]]].
  exists actions,attributes;split;[exact ACTIONS|]. split;[exact ATTRIBUTES|]. split.
  - eapply DISTINCT;[exact ACTIONS|exact ATTRIBUTES|discriminate].
  - split;[exact FRESH_ACTIONS|]. split;[exact FRESH_ATTRIBUTES|].
    rewrite ACTION_SIZE in ACTION_ACCESS;rewrite ATTRIBUTE_SIZE in ATTR_ACCESS.
    split;assumption.
Qed.

Lemma gateway_caller_readonly_source_frame {World}(native_private:World->block->Prop)
    (stable_readonly:World->block->Z->Prop)readonly before world after:
  gateway_caller_readonly native_private stable_readonly readonly before world->
  Mem.unchanged_on(fun _ _=>True)before after->
  gateway_caller_readonly native_private stable_readonly readonly after world.
Proof.
  intros READONLY FRAME object position HERE.
  destruct(READONLY object position HERE)as[LIVE[PRIVATE|[READABLE STABLE]]];split.
  all:try solve[eapply Mem.valid_block_unchanged_on;eassumption].
  - left;exact PRIVATE.
  - right;split;[eapply Mem.perm_unchanged_on;[exact FRAME|exact I|exact READABLE]|exact STABLE].
Qed.

Theorem actual_exchange_native_family {World}(ge:Clight.genv)
    (native_private:World->block->Prop)(stable_readonly:World->block->Z->Prop)
    before environment allocated world readonly:
  exchange_stack_buffers ge before environment allocated->
  gateway_native_environment native_private world allocated environment->
  gateway_caller_readonly native_private stable_readonly readonly before world->
  gateway_caller_family native_private stable_readonly readonly(exchange_selected_block environment)
    allocated world allocated world.
Proof.
  intros[BUFFERS[STACK FRAME]]NATIVE READONLY;apply gateway_caller_family_refl.
  - intros object[identifier[ty LOOK]];exact(NATIVE identifier object ty LOOK).
  - eapply gateway_caller_readonly_source_frame;[exact READONLY|exact FRAME].
Qed.

Theorem actual_exchange_fresh_sdk_scope {World}(registry:World->gateway_builder_registry)
    (native_private:World->block->Prop)before environment allocated world:
  exchange_stack_buffers(Clight.globalenv prog)before environment allocated->
  gateway_native_environment native_private world allocated environment->
  gateway_builder_registry_allocated before(registry world)->
  exists actions attributes,
    environment!_actions=Some(actions,gateway_actions_type) /\
    environment!_attributes=Some(attributes,gateway_attributes_type) /\actions<>attributes /\
    gateway_builder_headers native_private actions attributes allocated world /\
    gateway_builder_actions(gateway_scoped_builders registry actions attributes world)=None /\
    gateway_builder_attributes(gateway_scoped_builders registry actions attributes world)=None /\
    Mem.range_perm allocated actions 0 80 Cur Freeable /\Mem.range_perm allocated attributes 0 336 Cur Freeable.
Proof.
  intros STACK NATIVE REGISTRY.
  destruct(actual_exchange_entry_owns_sdk(Clight.globalenv prog)before environment allocated
    (proj1 actual_gateway_spawn_layout)(proj2 actual_gateway_spawn_layout)STACK)
    as(actions&attributes&ACTIONS&ATTRIBUTES&DISTINCT&FRESH_ACTIONS&FRESH_ATTRIBUTES&ACTION_ACCESS&ATTR_ACCESS).
  destruct(gateway_fresh_builder_scope_empty registry world before actions attributes REGISTRY FRESH_ACTIONS FRESH_ATTRIBUTES)
    as[EMPTY_ACTIONS EMPTY_ATTRIBUTES].
  exists actions,attributes;split;[exact ACTIONS|]. split;[exact ATTRIBUTES|]. split;[exact DISTINCT|]. split.
  - intros object MEMBER;cbn in MEMBER;destruct MEMBER as[SAME|[SAME|FALSE]];try contradiction;subst object.
    + exact(NATIVE _ _ _ ACTIONS).
    + exact(NATIVE _ _ _ ATTRIBUTES).
  - split;[exact EMPTY_ACTIONS|]. split;[exact EMPTY_ATTRIBUTES|]. split;assumption.
Qed.
