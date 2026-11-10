(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Each libc action/attribute call updates the same real SDK object. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewayRuntime GatewaySpawnABI GatewaySpawnResources GatewaySpawnRuntime
  GatewaySpawnDescriptors GatewayThreadRuntime GatewayStreamInterface.
Import ListNotations.
Open Scope Z_scope.

Record gateway_spawn_attributes := {
  gateway_attribute_flags : int;
  gateway_attribute_group : int
}.
Record gateway_spawn_builders := {
  gateway_builder_actions : option (val * list gateway_spawn_action);
  gateway_builder_attributes : option (val * gateway_spawn_attributes)
}.
Definition gateway_with_actions state value :=
  {| gateway_builder_actions := value; gateway_builder_attributes := gateway_builder_attributes state |}.
Definition gateway_with_attributes state value :=
  {| gateway_builder_actions := gateway_builder_actions state; gateway_builder_attributes := value |}.
Definition gateway_default_attributes := {| gateway_attribute_flags := Int.zero; gateway_attribute_group := Int.zero |}.

Inductive gateway_action_request :=
  | gateway_add_dup (source target : Z) | gateway_add_closefrom (lower : Z).
Definition gateway_action_request_api request := match request with
  | gateway_add_dup _ _ => gateway_actions_dup_api | gateway_add_closefrom _ => gateway_actions_closefrom_api end.
Definition gateway_action_request_arguments request pointer := match request with
  | gateway_add_dup source target => [pointer; Vint (Int.repr source); Vint (Int.repr target)]
  | gateway_add_closefrom lower => [pointer; Vint (Int.repr lower)] end.
Definition gateway_action_request_value request := match request with
  | gateway_add_dup source target => gateway_spawn_dup source target
  | gateway_add_closefrom lower => gateway_spawn_closefrom lower end.
Definition gateway_action_request_valid request : Prop := match request with
  | gateway_add_dup source target => 0 <= source <= Int.max_signed /\ 0 <= target <= Int.max_signed
  | gateway_add_closefrom lower => 0 <= lower <= Int.max_signed end.

Inductive gateway_attribute_request := gateway_set_group (group : int) | gateway_set_spawn_flags (flags : int).
Definition gateway_attribute_request_api request := match request with
  | gateway_set_group _ => gateway_attributes_group_api | gateway_set_spawn_flags _ => gateway_attributes_flags_api end.
Definition gateway_attribute_request_arguments request pointer := match request with
  | gateway_set_group group => [pointer; Vint group] | gateway_set_spawn_flags flags => [pointer; Vint flags] end.
Definition gateway_attribute_request_value request before := match request with
  | gateway_set_group group => {| gateway_attribute_flags := gateway_attribute_flags before; gateway_attribute_group := group |}
  | gateway_set_spawn_flags flags => {| gateway_attribute_flags := flags; gateway_attribute_group := gateway_attribute_group before |}
  end.
Definition gateway_attribute_request_valid request : Prop := match request with
  | gateway_set_group group => 0 <= Int.signed group
  | gateway_set_spawn_flags flags => Int.sign_ext 16 flags = flags end.

Definition gateway_builder_mutation definition : Prop :=
  exists api, In api [gateway_actions_init_api; gateway_actions_destroy_api; gateway_actions_dup_api;
    gateway_actions_closefrom_api; gateway_attributes_init_api; gateway_attributes_destroy_api;
    gateway_attributes_group_api; gateway_attributes_flags_api] /\ gateway_spawn_definition api = Some definition.

Definition gateway_builder_unexposed (footprint : block -> Z -> Prop) (arguments : list val) : Prop :=
  forall object offset, In (Vptr object offset) arguments -> forall position, ~ footprint object position.

Section BuilderPost.
Context {World Event} (backend : gateway_backend World Event) (io : Event -> option gateway_native_io)
    (native_private : World -> block -> Prop) (stable_readonly : World -> block -> Z -> Prop)
    (discipline : option val -> mem -> World -> Prop) (resources : World -> gateway_resource_state)
    (genuine : mem -> World -> Prop).
Definition gateway_builder_post before world after next observed object offset width : Prop :=
  discipline None after next /\ genuine after next /\ gateway_resource_valid (resources next) /\
  gateway_access_retained native_private stable_readonly before world next /\
  gateway_native_permissions before after object offset width /\
  gateway_native_frame native_private stable_readonly (gateway_native_region object offset width) world before after /\
  gateway_resource_frame (resources world) (resources next) (fun _ => False) (fun _ => False) /\
  gateway_resource_status_frame (resources world) (resources next) (fun _ => False) /\
  gateway_exclusive_kept (resources world) (resources next) /\ io observed = None.
End BuilderPost.

(* The representation predicate covers the actual initialized SDK structs and
   their library-owned allocation footprints. Source stores must preserve that
   footprint, rather than assuming that any native store preserves SDK state. *)
Record gateway_spawn_builder_runtime {World Event} (backend : gateway_backend World Event)
    (io : Event -> option gateway_native_io)
    (native_private : World -> block -> Prop) (stable_readonly : World -> block -> Z -> Prop)
    (discipline : option val -> mem -> World -> Prop) (resources : World -> gateway_resource_state)
    (builders : World -> gateway_spawn_builders) (genuine : mem -> World -> Prop)
    (footprint : World -> block -> Z -> Prop) : Prop := {
  gateway_builder_empty : forall memory world,
    gateway_builder_actions (builders world) = None -> gateway_builder_attributes (builders world) = None -> genuine memory world;
  gateway_builder_representation_frame : forall before after world,
    genuine before world -> Mem.unchanged_on (footprint world) before after -> genuine after world;
  gateway_builder_footprint_live : forall memory world object position,
    genuine memory world -> footprint world object position -> Mem.valid_block memory object;
  gateway_builder_native_footprint : forall memory world object position,
    genuine memory world -> native_private world object -> footprint world object position ->
    (exists offset actions, gateway_builder_actions (builders world) = Some (Vptr object offset, actions)) \/
    (exists offset attributes, gateway_builder_attributes (builders world) = Some (Vptr object offset, attributes));
  gateway_builder_ambient : forall before world after next,
    discipline None before world -> genuine before world -> gateway_interference backend before world after next ->
    builders next = builders world /\ genuine after next;
  gateway_builder_passive : forall definition arguments before world result after next observed,
    discipline None before world -> ~ gateway_builder_mutation definition ->
    gateway_runtime_operation backend definition arguments before world result after next observed ->
    builders next = builders world;
  (* An unrelated SDK operation receives none of this invocation's private SDK
     representation. Native stores/frees use the separate representation frame;
     posix_spawn intentionally receives the structs and has its own precise law. *)
  gateway_builder_unexposed_operation : forall definition arguments before world result after next observed,
    discipline None before world -> genuine before world -> ~ gateway_builder_mutation definition ->
    gateway_builder_unexposed (footprint world) arguments ->
    gateway_runtime_operation backend definition arguments before world result after next observed ->
    genuine after next;

  gateway_actions_append : forall request before world object offset actions result after next observed,
    discipline None before world -> genuine before world -> gateway_resource_valid (resources world) ->
    native_private world object -> gateway_native_pointer before object offset 80 Writable ->
    offset = Ptrofs.zero ->
    gateway_builder_actions (builders world) = Some (Vptr object offset, actions) -> gateway_action_request_valid request ->
    gateway_spawn_operation backend (gateway_action_request_api request)
      (gateway_action_request_arguments request (Vptr object offset)) before world result after next observed ->
    gateway_builder_post io native_private stable_readonly discipline resources genuine
      before world after next observed object offset 80 /\
    exists status, result = Vint status /\ builders next = gateway_with_actions (builders world)
      (Some (Vptr object offset, if Int.eq status Int.zero then actions ++ [gateway_action_request_value request] else actions));

  gateway_attributes_update : forall request before world object offset attributes result after next observed,
    discipline None before world -> genuine before world -> gateway_resource_valid (resources world) ->
    native_private world object -> gateway_native_pointer before object offset 336 Writable ->
    offset = Ptrofs.zero ->
    gateway_builder_attributes (builders world) = Some (Vptr object offset, attributes) -> gateway_attribute_request_valid request ->
    gateway_spawn_operation backend (gateway_attribute_request_api request)
      (gateway_attribute_request_arguments request (Vptr object offset)) before world result after next observed ->
    gateway_builder_post io native_private stable_readonly discipline resources genuine
      before world after next observed object offset 336 /\
    exists status, result = Vint status /\ builders next = gateway_with_attributes (builders world)
      (Some (Vptr object offset, if Int.eq status Int.zero then gateway_attribute_request_value request attributes else attributes));

  gateway_actions_release : forall before world object offset actions result after next observed,
    discipline None before world -> genuine before world -> gateway_resource_valid (resources world) ->
    native_private world object -> gateway_native_pointer before object offset 80 Writable ->
    offset = Ptrofs.zero ->
    gateway_builder_actions (builders world) = Some (Vptr object offset, actions) ->
    gateway_spawn_operation backend gateway_actions_destroy_api [Vptr object offset] before world result after next observed ->
    gateway_builder_post io native_private stable_readonly discipline resources genuine
      before world after next observed object offset 80 /\ result = Vint Int.zero /\
    builders next = gateway_with_actions (builders world) None;

  gateway_attributes_release : forall before world object offset attributes result after next observed,
    discipline None before world -> genuine before world -> gateway_resource_valid (resources world) ->
    native_private world object -> gateway_native_pointer before object offset 336 Writable ->
    offset = Ptrofs.zero ->
    gateway_builder_attributes (builders world) = Some (Vptr object offset, attributes) ->
    gateway_spawn_operation backend gateway_attributes_destroy_api [Vptr object offset] before world result after next observed ->
    gateway_builder_post io native_private stable_readonly discipline resources genuine
      before world after next observed object offset 336 /\ result = Vint Int.zero /\
    builders next = gateway_with_attributes (builders world) None
}.

(* An invocation selects actual separately allocated struct roots before these
   calls. A scoped registry view is not a model for initialization at every
   unrelated native address. Source offset zero supplies the supported ABI
   alignment; other pointers remain unrestricted in the broad machine. *)
Record gateway_spawn_initializer_runtime {World Event} (backend : gateway_backend World Event)
    (io : Event -> option gateway_native_io)
    (native_private : World -> block -> Prop) (stable_readonly : World -> block -> Z -> Prop)
    (discipline : option val -> mem -> World -> Prop) (resources : World -> gateway_resource_state)
    (builders : World -> gateway_spawn_builders) (genuine : mem -> World -> Prop)
    (footprint : World -> block -> Z -> Prop) (actions attributes : block) : Prop := {
  gateway_actions_initialize : forall before world result after next observed,
    discipline None before world -> genuine before world -> gateway_resource_valid (resources world) ->
    gateway_builder_actions (builders world) = None -> native_private world actions ->
    gateway_native_pointer before actions Ptrofs.zero 80 Writable ->
    (forall position, ~ footprint world actions position) ->
    gateway_spawn_operation backend gateway_actions_init_api [Vptr actions Ptrofs.zero]
      before world result after next observed ->
    gateway_builder_post io native_private stable_readonly discipline resources genuine
      before world after next observed actions Ptrofs.zero 80 /\
    exists status, result = Vint status /\ builders next = gateway_with_actions (builders world)
      (if Int.eq status Int.zero then Some (Vptr actions Ptrofs.zero, []) else None);
  gateway_attributes_initialize : forall before world result after next observed,
    discipline None before world -> genuine before world -> gateway_resource_valid (resources world) ->
    gateway_builder_attributes (builders world) = None -> native_private world attributes ->
    gateway_native_pointer before attributes Ptrofs.zero 336 Writable ->
    (forall position, ~ footprint world attributes position) ->
    gateway_spawn_operation backend gateway_attributes_init_api [Vptr attributes Ptrofs.zero]
      before world result after next observed ->
    gateway_builder_post io native_private stable_readonly discipline resources genuine
      before world after next observed attributes Ptrofs.zero 336 /\
    exists status, result = Vint status /\ builders next = gateway_with_attributes (builders world)
      (if Int.eq status Int.zero then Some (Vptr attributes Ptrofs.zero, gateway_default_attributes) else None)
}.
