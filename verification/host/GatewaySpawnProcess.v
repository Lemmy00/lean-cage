(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Actual spawn captures its arguments and later exec uses that same birth. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Values Memory Memdata Clight.
From HostGateway Require Import GatewayMachine GatewayRuntime GatewaySpawnABI GatewaySpawnResources GatewaySpawnRuntime
  GatewaySpawnActions GatewaySpawnDescriptors GatewayThreadRuntime GatewayStreamInterface GatewayErrorRuntime.
Import ListNotations.
Open Scope Z_scope.

Fixpoint gateway_spawn_vector_cells memory object offset pointers : Prop :=
  match pointers with
  | [] => Mem.loadv Mptr memory (Vptr object offset) = Some Vnullptr
  | pointer :: rest => Mem.loadv Mptr memory (Vptr object offset) = Some pointer /\
      gateway_spawn_vector_cells memory object (Ptrofs.add offset (Ptrofs.repr 8)) rest
  end.

Definition gateway_spawn_vector memory pointer strings : Prop :=
  exists object offset pointers,
    pointer = Vptr object offset /\
    Ptrofs.unsigned offset + 8 * Z.of_nat (length pointers + 1) <= Ptrofs.modulus /\
    gateway_spawn_vector_cells memory object offset pointers /\
    Forall2 (gateway_error_cstring memory) pointers strings.

Record gateway_child_birth := {
  gateway_child_pid : Z;
  gateway_child_path : list Byte.int;
  gateway_child_arguments : list (list Byte.int);
  gateway_child_environment : list (list Byte.int);
  gateway_child_actions : list gateway_spawn_action;
  gateway_child_attributes : gateway_spawn_attributes;
  gateway_child_inherited : gateway_descriptor_table gateway_open_description
}.

Record gateway_child_exec := {
  gateway_exec_path : list Byte.int;
  gateway_exec_arguments : list (list Byte.int);
  gateway_exec_environment : list (list Byte.int);
  gateway_exec_image_object : nat;
  gateway_exec_descriptors : gateway_descriptor_table gateway_open_description
}.

Definition gateway_exec_from_birth birth execution : Prop :=
  gateway_exec_path execution = gateway_child_path birth /\
  gateway_exec_arguments execution = gateway_child_arguments birth /\
  gateway_exec_environment execution = gateway_child_environment birth /\
  exists prepared,
    gateway_spawn_actions_apply (gateway_child_inherited birth) (gateway_child_actions birth) = Some prepared /\
    gateway_exec_descriptors execution = gateway_descriptor_exec prepared.

Definition gateway_child_history_retained (before after : nat -> option gateway_child_birth) : Prop :=
  forall token birth, before token = Some birth -> after token = Some birth.

(* These are immutable birth histories, not claims that a process is still live. *)
Record gateway_spawn_birth_receipt {World} (resources : World -> gateway_resource_state)
    (births : World -> nat -> option gateway_child_birth) before after path arguments environment actions attributes : Type := {
  gateway_spawned_token : nat;
  gateway_spawned_birth : gateway_child_birth;
  gateway_spawned_token_fresh : births before gateway_spawned_token = None;
  gateway_spawned_recorded : births after gateway_spawned_token = Some gateway_spawned_birth;
  gateway_spawned_pid_width : 0 < gateway_child_pid gateway_spawned_birth <= Int.max_signed;
  gateway_spawned_path : gateway_child_path gateway_spawned_birth = path;
  gateway_spawned_arguments : gateway_child_arguments gateway_spawned_birth = arguments;
  gateway_spawned_environment : gateway_child_environment gateway_spawned_birth = environment;
  gateway_spawned_actions : gateway_child_actions gateway_spawned_birth = actions;
  gateway_spawned_attributes : gateway_child_attributes gateway_spawned_birth = attributes;
  (* The full fork snapshot may differ on unrelated concurrent descriptor slots. *)
  gateway_spawned_inherited : forall fd entry,
    gateway_owned_descriptor (resources before) fd entry ->
    gateway_child_inherited gateway_spawned_birth fd = Some entry
}.

(* Birth/execution views are filtered to this actual source invocation. The
   physical adapter retains all invocation tags in its joint global journal;
   births of other invocations are not excluded from that global history. *)
Record gateway_spawn_process_runtime {World Event} (backend : gateway_backend World Event)
    (io : Event -> option gateway_native_io)
    (native_private : World -> block -> Prop) (stable_readonly : World -> block -> Z -> Prop)
    (discipline : option val -> mem -> World -> Prop) (resources : World -> gateway_resource_state)
    (builders : World -> gateway_spawn_builders) (genuine : mem -> World -> Prop)
    (footprint : World -> block -> Z -> Prop) (births : World -> nat -> option gateway_child_birth)
    (executed : World -> nat -> gateway_child_exec -> Prop) : Prop := {
  (* This is one actual Linux/library exec observation, not an initial safe-channel premise. *)
  gateway_execution_origin : forall world token execution,
    executed world token execution -> exists birth, births world token = Some birth /\ gateway_exec_from_birth birth execution;
  gateway_birth_ambient : forall before world after next,
    gateway_interference backend before world after next ->
    gateway_child_history_retained (births world) (births next);
  gateway_birth_passive : forall definition arguments before world result after next observed,
    gateway_runtime_operation backend definition arguments before world result after next observed ->
    gateway_child_history_retained (births world) (births next);
  gateway_birth_builtin : forall external types arguments before world result after next observed,
    gateway_builtin backend external types arguments before world result after next observed ->
    gateway_child_history_retained (births world) (births next);

  gateway_posix_spawn_operation : forall before world pid_object pid_offset path_pointer path
      actions_pointer actions attributes_pointer attributes arguments_pointer arguments environment_pointer environment
      result after next observed,
    discipline None before world -> genuine before world -> gateway_resource_valid (resources world) ->
    native_private world pid_object -> gateway_native_pointer before pid_object pid_offset 4 Writable ->
    Mem.valid_access before Mint32 pid_object (Ptrofs.unsigned pid_offset) Writable ->
    (forall position, ~ footprint world pid_object position) ->
    gateway_builder_actions (builders world) = Some (actions_pointer, actions) ->
    gateway_builder_attributes (builders world) = Some (attributes_pointer, attributes) ->
    gateway_error_cstring before path_pointer path ->
    gateway_spawn_vector before arguments_pointer arguments ->
    gateway_spawn_vector before environment_pointer environment ->
    gateway_spawn_operation backend gateway_posix_spawn_api
      [Vptr pid_object pid_offset; path_pointer; actions_pointer; attributes_pointer; arguments_pointer; environment_pointer]
      before world result after next observed ->
    discipline None after next /\ genuine after next /\ gateway_resource_valid (resources next) /\
    builders next = builders world /\
    gateway_access_retained native_private stable_readonly before world next /\
    gateway_native_permissions before after pid_object pid_offset 4 /\
    gateway_native_frame native_private stable_readonly (gateway_native_region pid_object pid_offset 4) world before after /\
    gateway_resource_frame (resources world) (resources next) (fun _ => False) (fun _ => False) /\
    gateway_child_history_retained (births world) (births next) /\ io observed = None /\
    exists status (created : option (gateway_spawn_birth_receipt resources births world next path arguments environment actions attributes)),
      result = Vint status /\
      (status = Int.zero -> exists receipt, created = Some receipt /\
        Mem.load Mint32 after pid_object (Ptrofs.unsigned pid_offset) =
          Some (Vint (Int.repr (gateway_child_pid (gateway_spawned_birth _ _ _ _ _ _ _ _ _ receipt))))) /\
      (forall token birth, births next token = Some birth -> births world token = None ->
        exists receipt, created = Some receipt /\ token = gateway_spawned_token _ _ _ _ _ _ _ _ _ receipt)
}.
