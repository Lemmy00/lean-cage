(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The real caller's stored vectors and SDK objects reach the same spawn call. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayMemoryPrefixes GatewayFramedRuntime
  GatewaySpawnABI GatewaySpawnActions GatewaySpawnResources GatewayThreadRuntime GatewaySpawnVectorContext
  GatewaySpawnVectorMemory GatewaySpawnVectorPrefix GatewaySpawnVectors GatewaySpawnVectorStores GatewaySpawnCall GatewayVectorCells
  GatewayReadonly.
Import ListNotations.
Open Scope Z_scope.

Section LaunchPrefix.
Context {World Event} (backend : gateway_backend World Event) io native stable discipline thread_errno resources
  builders genuine footprint
  (thread : gateway_thread_runtime backend io native stable discipline thread_errno)
  (sdk : gateway_spawn_builder_runtime backend io native stable discipline resources builders genuine footprint).
Variables (ge : Clight.genv) (environment : env) (temporaries : temp_env)
  (blocks : gateway_spawn_vector_blocks) (symbols : gateway_spawn_vector_symbols) (state : World -> Prop).
Hypothesis STATE_AMBIENT : forall before world after next,
  discipline None before world -> state world -> gateway_interference backend before world after next -> state next.
Local Definition base := gateway_spawn_vector_base native discipline builders genuine blocks state.
Local Definition progress := gateway_spawn_vector_progress blocks symbols base.

Theorem actual_sdk_launch_argument_prefix actions attributes continuation before world events terminal next symbol :
  gateway_spawn_vector_locations ge environment blocks symbols -> gateway_spawn_blocks_distinct blocks ->
  environment ! _actions = Some (actions, gateway_actions_type) ->
  environment ! _attributes = Some (attributes, gateway_attributes_type) -> environment ! _posix_spawn = None ->
  Genv.find_symbol ge _posix_spawn = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some (gateway_spawn_signature gateway_posix_spawn_api) ->
  temporaries ! _setup = Some (Vint Int.zero) -> gateway_instruction_boundary terminal ->
  base before world -> Forall (gateway_vector_writable before) (gateway_spawn_cell_plan blocks symbols) ->
  gateway_steps backend ge
    (gateway_live (State f_host_exchange spawn_vector_start continuation environment temporaries before) world)
    events (gateway_live terminal next) ->
  exists prefix suffix memory current,
    events = prefix ++ suffix /\ Forall gateway_quiet_event prefix /\
    gateway_steps backend ge
      (gateway_live (State f_host_exchange spawn_vector_start continuation environment temporaries before) world) prefix
      (gateway_live (Callstate (gateway_spawn_signature gateway_posix_spawn_api)
        (gateway_spawn_call_values blocks symbols actions attributes)
        (gateway_spawn_call_cont environment temporaries continuation) memory) current) /\
    base memory current /\
    Forall (gateway_vector_writable memory) (gateway_spawn_cell_plan blocks symbols) /\
    Forall (gateway_vector_loaded memory) (gateway_spawn_cell_plan blocks symbols) /\
    gateway_steps backend ge
      (gateway_live (Callstate (gateway_spawn_signature gateway_posix_spawn_api)
        (gateway_spawn_call_values blocks symbols actions attributes)
        (gateway_spawn_call_cont environment temporaries continuation) memory) current)
      suffix (gateway_live terminal next).
Proof.
  intros LOCATIONS DISTINCT ACTIONS ATTRIBUTES NOT_LOCAL SYMBOL FUNCTION SETUP BOUNDARY BASE ACCESS RUN.
  assert (AMBIENT : forall before world after next, base before world ->
    gateway_interference backend before world after next -> base after next /\
    Mem.unchanged_on (gateway_vector_span (gateway_spawn_cell_plan blocks symbols)) before after).
  { exact (gateway_spawn_base_ambient backend io native stable discipline thread_errno resources builders genuine footprint
      thread sdk blocks state STATE_AMBIENT symbols). }
  assert (STORES : forall before world after cell, base before world -> In cell (gateway_spawn_cell_plan blocks symbols) ->
    Mem.store (vector_cell_chunk cell) before (vector_cell_block cell) (vector_cell_offset cell)
      (vector_cell_value cell) = Some after -> base after world).
  { exact (gateway_spawn_base_store backend io native stable discipline thread_errno resources builders genuine footprint
      thread sdk blocks state symbols). }
  pose proof (gateway_spawn_vectors_script backend ge environment temporaries blocks symbols base LOCATIONS DISTINCT
    AMBIENT STORES continuation before) as VECTORS.
  assert (CALL : gateway_memory_prefix backend ge
    (Callstate (gateway_spawn_signature gateway_posix_spawn_api) (gateway_spawn_call_values blocks symbols actions attributes)
      (gateway_spawn_call_cont environment temporaries continuation) before)
    (progress 6) (progress 6)
    (State f_host_exchange (spawn_vector_after 6) continuation environment temporaries before)).
  { eapply actual_spawn_selected_script; try eassumption.
    exact (gateway_spawn_progress_ambient backend blocks symbols base AMBIENT 6). }
  pose proof (gateway_memory_prefix_compose backend ge _ _ _ _ _ _ VECTORS CALL) as SCRIPT.
  destruct (gateway_memory_prefix_cut backend ge _ _ _ _ before world events terminal next SCRIPT BOUNDARY
    ltac:(split; [exact BASE |split; [exact ACCESS |constructor]]) RUN)
    as (prefix & suffix & memory & current & EVENTS & QUIET & PREFIX & [FINAL [WRITABLE LOADED]] & SUFFIX).
  change (Forall (gateway_vector_loaded memory) (gateway_spawn_cell_plan blocks symbols)) in LOADED.
  exists prefix, suffix, memory, current.
  split; [exact EVENTS |]. split; [exact QUIET |]. split; [exact PREFIX |].
  split; [exact FINAL |]. split; [exact WRITABLE |]. split; [exact LOADED |exact SUFFIX].
Qed.
End LaunchPrefix.
