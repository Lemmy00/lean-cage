(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A real failed edit skips later setup and reaches original cleanup. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Maps Integers AST Values Memory Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewaySDKEditSource GatewaySDKEditReturn
  GatewayExchangeSetup GatewayMemoryPrefixes GatewayFramedRuntime GatewaySpawnVectors GatewaySpawnVectorMemory
  GatewaySpawnVectorPrefix GatewaySpawnVectorStores GatewayVectorCells GatewayStartedFailure GatewayLaunchPaths GatewayLaunchMemory GatewayLaunchPre.
Import ListNotations.

Theorem actual_sdk_nonzero_skip_suffix {World Event}(backend:gateway_backend World Event)
    property(CLOSED:gateway_ambient_closed backend property)completed environment temporaries memory word:
  temporaries!_setup=Some(Vint word)->Int.eq word Int.zero=false->
  gateway_memory_prefix backend(Clight.globalenv prog)
    (State f_host_exchange spawn_vector_start Kstop environment temporaries memory)property property
    (State f_host_exchange(sdk_edit_after completed)Kstop environment temporaries memory).
Proof.
  intros SETUP NONZERO.
  assert(ONE:forall edit,edit<>gateway_edit_group->
    gateway_memory_prefix backend(Clight.globalenv prog)
      (State f_host_exchange spawn_vector_start Kstop environment temporaries memory)property property
      (State f_host_exchange(sdk_edit_after edit)Kstop environment temporaries memory)->
    gateway_memory_prefix backend(Clight.globalenv prog)
      (State f_host_exchange spawn_vector_start Kstop environment temporaries memory)property property
      (State f_host_exchange(sdk_edit_start edit)Kstop environment temporaries memory)).
  { intros edit GUARDED TAIL;eapply gateway_memory_prefix_compose;
      [eapply actual_sdk_edit_nonzero_skip;[exact CLOSED|exact GUARDED|exact SETUP|exact NONZERO]|exact TAIL]. }
  assert(CLOSE:gateway_memory_prefix backend(Clight.globalenv prog)
    (State f_host_exchange spawn_vector_start Kstop environment temporaries memory)property property
    (State f_host_exchange(sdk_edit_start gateway_edit_closefrom)Kstop environment temporaries memory)).
  { apply ONE;[discriminate|apply gateway_memory_identity]. }
  assert(CANCEL:gateway_memory_prefix backend(Clight.globalenv prog)
    (State f_host_exchange spawn_vector_start Kstop environment temporaries memory)property property
    (State f_host_exchange(sdk_edit_start gateway_edit_cancellation)Kstop environment temporaries memory)).
  { apply ONE;[discriminate|exact CLOSE]. }
  assert(OUTPUT:gateway_memory_prefix backend(Clight.globalenv prog)
    (State f_host_exchange spawn_vector_start Kstop environment temporaries memory)property property
    (State f_host_exchange(sdk_edit_start gateway_edit_output)Kstop environment temporaries memory)).
  { apply ONE;[discriminate|exact CANCEL]. }
  assert(INPUT:gateway_memory_prefix backend(Clight.globalenv prog)
    (State f_host_exchange spawn_vector_start Kstop environment temporaries memory)property property
    (State f_host_exchange(sdk_edit_start gateway_edit_input)Kstop environment temporaries memory)).
  { apply ONE;[discriminate|exact OUTPUT]. }
  assert(FLAGS:gateway_memory_prefix backend(Clight.globalenv prog)
    (State f_host_exchange spawn_vector_start Kstop environment temporaries memory)property property
    (State f_host_exchange(sdk_edit_start gateway_edit_flags)Kstop environment temporaries memory)).
  { apply ONE;[discriminate|exact INPUT]. }
  destruct completed;try assumption;apply gateway_memory_identity.
Qed.

Section Failure.
Context {World Event}(backend:gateway_backend World Event)(environment:env)(temporaries:temp_env)
    (blocks:gateway_spawn_vector_blocks)(symbols:gateway_spawn_vector_symbols)(base:mem->World->Prop).
Hypothesis LOCATIONS:gateway_spawn_vector_locations(Clight.globalenv prog)environment blocks symbols.
Hypothesis DISTINCT:gateway_spawn_blocks_distinct blocks.
Hypothesis AMBIENT:forall before world after next,base before world->
  gateway_interference backend before world after next->base after next /\
  Mem.unchanged_on(gateway_vector_span(gateway_spawn_cell_plan blocks symbols))before after.
Hypothesis STORES:forall before world after cell,base before world->In cell(gateway_spawn_cell_plan blocks symbols)->
  Mem.store(vector_cell_chunk cell)before(vector_cell_block cell)(vector_cell_offset cell)(vector_cell_value cell)=Some after->
  base after world.

Theorem actual_sdk_failed_edit_path target completed allocation_before allocated memory word:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  temporaries!_setup=Some(Vint word)->Int.eq word Int.zero=false->
  gateway_launch_path backend target(gateway_spawn_vector_progress blocks symbols base 0)
    (State f_host_exchange(sdk_edit_after completed)Kstop environment temporaries memory).
Proof.
  intros ALLOC SETUP NONZERO.
  eapply gateway_launch_after_memory_prefix.
  - eapply actual_sdk_nonzero_skip_suffix;[|exact SETUP|exact NONZERO].
    exact(gateway_spawn_progress_ambient backend blocks symbols base AMBIENT 0).
  - eapply gateway_launch_after_memory_prefix.
    + exact(gateway_spawn_vectors_script backend(Clight.globalenv prog)environment temporaries blocks symbols base
        LOCATIONS DISTINCT AMBIENT STORES Kstop memory).
    + eapply gateway_launch_pre;
        [exact(actual_failed_setup_decision_path backend target allocation_before allocated environment temporaries memory word
          ALLOC SETUP NONZERO)|exact(gateway_spawn_progress_ambient backend blocks symbols base AMBIENT 6)|].
      intros;exact I.
Qed.
End Failure.
