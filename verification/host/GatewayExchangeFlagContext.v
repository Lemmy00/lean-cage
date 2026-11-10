(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: Individual flag operations retain the two actual connection owners. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewayThreadRuntime GatewayStreamInterface GatewayOperations
  GatewayCallerBuffers GatewayCallerFamily GatewaySpawnABI GatewaySpawnRuntime GatewaySpawnResources GatewayPairContext
  GatewayConnectionResources GatewayPairHistory GatewayExchangeContext GatewayCallerClockResources.
Import ListNotations.
Open Scope Z_scope.

Section FlagContext.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
    (native:World->block->Prop)(stable:World->block->Z->Prop)(discipline:option val->mem->World->Prop)
    (thread_errno:World->int)(resources:World->gateway_resource_state)(ipc:nat->Prop).
Context(thread:gateway_thread_runtime backend io native stable discipline thread_errno)
    (descriptors:gateway_spawn_descriptor_runtime backend io native stable discipline resources ipc).
Variables(readonly:block->Z->Prop)(selected:block->Prop)(reference:mem)(owner:World)(original:gateway_resource_state)
    (data_identity control_identity:gateway_pair_identity ipc)(data control:block)
    (data_left data_right control_left control_right:Z).
Hypotheses(DATA_SELECTED:selected data)(CONTROL_SELECTED:selected control).

Definition gateway_flag_context left_mode right_mode memory world:Prop:=
  discipline None memory world /\
  gateway_caller_family native stable readonly selected reference owner memory world /\
  gateway_resource_valid(resources world) /\
  gateway_pair_leases ipc data_identity data_left data_right(resources world) /\
  gateway_pair_leases ipc control_identity control_left control_right(resources world) /\
  gateway_pair_modes ipc data_identity left_mode right_mode(resources world) /\
  gateway_pair_cells memory data Ptrofs.zero data_left data_right /\
  gateway_pair_cells memory control Ptrofs.zero control_left control_right /\
  (forall fd entry,gateway_owned_descriptor original fd entry->gateway_owned_descriptor(resources world)fd entry).

Theorem gateway_flag_context_from_pairs memory world:
  gateway_pair_context native discipline resources ipc data_identity data Ptrofs.zero data_left data_right memory world->
  gateway_pair_context native discipline resources ipc control_identity control Ptrofs.zero control_left control_right memory world->
  gateway_exchange_context native stable discipline resources readonly selected reference owner original memory world->
  gateway_flag_context true true memory world.
Proof.
  intros[DATA_SIDE[DATA_PRIVATE[DATA_CELLS DATA_RESOURCES]]]
    [CONTROL_SIDE[CONTROL_PRIVATE[CONTROL_CELLS CONTROL_RESOURCES]]][SIDE[[VALID ORIGINAL]FAMILY]].
  split;[exact SIDE|]. split;[exact FAMILY|]. split;[exact VALID|].
  split;[apply gateway_pair_resources_leases;exact DATA_RESOURCES|].
  split;[apply gateway_pair_resources_leases;exact CONTROL_RESOURCES|].
  split;[exact(gateway_pair_resources_modes ipc data_identity data_left data_right(resources world)DATA_RESOURCES)|].
  split;[exact DATA_CELLS|]. split;[exact CONTROL_CELLS|exact(proj1 ORIGINAL)].
Qed.

Lemma gateway_flag_context_preserved left_mode right_mode after_left after_right before world after next:
  gateway_flag_context left_mode right_mode before world->discipline None after next->
  gateway_access_retained native stable before world next->
  gateway_native_frame native stable gateway_native_no_output world before after->
  gateway_resource_valid(resources next)->
  gateway_resource_frame(resources world)(resources next)(fun _=>False)(fun _=>False)->
  gateway_exclusive_kept(resources world)(resources next)->
  gateway_pair_modes ipc data_identity after_left after_right(resources next)->
  gateway_flag_context after_left after_right after next.
Proof.
  intros[SIDE[FAMILY[VALID[DATA[CONTROL[MODES[DATA_CELLS[CONTROL_CELLS ORIGINAL]]]]]]]]
    NORMAL ACCESS MEMORY AFTER FRAME EXCLUSIVE NEW_MODES.
  split;[exact NORMAL|]. split.
  - intros target SELECTED;eapply gateway_caller_buffers_no_output;[exact(FAMILY target SELECTED)|exact ACCESS|exact MEMORY].
  - split;[exact AFTER|]. split;[eapply gateway_pair_leases_frame;[exact VALID|exact DATA|exact FRAME|exact EXCLUSIVE]|].
    split;[eapply gateway_pair_leases_frame;[exact VALID|exact CONTROL|exact FRAME|exact EXCLUSIVE]|].
    split;[exact NEW_MODES|]. split.
    + eapply gateway_pair_cells_unchanged;[exact DATA_CELLS|].
      eapply gateway_native_frame_restrict;[exact MEMORY| |intros;tauto].
      intros object position[SAME RANGE];subst object;left;exact(proj1(proj2(FAMILY data DATA_SELECTED))).
    + split.
      * eapply gateway_pair_cells_unchanged;[exact CONTROL_CELLS|].
        eapply gateway_native_frame_restrict;[exact MEMORY| |intros;tauto].
        intros object position[SAME RANGE];subst object;left;exact(proj1(proj2(FAMILY control CONTROL_SELECTED))).
      * intros fd entry OLD;eapply(proj1 FRAME);[apply ORIGINAL;exact OLD|tauto].
Qed.

Lemma gateway_flag_context_observer left_mode right_mode before world after next:
  gateway_flag_context left_mode right_mode before world->discipline None after next->
  gateway_access_retained native stable before world next->
  gateway_native_frame native stable gateway_native_no_output world before after->
  gateway_resource_valid(resources next)->
  gateway_resource_frame(resources world)(resources next)(fun _=>False)(fun _=>False)->
  gateway_resource_status_frame(resources world)(resources next)(fun _=>False)->
  gateway_exclusive_kept(resources world)(resources next)->gateway_flag_context left_mode right_mode after next.
Proof.
  intros INITIAL SIDE ACCESS MEMORY VALID FRAME STATUS EXCLUSIVE.
  eapply gateway_flag_context_preserved;[exact INITIAL|exact SIDE|exact ACCESS|exact MEMORY|exact VALID|exact FRAME|exact EXCLUSIVE|].
  destruct INITIAL as[_[_[_[DATA[_[MODES REST]]]]]];eapply gateway_pair_modes_frame;[exact DATA|exact MODES|exact STATUS].
Qed.

Theorem gateway_flag_context_ambient left_mode right_mode before world after next:
  gateway_flag_context left_mode right_mode before world->gateway_interference backend before world after next->
  gateway_flag_context left_mode right_mode after next.
Proof.
  intros INITIAL INTERFERENCE.
  pose proof(proj1 INITIAL)as SIDE;pose proof(proj1(proj2(proj2 INITIAL)))as VALID.
  destruct(gateway_thread_ambient _ _ _ _ _ _ thread None before world after next SIDE INTERFERENCE)
    as[NORMAL[ACCESS MEMORY]].
  destruct(gateway_spawn_ambient _ _ _ _ _ _ _ descriptors before world after next SIDE VALID INTERFERENCE)
    as[AFTER[FRAME[STATUS EXCLUSIVE]]].
  eapply gateway_flag_context_observer;eassumption.
Qed.

Theorem gateway_actual_get_flags_context before world result after next observed:
  gateway_flag_context true true before world->
  gateway_spawn_operation backend gateway_fcntl_api
    [Vint(Int.repr data_right);Vint(Int.repr 3);Vint Int.zero]before world result after next observed->
  gateway_flag_context true true after next /\io observed=None /\
  (result=Vint(Int.neg Int.one) \/exists flags,result=Vint flags /\0<=Int.signed flags).
Proof.
  intros INITIAL OPERATION.
  pose proof INITIAL as ORIGINAL_CONTEXT.
  destruct INITIAL as[SIDE[FAMILY[VALID[DATA[CONTROL REST]]]]].
  destruct(gateway_get_flags_operation _ _ _ _ _ _ _ descriptors before world data_right(pair_right_entry ipc data_identity)
    result after next observed SIDE VALID(gateway_pair_lease_right _ _ _ _ _ DATA)
    (gateway_pair_lease_right_exclusive _ _ _ _ _ DATA)OPERATION)
    as(NORMAL&AFTER&ACCESS&MEMORY&FRAME&STATUS&EXCLUSIVE&IO&CHOICE).
  split.
  - eapply gateway_flag_context_observer;
      [exact ORIGINAL_CONTEXT|exact NORMAL|exact ACCESS|exact MEMORY|exact AFTER|exact FRAME|exact STATUS|exact EXCLUSIVE].
  - split;[exact IO|]. destruct CHOICE as[FAILED|[flags[RESULT[RANGE FLAG]]]];[left;exact FAILED|].
    right;exists flags;split;assumption.
Qed.

Theorem gateway_actual_set_flags_context flags before world result after next observed:
  gateway_flag_context true true before world->
  gateway_spawn_operation backend gateway_fcntl_api
    [Vint(Int.repr data_right);Vint(Int.repr 4);Vint(Int.and flags(Int.not(Int.repr 2048)))]
    before world result after next observed->
  io observed=None /\(result=Vint(Int.neg Int.one) \/result=Vint Int.zero /\gateway_flag_context true false after next).
Proof.
  intros INITIAL OPERATION.
  pose proof(proj1 INITIAL)as SIDE;pose proof(proj1(proj2(proj2 INITIAL)))as VALID.
  pose proof(proj1(proj2(proj2(proj2 INITIAL))))as DATA.
  destruct(gateway_set_flags_operation _ _ _ _ _ _ _ descriptors before world data_right(pair_right_entry ipc data_identity)
    (Int.and flags(Int.not(Int.repr 2048)))result after next observed SIDE VALID(gateway_pair_lease_right _ _ _ _ _ DATA)
    (gateway_pair_lease_right_exclusive _ _ _ _ _ DATA)OPERATION)
    as(NORMAL&AFTER&ACCESS&MEMORY&FRAME&STATUS&EXCLUSIVE&IO&CHOICE).
  split;[exact IO|]. destruct CHOICE as[FAILED|[ZERO BLOCKING]];[left;exact FAILED|].
  right;split;[exact ZERO|].
  eapply gateway_flag_context_preserved;[exact INITIAL|exact NORMAL|exact ACCESS|exact MEMORY|exact AFTER|exact FRAME|exact EXCLUSIVE|].
  eapply gateway_pair_engine_blocking;[exact DATA|exact(proj1(proj2(proj2(proj2(proj2(proj2 INITIAL))))))|exact STATUS|].
  rewrite gateway_removed_nonblocking in BLOCKING;exact BLOCKING.
Qed.
End FlagContext.
