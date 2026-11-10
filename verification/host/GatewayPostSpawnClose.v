(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: Closing a parent peer consumes its lease and preserves other actual leases. *)
From Stdlib Require Import ZArith List Bool.
From compcert Require Import Integers AST Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewayRuntime GatewayThreadRuntime GatewayStreamInterface GatewaySpawnABI
  GatewaySpawnResources GatewaySpawnRuntime GatewaySpawnActions GatewayPostSpawnContext.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_leases_without fd(leases:list(Z*gateway_resource_descriptor)):=
  filter(fun entry=>negb(Z.eqb(fst entry)fd))leases.
Lemma gateway_leases_without_member fd leases entry:
  In entry(gateway_leases_without fd leases)->In entry leases /\fst entry<>fd.
Proof.
  unfold gateway_leases_without;rewrite filter_In;intros[MEMBER OTHER];split;[exact MEMBER|].
  apply negb_true_iff in OTHER;apply Z.eqb_neq;exact OTHER.
Qed.
Lemma gateway_close_not_builder:~gateway_builder_mutation(gateway_spawn_signature gateway_close_api).
Proof.
  intros[api[MEMBER DEFINITION]];rewrite actual_gateway_spawn_signatures in DEFINITION.
  destruct api;cbn[gateway_spawn_signature]in DEFINITION;try discriminate DEFINITION;cbn in MEMBER;intuition discriminate.
Qed.

Theorem gateway_postspawn_close {World Event}(backend:gateway_backend World Event)io native stable discipline resources ipc
    builders genuine footprint
    (descriptors:gateway_spawn_descriptor_runtime backend io native stable discipline resources ipc)
    (sdk:gateway_spawn_builder_runtime backend io native stable discipline resources builders genuine footprint)
    readonly selected reference owner data control data_left data_right control_left control_right expected leases
    fd entry before world result after next observed:
  selected data->selected control->
  gateway_postspawn_context native stable discipline resources builders genuine readonly selected reference owner
    data control data_left data_right control_left control_right expected leases before world->
  In(fd,entry)leases->
  gateway_spawn_operation backend gateway_close_api[Vint(Int.repr fd)]before world result after next observed->
  (result=Vint Int.zero \/result=Vint(Int.neg Int.one)) /\io observed=None /\
  gateway_postspawn_context native stable discipline resources builders genuine readonly selected reference owner
    data control data_left data_right control_left control_right expected(gateway_leases_without fd leases)after next.
Proof.
  intros DATA_SELECTED CONTROL_SELECTED INITIAL MEMBER OPERATION.
  pose proof INITIAL as INPUT;destruct INPUT as[SIDE VALID GENUINE SHADOW FAMILY DATA CONTROL LEASES].
  assert(OWNED:gateway_owned_descriptor(resources world)fd entry).
  { exact((proj1(Forall_forall _ _))LEASES(fd,entry)MEMBER). }
  destruct(gateway_close_operation _ _ _ _ _ _ _ descriptors before world fd entry result after next observed
    SIDE VALID OWNED OPERATION)as[RESULT[NORMAL[VALID_AFTER[ACCESS[FRAME[CONSUMED[RESOURCES[STATUS[EXCLUSIVE IO]]]]]]]]].
  assert(REAL:gateway_runtime_operation backend(gateway_spawn_signature gateway_close_api)[Vint(Int.repr fd)]
    before world result after next observed).
  { destruct OPERATION as[definition[DEFINITION REAL]];rewrite actual_gateway_spawn_signatures in DEFINITION;
      injection DEFINITION as SAME;subst definition;exact REAL. }
  pose proof(gateway_builder_passive _ _ _ _ _ _ _ _ _ sdk(gateway_spawn_signature gateway_close_api)[Vint(Int.repr fd)]
    before world result after next observed SIDE gateway_close_not_builder REAL)as SHADOW_AFTER.
  assert(GENUINE_AFTER:genuine after next).
  { eapply gateway_builder_unexposed_operation;[exact sdk|exact SIDE|exact GENUINE|exact gateway_close_not_builder| |exact REAL].
    intros object offset[WRONG|ABSENT];[discriminate WRONG|contradiction]. }
  split;[exact RESULT|]. split;[exact IO|].
  eapply gateway_postspawn_kept with(expected:=expected)(leases:=leases)(before:=before)(world:=world)
    (removed:=fun candidate=>candidate=fd)(added:=fun _=>False);
    [exact DATA_SELECTED|exact CONTROL_SELECTED|exact INITIAL|exact NORMAL|exact VALID_AFTER|exact GENUINE_AFTER
    |exact SHADOW_AFTER|exact ACCESS|exact FRAME|exact RESOURCES|].
  intros kept HERE;exact(gateway_leases_without_member fd leases kept HERE).
Qed.
