(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: Individual real SDK destroys preserve all parent IPC leases. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewayRuntime GatewayThreadRuntime GatewayStreamInterface GatewaySpawnABI
  GatewaySpawnResources GatewaySpawnRuntime GatewaySpawnActions GatewayCallerFamily GatewaySDKInputs GatewayPostSpawnContext.
Import ListNotations.
Open Scope Z_scope.

Inductive gateway_release_kind:=gateway_release_actions|gateway_release_attributes.
Definition gateway_release_api kind:=match kind with
  gateway_release_actions=>gateway_actions_destroy_api|gateway_release_attributes=>gateway_attributes_destroy_api end.
Definition gateway_release_width kind:Z:=match kind with gateway_release_actions=>80|gateway_release_attributes=>336 end.
Definition gateway_release_present kind state object:Prop:=match kind with
  |gateway_release_actions=>exists plan,gateway_builder_actions state=Some(Vptr object Ptrofs.zero,plan)
  |gateway_release_attributes=>exists settings,gateway_builder_attributes state=Some(Vptr object Ptrofs.zero,settings) end.
Definition gateway_release_done kind state:=match kind with
  |gateway_release_actions=>gateway_with_actions state None|gateway_release_attributes=>gateway_with_attributes state None end.

Section Release.
Context {World Event}(backend:gateway_backend World Event)io native stable discipline resources
  builders genuine footprint
  (sdk:gateway_spawn_builder_runtime backend io native stable discipline resources builders genuine footprint).
Variables(readonly:Values.block->Z->Prop)(selected:Values.block->Prop)(reference:mem)(owner:World)
  (data control:Values.block)(data_left data_right control_left control_right:Z).
Hypotheses(DATA_SELECTED:selected data)(CONTROL_SELECTED:selected control).
Local Definition context:=gateway_postspawn_context native stable discipline resources builders genuine readonly selected reference owner
  data control data_left data_right control_left control_right.

Lemma gateway_postspawn_release kind expected leases object before world result after next observed:
  context expected leases before world->selected object->object<>data->object<>control->
  (forall position,~readonly object position)->
  Mem.range_perm reference object 0(gateway_release_width kind)Cur Freeable->
  gateway_release_present kind expected object->
  gateway_spawn_operation backend(gateway_release_api kind)[Vptr object Ptrofs.zero]before world result after next observed->
  result=Vint Int.zero /\io observed=None /\context(gateway_release_done kind expected)leases after next.
Proof.
  intros INITIAL SELECTED AWAY_DATA AWAY_CONTROL DISJOINT WRITABLE PRESENT OPERATION.
  destruct INITIAL as[SIDE VALID GENUINE SHADOW FAMILY DATA CONTROL LEASES].
  destruct(gateway_sdk_header_from_family native stable readonly selected reference owner before world object(gateway_release_width kind)
    FAMILY SELECTED WRITABLE ltac:(destruct kind;change Ptrofs.modulus with 18446744073709551616;cbn;lia))as[PRIVATE POINTER].
  assert(POST:gateway_builder_post io native stable discipline resources genuine before world after next observed
      object Ptrofs.zero(gateway_release_width kind) /\result=Vint Int.zero /\builders next=gateway_release_done kind(builders world)).
  { destruct kind;cbn[gateway_release_present]in PRESENT;destruct PRESENT as[content PRESENT];rewrite<-SHADOW in PRESENT.
    - exact(gateway_actions_release _ _ _ _ _ _ _ _ _ sdk before world object Ptrofs.zero content result after next observed
        SIDE GENUINE VALID PRIVATE POINTER eq_refl PRESENT OPERATION).
    - exact(gateway_attributes_release _ _ _ _ _ _ _ _ _ sdk before world object Ptrofs.zero content result after next observed
        SIDE GENUINE VALID PRIVATE POINTER eq_refl PRESENT OPERATION). }
  destruct POST as[[NORMAL[GENUINE_AFTER[VALID_AFTER[ACCESS[PERMISSIONS[FRAME[RESOURCES[STATUS[EXCLUSIVE IO]]]]]]]]] [RESULT BUILDERS]].
  split;[exact RESULT|]. split;[exact IO|].
  eapply gateway_postspawn_output with(expected:=expected)(leases:=leases)(before:=before)(world:=world)(object:=object)(offset:=Ptrofs.zero)
    (width:=gateway_release_width kind).
  - exact DATA_SELECTED.
  - exact CONTROL_SELECTED.
  - constructor;assumption.
  - exact AWAY_DATA.
  - exact AWAY_CONTROL.
  - exact DISJOINT.
  - exact NORMAL.
  - exact VALID_AFTER.
  - exact GENUINE_AFTER.
  - rewrite BUILDERS,SHADOW;reflexivity.
  - exact ACCESS.
  - exact PERMISSIONS.
  - exact FRAME.
  - exact RESOURCES.
Qed.
End Release.
