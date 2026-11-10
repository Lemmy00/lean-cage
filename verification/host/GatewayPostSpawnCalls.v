(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: Actual SDK destroy calls retain the same parent resources. *)
From Stdlib Require Import ZArith List String.
From compcert Require Import Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewayMachine GatewayRuntime GatewayThreadRuntime GatewayStreamInterface GatewaySpawnABI
  GatewaySpawnResources GatewaySpawnRuntime GatewaySpawnActions GatewayCallerFamily GatewaySDKInputs GatewayPostSpawnContext
  GatewayPostSpawnRelease GatewayPostSpawnClose GatewayPrimitiveCalls GatewayPrimitiveQuiet GatewayOperations GatewayFramedRuntime GatewaySendRuntime.
Import ListNotations.
Local Open Scope string_scope.
Open Scope Z_scope.

Section Calls.
Context {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno resources ipc
  builders genuine footprint
  (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
  (descriptors:gateway_spawn_descriptor_runtime backend io native stable discipline resources ipc)
  (sdk:gateway_spawn_builder_runtime backend io native stable discipline resources builders genuine footprint).
Variables(readonly:Values.block->Z->Prop)(selected:Values.block->Prop)(reference:mem)(owner:World)
  (data control:Values.block)(data_left data_right control_left control_right:Z).
Hypotheses(DATA_SELECTED:selected data)(CONTROL_SELECTED:selected control).
Local Definition context:=gateway_postspawn_context native stable discipline resources builders genuine readonly selected reference owner
  data control data_left data_right control_left control_right.
Local Lemma context_closed expected leases:gateway_ambient_closed backend(context expected leases).
Proof. eapply gateway_postspawn_ambient;[exact runtime|exact descriptors|exact sdk|exact DATA_SELECTED|exact CONTROL_SELECTED]. Qed.

Theorem actual_postspawn_release ge kind expected leases object before world events returned after next descriptor:
  context expected leases before world->selected object->object<>data->object<>control->
  (forall position,~readonly object position)->
  Mem.range_perm reference object 0(gateway_release_width kind)Cur Freeable->gateway_release_present kind expected object->
  gateway_steps backend ge
    (gateway_live(Callstate(gateway_spawn_signature(gateway_release_api kind))[Vptr object Ptrofs.zero]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next)->
  returned=Vint Int.zero /\context(gateway_release_done kind expected)leases after next /\
    gateway_received_bytes io descriptor events=[] /\gateway_sent_bytes io descriptor events=[].
Proof.
  intros INITIAL SELECTED AWAY_DATA AWAY_CONTROL DISJOINT WRITABLE PRESENT RUN.
  destruct(gateway_spawn_signature(gateway_release_api kind))as[function|external types result_type convention]eqn:SIGNATURE.
  - destruct kind;discriminate SIGNATURE.
  - assert(EFFECT:forall before world result after next observed,context expected leases before world->
      gateway_external backend external types result_type convention[Vptr object Ptrofs.zero]before world result after next observed->
      result=Vint Int.zero /\context(gateway_release_done kind expected)leases after next).
    { intros memory current value changed future observed READY OPERATION.
      assert(OP:gateway_spawn_operation backend(gateway_release_api kind)[Vptr object Ptrofs.zero]
        memory current value changed future observed).
      { exists(External external types result_type convention);split;
          [rewrite actual_gateway_spawn_signatures,SIGNATURE;reflexivity|exact OPERATION]. }
      destruct(gateway_postspawn_release backend io native stable discipline resources builders genuine footprint sdk
        readonly selected reference owner data control data_left data_right control_left control_right DATA_SELECTED CONTROL_SELECTED
        kind expected leases object memory current value changed future observed READY SELECTED AWAY_DATA AWAY_CONTROL DISJOINT WRITABLE
        PRESENT OP)as[RESULT[IO AFTER]];split;assumption. }
    destruct(gateway_actual_primitive_context backend ge external types result_type convention[Vptr object Ptrofs.zero]
      (context expected leases)(fun value memory current=>value=Vint Int.zero /\context(gateway_release_done kind expected)leases memory current)
      (context_closed expected leases)
      ltac:(intros value memory current changed future[RESULT READY]INTERFERENCE;split;[exact RESULT|
        eapply context_closed;[exact READY|exact INTERFERENCE]])
      EFFECT before world events returned after next INITIAL RUN)
      as(prefix & suffix & memory & current & changed & future & observed & EVENTS & PENDING & PREFIX & CALLED & OPERATION & OUTPUT & SUFFIX & FINAL).
    assert(OP:gateway_spawn_operation backend(gateway_release_api kind)[Vptr object Ptrofs.zero]
      memory current returned changed future observed).
    { exists(External external types result_type convention);split;
        [rewrite actual_gateway_spawn_signatures,SIGNATURE;reflexivity|exact OPERATION]. }
    destruct(gateway_postspawn_release backend io native stable discipline resources builders genuine footprint sdk
      readonly selected reference owner data control data_left data_right control_left control_right DATA_SELECTED CONTROL_SELECTED
      kind expected leases object memory current returned changed future observed CALLED SELECTED AWAY_DATA AWAY_CONTROL DISJOINT WRITABLE
      PRESENT OP)as[RESULT[IO AFTER]].
    split;[exact(proj1 FINAL)|]. split;[exact(proj2 FINAL)|].
    eapply gateway_external_no_io_projection;[exact EVENTS|exact PENDING|exact IO|exact SUFFIX].
Qed.
Theorem actual_postspawn_close ge expected leases fd entry before world events returned after next descriptor:
  context expected leases before world->In(fd,entry)leases->
  gateway_steps backend ge
    (gateway_live(Callstate(gateway_spawn_signature gateway_close_api)[Vint(Int.repr fd)]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next)->
  (returned=Vint Int.zero \/returned=Vint(Int.neg Int.one)) /\
  context expected(gateway_leases_without fd leases)after next /\
  gateway_received_bytes io descriptor events=[] /\gateway_sent_bytes io descriptor events=[].
Proof.
  intros INITIAL MEMBER RUN.
  assert(EFFECT:forall before world result after next observed,context expected leases before world->
    gateway_external backend(EF_external "close"(mksignature[Xint]Xint cc_default))[tint]tint cc_default[Vint(Int.repr fd)]
      before world result after next observed->
    (result=Vint Int.zero \/result=Vint(Int.neg Int.one)) /\context expected(gateway_leases_without fd leases)after next).
  { intros memory current value changed future observed READY OPERATION.
    assert(OP:gateway_spawn_operation backend gateway_close_api[Vint(Int.repr fd)]memory current value changed future observed).
    { exists(gateway_spawn_signature gateway_close_api);split;[apply actual_gateway_spawn_signatures|exact OPERATION]. }
    destruct(gateway_postspawn_close backend io native stable discipline resources ipc builders genuine footprint descriptors sdk
      readonly selected reference owner data control data_left data_right control_left control_right expected leases fd entry
      memory current value changed future observed DATA_SELECTED CONTROL_SELECTED READY MEMBER OP)as[RESULT[IO AFTER]];split;assumption. }
  destruct(gateway_actual_primitive_context backend ge(EF_external "close"(mksignature[Xint]Xint cc_default))[tint]tint cc_default
    [Vint(Int.repr fd)](context expected leases)
    (fun value memory current=>(value=Vint Int.zero \/value=Vint(Int.neg Int.one)) /\
      context expected(gateway_leases_without fd leases)memory current)
    (context_closed expected leases)
    ltac:(intros value memory current changed future[RESULT READY]INTERFERENCE;split;[exact RESULT|
      eapply context_closed;[exact READY|exact INTERFERENCE]])
    EFFECT before world events returned after next INITIAL RUN)
    as(prefix & suffix & memory & current & changed & future & observed & EVENTS & PENDING & PREFIX & CALLED & OPERATION & OUTPUT & SUFFIX & FINAL).
  assert(OP:gateway_spawn_operation backend gateway_close_api[Vint(Int.repr fd)]memory current returned changed future observed).
  { exists(gateway_spawn_signature gateway_close_api);split;[apply actual_gateway_spawn_signatures|exact OPERATION]. }
  destruct(gateway_postspawn_close backend io native stable discipline resources ipc builders genuine footprint descriptors sdk
    readonly selected reference owner data control data_left data_right control_left control_right expected leases fd entry
    memory current returned changed future observed DATA_SELECTED CONTROL_SELECTED CALLED MEMBER OP)as[RESULT[IO AFTER]].
  split;[exact(proj1 FINAL)|]. split;[exact(proj2 FINAL)|].
  eapply gateway_external_no_io_projection;[exact EVENTS|exact PENDING|exact IO|exact SUFFIX].
Qed.

End Calls.
