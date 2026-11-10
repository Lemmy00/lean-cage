(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Real C returns free only their owned locals before returning runtime roots. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewayMachine GatewayContexts GatewayPure GatewayFrames GatewayOperations
  GatewayReadonly GatewayLocalRuntime GatewayThreadRuntime GatewayStreamInterface GatewayCallPath GatewayPathEvents.
Import ListNotations.

Section ReturnRuntime.
Context {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
  (io:Event->option gateway_native_io)(native:World->block->Prop)(stable:World->block->BinNums.Z->Prop)
  (discipline:option val->mem->World->Prop)(thread_errno:World->Integers.int).
Context(runtime:gateway_thread_runtime backend io native stable discipline thread_errno).

Definition gateway_return_environment mode environment memory world :Prop:=
  discipline mode memory world /\gateway_native_environment native world memory environment.

Lemma gateway_return_environment_ambient mode environment :
  gateway_runtime_discipline backend(gateway_return_environment mode environment).
Proof.
  intros before world after next[SIDE OWNED]INTERFERENCE.
  destruct(gateway_thread_ambient _ _ _ _ _ _ runtime mode _ _ _ _ SIDE INTERFERENCE)
    as[NEXT[[RETAIN_NATIVE RETAIN_STABLE]FRAME]].
  split;[exact NEXT|]. intros identifier object ty LOOK.
  destruct(OWNED identifier object ty LOOK)as[LIVE NATIVE];split.
  - eapply Mem.valid_block_unchanged_on;[exact FRAME|exact LIVE].
  - apply RETAIN_NATIVE;assumption.
Qed.

Theorem gateway_actual_return_side mode function expression continuation environment temporaries
    before world events value after next :
  call_cont continuation=Kstop ->gateway_return_environment mode environment before world ->
  gateway_steps backend ge
    (gateway_live(State function(Sreturn expression)continuation environment temporaries before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->
  discipline mode after next /\Forall gateway_quiet_event events.
Proof.
  intros STOP.
  assert(AMBIENT:gateway_runtime_discipline backend(discipline mode)).
  { intros first current last following READY INTERFERENCE.
    exact(proj1(gateway_thread_ambient _ _ _ _ _ _ runtime mode _ _ _ _ READY INTERFERENCE)). }
  revert before world;induction events as[|observed rest IH];intros before world[SIDE OWNED]RUN.
  - inversion RUN.
  - inversion RUN as[|first event middle remaining target HEAD TAIL];subst.
    assert(INTERNAL:~gateway_at_primitive(State function(Sreturn expression)continuation environment temporaries before))
      by(cbn;tauto).
    destruct(gateway_nonprimitive_step backend ge _ _ _ _ INTERNAL HEAD)
      as[[trace[following[EVENT[REAL TARGET]]]]|
        [[changed[following_world[EVENT[INTERFERENCE TARGET]]]]|[EVENT TARGET]]];subst.
    + inversion REAL;subst.
      all:try match goal with BAD:_=_\/_=_|-_=>destruct BAD;discriminate end.
      all:match goal with FREE:Mem.free_list _ (blocks_of_env _ ?locals)=Some ?freed|-_=>
        assert(AFTER_SIDE:discipline mode freed world)by
          (eapply gateway_native_free_list;[exact runtime|exact SIDE| |exact FREE];
            intros object low high MEMBER;eapply gateway_native_environment_free_blocks;[exact OWNED|exact MEMBER])end.
      all:rewrite STOP in TAIL.
      all:match goal with
        TAIL:gateway_steps _ _ (gateway_live(Returnstate ?actual Kstop ?freed)?current)_ _|-_=>
          assert(FINAL_SIDE:discipline mode after next)by
            (eapply(gateway_readonly_run_side backend ge(discipline mode)AMBIENT
              (Returnstate actual Kstop freed)current rest value after next);
              [exact I|exact AFTER_SIDE|exact TAIL])end.
      all:split;[exact FINAL_SIDE|].
      all:constructor;[left;reflexivity|].
      all:match goal with TAIL:gateway_steps _ _ (gateway_live(Returnstate ?actual Kstop ?freed)?current)_ _|-_=>
        eapply(gateway_readonly_run_events backend ge(Returnstate actual Kstop freed)current rest value after next);
          [exact I|exact TAIL]end.
    + destruct(IH changed following_world
        (gateway_return_environment_ambient mode environment before world changed following_world
          (conj SIDE OWNED)INTERFERENCE)TAIL)
        as[AFTER QUIET].
      split;[exact AFTER|constructor;[right;reflexivity|exact QUIET]].
    + destruct(gateway_dead_steps _ _ _ _ _ _ TAIL)as[_ BAD];discriminate.
Qed.

End ReturnRuntime.
