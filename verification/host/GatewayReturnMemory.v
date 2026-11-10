(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual local cleanup retains the caller's disjoint native regions. *)
From Stdlib Require Import List.
From compcert Require Import Integers AST Values Memory Events Ctypes Clight.
Require Import Machine ClightSteps StoreSteps.
From HostGateway Require Import GatewayMachine GatewayContexts GatewayFrames GatewayCallPath GatewayReadonly
  GatewayNativeRegions GatewayReturnRuntime GatewayScopedMemory GatewayLocalRuntime GatewayThreadRuntime
  GatewayStreamInterface GatewayRuntimeCuts GatewayOperations.
Import ListNotations.

Section ReturnMemory.
Context {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
  (io:Event->option gateway_native_io)(native:World->block->Prop)(stable:World->block->BinNums.Z->Prop)
  (discipline:option val->mem->World->Prop)(thread_errno:World->int).
Context(runtime:gateway_thread_runtime backend io native stable discipline thread_errno).

Definition gateway_return_region_context mode environment protected original memory world :Prop:=
  gateway_return_environment native discipline mode environment memory world /\
  gateway_native_region_owned native protected memory world /\Mem.unchanged_on protected original memory.

Lemma gateway_return_region_ambient mode environment protected original :
  gateway_runtime_discipline backend(gateway_return_region_context mode environment protected original).
Proof.
  intros before world after next[ENV[OWNED FRAME]]INTERFERENCE.
  pose proof(gateway_return_environment_ambient backend io native stable discipline thread_errno runtime
    mode environment before world after next ENV INTERFERENCE)as AFTER_ENV.
  destruct(gateway_native_region_ambient backend io native stable discipline thread_errno runtime mode protected
    before world after next(proj1 ENV)OWNED INTERFERENCE)as[SIDE[AFTER STEP_FRAME]].
  split;[exact AFTER_ENV|]. split;[exact AFTER|eapply Mem.unchanged_on_trans;eassumption].
Qed.

Theorem gateway_actual_return_memory mode function expression continuation environment temporaries protected original
    before world events value after next :
  call_cont continuation=Kstop ->gateway_environment_avoids protected environment ->
  gateway_return_region_context mode environment protected original before world ->
  gateway_steps backend ge
    (gateway_live(State function(Sreturn expression)continuation environment temporaries before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->
  gateway_native_region_context native discipline mode protected original after next.
Proof.
  intros STOP AVOIDS.
  pose proof(gateway_native_region_context_ambient backend io native stable discipline thread_errno runtime
    mode protected original)as CLOSED.
  revert before world;induction events as[|observed rest IH];intros before world[[SIDE OWNED][REGION FRAME]]RUN.
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
            intros object low high MEMBER;eapply gateway_native_environment_free_blocks;[exact OWNED|exact MEMBER]);
        assert(STEP_FRAME:Mem.unchanged_on protected before freed)by
          (eapply gateway_environment_avoids_free;[exact AVOIDS|exact FREE]);
        assert(AFTER_REGION:gateway_native_region_owned native protected freed world)by
          (eapply gateway_native_region_memory_frame;[exact REGION|exact STEP_FRAME])end.
      all:rewrite STOP in TAIL.
      all:match goal with
        TAIL:gateway_steps _ _ (gateway_live(Returnstate ?actual Kstop ?freed)?current)_ _|-_=>
          eapply(gateway_readonly_run_side backend ge _ CLOSED(Returnstate actual Kstop freed)current rest value after next);
          [exact I| |exact TAIL]end.
      all:split;[exact AFTER_SIDE|].
      all:split;[exact AFTER_REGION|eapply Mem.unchanged_on_trans;[exact FRAME|exact STEP_FRAME]].
    + eapply IH;[|exact TAIL].
      exact(gateway_return_region_ambient mode environment protected original before world changed following_world
        (conj(conj SIDE OWNED)(conj REGION FRAME))INTERFERENCE).
    + destruct(gateway_dead_steps _ _ _ _ _ _ TAIL)as[_ BAD];discriminate.
Qed.

Theorem gateway_actual_caller_return_memory mode function destination environment temporaries expression following
    protected original before world events returned value after next :
  call_cont following=Kstop ->gateway_environment_avoids protected environment ->
  gateway_return_region_context mode environment protected original before world ->
  gateway_steps backend ge
    (gateway_live(Returnstate returned(Kcall destination function environment temporaries
      (Kseq(Sreturn expression)following))before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->
  gateway_native_region_context native discipline mode protected original after next.
Proof.
  intros STOP AVOIDS READY RUN.
  pose proof(gateway_return_region_ambient mode environment protected original)as CLOSED.
  destruct(gateway_uniform_edge_side_cut backend ge _ CLOSED
    (Returnstate returned(Kcall destination function environment temporaries(Kseq(Sreturn expression)following))before)
    (State function Sskip(Kseq(Sreturn expression)following)environment(set_opttemp destination returned temporaries)before)
    before world events value after next ltac:(cbn;tauto)
    ltac:(intros;apply unchanged_store_edge,edge_returnstate)READY RUN)
    as(prefix &rest &middle &current &EVENTS &AMBIENT &PREFIX &MIDDLE_READY &REST).
  destruct(gateway_uniform_edge_side_cut backend ge _ CLOSED
    (State function Sskip(Kseq(Sreturn expression)following)environment(set_opttemp destination returned temporaries)middle)
    (State function(Sreturn expression)following environment(set_opttemp destination returned temporaries)middle)
    middle current rest value after next ltac:(cbn;tauto)
    ltac:(intros;apply unchanged_store_edge,edge_skip_seq)MIDDLE_READY REST)
    as(pending &suffix &return_memory &return_world &REST_EVENTS &WAITING &TO_RETURN &RETURN_READY &FROM_RETURN).
  exact(gateway_actual_return_memory mode function expression following environment(set_opttemp destination returned temporaries)
    protected original return_memory return_world suffix value after next STOP AVOIDS RETURN_READY FROM_RETURN).
Qed.

End ReturnMemory.
