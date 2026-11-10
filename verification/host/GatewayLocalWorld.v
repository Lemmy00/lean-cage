(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Source-only scopes retain coupled physical ownership observations. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewayMachine GatewayLocalRuntime GatewayThreadRuntime
  GatewayReadonly GatewayCallPath GatewayOperations GatewayFrames GatewayStreamInterface GatewayContexts.
Import ListNotations.

Section LocalWorld.
Context {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)(io:Event->option gateway_native_io)
    (native_private:World->block->Prop)(stable_readonly:World->block->BinNums.Z->Prop)
    (discipline:option val->mem->World->Prop)(thread_errno:World->Integers.int).
Context(runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).
Variable state:World->Prop.
Hypothesis STATE_AMBIENT:forall before world after next,
  discipline None before world->state world->gateway_interference backend before world after next->state next.

Definition gateway_local_world_runtime(source:gateway_state World):Prop:=
  match source with
  |gateway_live current world=>gateway_local_runtime native_private discipline None source /\state world
  |gateway_dead _ _=>True
  end.

Lemma gateway_local_world_step source world event after:
  gateway_local_world_runtime(gateway_live source world)->
  gateway_step backend ge(gateway_live source world)event after->
  gateway_local_world_runtime after /\forall descriptor,gateway_received_event io descriptor event=[].
Proof.
  intros[[PROFILE SIDE]STATE]STEP.
  pose proof(gateway_local_runtime_step backend io native_private stable_readonly discipline thread_errno runtime
    ge None(gateway_live source world)event after(conj PROFILE SIDE)STEP)as NEXT.
  destruct(gateway_nonprimitive_step backend ge _ _ _ _
    (gateway_local_readonly_not_primitive native_private source world PROFILE)STEP)
    as[[trace[target[EVENT[REAL TARGET]]]]|
      [[memory[next[EVENT[INTERFERENCE TARGET]]]]|[EVENT TARGET]]];subst.
  - split;[split;[exact NEXT|exact STATE]|intros;reflexivity].
  - split;[split;[exact NEXT|eapply STATE_AMBIENT;eassumption]|intros;reflexivity].
  - split;[exact I|intros;reflexivity].
Qed.

Theorem gateway_local_world_prefix source world events after:
  gateway_local_world_runtime(gateway_live source world)->
  gateway_steps backend ge(gateway_live source world)events after->
  gateway_local_world_runtime after /\forall descriptor,gateway_received_bytes io descriptor events=[].
Proof.
  intros READY RUN;remember(gateway_live source world)as first eqn:INITIAL.
  revert source world INITIAL READY.
  induction RUN;intros source world INITIAL READY;subst.
  - split;[exact READY|intros;reflexivity].
  - destruct(gateway_local_world_step source world observed middle READY H)as[NEXT EMPTY].
    destruct middle as[following current|memory current].
    + destruct(IHRUN following current eq_refl NEXT)as[FINAL REST]. split;[exact FINAL|].
      intro descriptor;change(gateway_received_event io descriptor observed++gateway_received_bytes io descriptor rest=[]).
      rewrite EMPTY,REST;reflexivity.
    + destruct(gateway_dead_steps _ _ _ _ _ _ RUN)as[EMPTY_REST DEAD];subst.
      split;[exact I|]. intro descriptor;change(gateway_received_event io descriptor observed++[]=[]).
      rewrite EMPTY;reflexivity.
Qed.

Theorem gateway_local_world_return source world events returned after next:
  gateway_local_readonly_source native_private world source->
  discipline None(memory_of source)world->state world->
  gateway_steps backend ge(gateway_live source world)events(gateway_live(Returnstate returned Kstop after)next)->
  discipline None after next /\state next /\forall descriptor,gateway_received_bytes io descriptor events=[].
Proof.
  intros LOCAL SIDE STATE RUN.
  destruct(gateway_local_world_prefix source world events(gateway_live(Returnstate returned Kstop after)next)
    (conj(conj LOCAL SIDE)STATE)RUN)as[[FINAL NEXT]EMPTY].
  split;[exact(proj2 FINAL)|]. split;assumption.
Qed.
End LocalWorld.
