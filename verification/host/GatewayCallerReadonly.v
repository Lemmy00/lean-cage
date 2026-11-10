(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Readonly scopes retain real uninitialized caller buffers. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewayMachine GatewayReadonly GatewayLocalRuntime GatewayScopedMemory
  GatewayCallerBuffers GatewayBufferReference GatewayThreadRuntime GatewayStreamInterface
  GatewayOperations GatewayFrames GatewayContexts.
Import ListNotations.

Definition gateway_caller_scope (readonly:block->Z->Prop) target reference object position:Prop:=
  object=target \/readonly object position \/Mem.valid_block reference object.

Lemma gateway_caller_scope_live {World}(native_private:World->block->Prop)
    (stable_readonly:World->block->Z->Prop) readonly target reference owner memory world:
  gateway_caller_buffers native_private stable_readonly readonly target reference owner memory world->
  gateway_region_live(gateway_caller_scope readonly target reference)memory.
Proof.
  intros[LIVE[PRIVATE[READONLY[BUFFER REST]]]]object position[TARGET|[HERE|ORIGINAL]].
  - subst object;exact LIVE.
  - exact(proj1(READONLY object position HERE)).
  - eapply Mem.valid_block_unchanged_on;[exact(proj1 BUFFER)|exact ORIGINAL].
Qed.

Lemma gateway_caller_buffers_source_frame {World}(native_private:World->block->Prop)
    (stable_readonly:World->block->Z->Prop) readonly target reference owner before world after:
  gateway_caller_buffers native_private stable_readonly readonly target reference owner before world->
  Mem.unchanged_on(gateway_caller_scope readonly target reference)before after->
  gateway_caller_buffers native_private stable_readonly readonly target reference owner after world.
Proof.
  intros[LIVE[PRIVATE[READONLY[BUFFER[NATIVE STABLE]]]]]FRAME.
  split;[eapply Mem.valid_block_unchanged_on;eassumption|]. split;[exact PRIVATE|].
  split.
  - intros object position HERE;destruct(READONLY object position HERE)as[VALID[OWNED|[READABLE IMMUTABLE]]].
    + split;[eapply Mem.valid_block_unchanged_on;eassumption|left;exact OWNED].
    + split;[eapply Mem.valid_block_unchanged_on;eassumption|]. right;split;[|exact IMMUTABLE].
      eapply Mem.perm_unchanged_on;[exact FRAME|right;left;exact HERE|exact READABLE].
  - split.
    + eapply gateway_buffer_reference_transitive;[exact BUFFER|]. split.
      * eapply Mem.unchanged_on_implies;[exact FRAME|]. intros object position HERE VALID;right;left;exact HERE.
      * intros object[SAME|SAME]position kind permission;subst object.
        all:apply(Mem.unchanged_on_perm _ _ _ FRAME target position kind permission);
          [left;reflexivity|exact LIVE].
    + split.
      * intros object VALID OWNED;destruct(NATIVE object VALID OWNED)as[CURRENT RETAINED].
        split;[eapply Mem.valid_block_unchanged_on;eassumption|exact RETAINED].
      * intros object position READABLE IMMUTABLE;destruct(STABLE object position READABLE IMMUTABLE)as[CURRENT RETAINED].
        split;[|exact RETAINED]. eapply Mem.perm_unchanged_on;[exact FRAME| |exact CURRENT].
        right;right;eapply Mem.perm_valid_block;exact READABLE.
Qed.

Section CallerReadonly.
Context {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)(io:Event->option gateway_native_io)
    (native_private:World->block->Prop)(stable_readonly:World->block->Z->Prop)
    (discipline:option val->mem->World->Prop)(thread_errno:World->int).
Context(runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).
Context(readonly:block->Z->Prop)(target:block)(reference:mem)(owner:World).
Local Definition scope:=gateway_caller_scope readonly target reference.
Local Definition history:=gateway_caller_buffers native_private stable_readonly readonly target reference owner.

Definition gateway_caller_readonly_ready memory world:Prop:=discipline None memory world /\history memory world.

Lemma gateway_caller_readonly_ambient:gateway_runtime_discipline backend gateway_caller_readonly_ready.
Proof.
  intros before world after next[SIDE HISTORY]INTERFERENCE.
  destruct(gateway_thread_ambient _ _ _ _ _ _ runtime None before world after next SIDE INTERFERENCE)
    as[AFTER[ACCESS FRAME]].
  split;[exact AFTER|]. eapply gateway_caller_buffers_no_output;[exact HISTORY|exact ACCESS|exact FRAME].
Qed.

Definition gateway_caller_readonly_runtime(state:gateway_state World):Prop:=
  match state with
  |gateway_live source world=>gateway_local_readonly_source native_private world source /\
      gateway_scoped_readonly scope source /\gateway_caller_readonly_ready(memory_of source)world
  |gateway_dead _ _=>True
  end.

Lemma gateway_caller_readonly_internal source world trace after:
  gateway_caller_readonly_runtime(gateway_live source world)->step2 ge source trace after->
  gateway_caller_readonly_runtime(gateway_live after world).
Proof.
  intros[LOCAL[SCOPED[SIDE HISTORY]]]STEP.
  destruct(gateway_local_readonly_source_step backend io native_private stable_readonly discipline thread_errno runtime
    ge None source world trace after LOCAL SIDE STEP)as[AFTER HELD].
  destruct(gateway_scoped_readonly_source_step ge scope source trace after SCOPED
    (gateway_caller_scope_live _ _ _ _ _ _ _ _ HISTORY)STEP)as[SCOPE FRAME].
  split;[exact AFTER|]. split;[exact SCOPE|]. split;[exact HELD|].
  eapply gateway_caller_buffers_source_frame;eassumption.
Qed.

Lemma gateway_caller_readonly_interference source world after next:
  gateway_caller_readonly_runtime(gateway_live source world)->
  gateway_interference backend(memory_of source)world after next->
  gateway_caller_readonly_runtime(gateway_live(gateway_replace_memory source after)next).
Proof.
  intros[LOCAL[SCOPED[SIDE HISTORY]]]INTERFERENCE.
  destruct(gateway_thread_ambient _ _ _ _ _ _ runtime None _ _ _ _ SIDE INTERFERENCE)
    as[HELD[ACCESS FRAME]].
  split;[eapply gateway_local_readonly_ambient;eassumption|].
  split;[apply gateway_scoped_readonly_replace;exact SCOPED|]. rewrite gateway_replace_memory_of.
  split;[exact HELD|]. eapply gateway_caller_buffers_no_output;eassumption.
Qed.

Lemma gateway_caller_readonly_step source world event after descriptor:
  gateway_caller_readonly_runtime(gateway_live source world)->
  gateway_step backend ge(gateway_live source world)event after->
  gateway_caller_readonly_runtime after /\gateway_received_event io descriptor event=[].
Proof.
  intros READY STEP.
  assert(INTERNAL:~gateway_at_primitive source).
  { eapply gateway_local_readonly_not_primitive;exact(proj1 READY). }
  inversion STEP;subst.
  - split;[eapply gateway_caller_readonly_internal;eassumption|reflexivity].
  - exfalso;apply INTERNAL;exact I.
  - exfalso;apply INTERNAL;exact I.
  - split;[eapply gateway_caller_readonly_interference;eassumption|reflexivity].
  - contradiction.
  - split;[exact I|reflexivity].
  - exfalso;apply INTERNAL;exact I.
  - exfalso;apply INTERNAL;exact I.
Qed.

Theorem gateway_caller_readonly_prefix source world events after descriptor:
  gateway_caller_readonly_runtime(gateway_live source world)->
  gateway_steps backend ge(gateway_live source world)events after->
  gateway_caller_readonly_runtime after /\gateway_received_bytes io descriptor events=[].
Proof.
  intros READY RUN;remember(gateway_live source world)as first eqn:INITIAL.
  revert source world INITIAL READY.
  induction RUN;intros source world INITIAL READY;subst.
  - split;[exact READY|reflexivity].
  - destruct(gateway_caller_readonly_step source world observed middle descriptor READY H)as[NEXT EMPTY].
    destruct middle as[following current|memory current].
    + destruct(IHRUN following current eq_refl NEXT)as[FINAL REST]. split;[exact FINAL|].
      change(gateway_received_event io descriptor observed++gateway_received_bytes io descriptor rest=[]).
      rewrite EMPTY,REST;reflexivity.
    + destruct(gateway_dead_steps _ _ _ _ _ _ RUN)as[EMPTY_REST DEAD];subst.
      split;[exact I|]. change(gateway_received_event io descriptor observed++[]=[]);rewrite EMPTY;reflexivity.
Qed.

Theorem gateway_caller_readonly_return source world events returned after next descriptor:
  gateway_local_readonly_source native_private world source->gateway_scoped_readonly scope source->
  gateway_caller_readonly_ready(memory_of source)world->
  gateway_steps backend ge(gateway_live source world)events(gateway_live(Returnstate returned Kstop after)next)->
  gateway_caller_readonly_ready after next /\gateway_received_bytes io descriptor events=[].
Proof.
  intros LOCAL SCOPED HISTORY RUN.
  destruct(gateway_caller_readonly_prefix source world events(gateway_live(Returnstate returned Kstop after)next)
    descriptor(conj LOCAL(conj SCOPED HISTORY))RUN)as[[AFTER[SCOPE FINAL]]EMPTY]. split;assumption.
Qed.
End CallerReadonly.
