(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: Every actual reap step retains the selected caller state. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayRuntime GatewayThreadRuntime GatewayStreamInterface
  GatewayReapRuntime GatewayReapAllocation GatewayReapContext GatewayReapScope GatewayReapStructure GatewayReapMemory
  GatewayReapEffects GatewayCallerBuffers GatewayCallerFamily GatewayReturnBarrier.
Import ListNotations.
Open Scope Z_scope.

Section ReapState.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
    (observation:Event->option gateway_reap_observation)(native:World->block->Prop)(stable:World->block->Z->Prop)
    (discipline:option val->mem->World->Prop)(thread_errno:World->int).
Context(thread:gateway_thread_runtime backend io native stable discipline thread_errno)
    (runtime:gateway_reap_runtime backend io observation native stable discipline thread_errno).
Variables(saved:val)(slots:gateway_reap_slots)(allocated:mem)(allocation_world:World)
  (readonly:block->Z->Prop)(selected:block->Prop)(reference:mem)(owner:World)(allocation_before:mem)(child:int).
Hypothesis(ALLOCATION:reap_allocations allocation_before slots allocated)
  (SCOPE:gateway_reap_scope slots readonly selected reference)(CHILD:0<Int.signed child).
Local Definition context:=gateway_reap_context native stable discipline saved slots allocated allocation_world
  readonly selected reference owner.
Local Definition post memory world:=discipline(Some saved)memory world /\
  gateway_caller_family native stable readonly selected reference owner memory world.

Definition gateway_reap_assertion(source:Clight.state)(world:World):Prop:=
  gateway_reap_source slots child source /\
  match source with Returnstate _ Kstop memory=>post memory world|_=>context(memory_of source)world end.

Definition gateway_reap_state(state:gateway_state World):Prop:=match state with
  |gateway_live source world=>gateway_reap_assertion source world|gateway_dead _ _=>True end.

Definition gateway_reap_regular(source:Clight.state):Prop:=match source with
  |Callstate(Internal _) _ _ _=>False|_=>True end.

Lemma gateway_reap_assertion_context source world:
  gateway_reap_source slots child source->context(memory_of source)world->gateway_reap_assertion source world.
Proof.
  intros SOURCE CONTEXT;split;[exact SOURCE|].
  destruct source as[function body continuation environment temporaries memory|
    definition arguments continuation memory|returned continuation memory];try exact CONTEXT.
  destruct continuation;try exact CONTEXT;exact(conj(proj1 CONTEXT)(proj1(proj2 CONTEXT))).
Qed.

Lemma gateway_reap_post_ambient before world after next:
  post before world->gateway_interference backend before world after next->post after next.
Proof.
  intros[SIDE FAMILY]INTERFERENCE.
  destruct(gateway_thread_ambient _ _ _ _ _ _ thread(Some saved)before world after next SIDE INTERFERENCE)
    as[AFTER[ACCESS FRAME]];split;[exact AFTER|].
  intros target SELECTED;eapply gateway_caller_buffers_no_output;[exact(FAMILY target SELECTED)|exact ACCESS|exact FRAME].
Qed.

Lemma gateway_reap_assertion_ambient source world memory next:
  gateway_reap_assertion source world->gateway_interference backend(memory_of source)world memory next->
  gateway_reap_assertion(gateway_replace_memory source memory)next.
Proof.
  intros[SOURCE CONTEXT]INTERFERENCE;split;[apply gateway_reap_source_replace;exact SOURCE|].
  destruct source as[function body continuation environment temporaries before|
    definition arguments continuation before|returned continuation before];cbn[gateway_replace_memory memory_of]in *.
  - eapply gateway_reap_context_ambient;[exact thread|exact CONTEXT|exact INTERFERENCE].
  - eapply gateway_reap_context_ambient;[exact thread|exact CONTEXT|exact INTERFERENCE].
  - destruct continuation;cbn in CONTEXT|-*.
    + eapply gateway_reap_post_ambient;eassumption.
    + eapply gateway_reap_context_ambient;[exact thread|exact CONTEXT|exact INTERFERENCE].
    + eapply gateway_reap_context_ambient;[exact thread|exact CONTEXT|exact INTERFERENCE].
    + eapply gateway_reap_context_ambient;[exact thread|exact CONTEXT|exact INTERFERENCE].
    + eapply gateway_reap_context_ambient;[exact thread|exact CONTEXT|exact INTERFERENCE].
    + eapply gateway_reap_context_ambient;[exact thread|exact CONTEXT|exact INTERFERENCE].
Qed.

Lemma gateway_reap_internal_assertion source world trace after:
  gateway_reap_assertion source world->gateway_reap_source_instruction source->internal_state source->
  step2(Clight.globalenv prog)source trace after->gateway_reap_assertion after world.
Proof.
  intros INPUT INSTRUCTION INTERNAL STEP.
  pose proof(proj1 INPUT)as SOURCE.
  assert(CONTEXT:context(memory_of source)world).
  { destruct INPUT as[PROFILE CONTEXT].
    destruct source as[function body continuation environment temporaries memory|
      definition arguments continuation memory|returned continuation memory];try exact CONTEXT;try contradiction.
    destruct continuation;try exact CONTEXT;inversion STEP. }
  assert(NOT_PRIMITIVE:~gateway_at_primitive source)by(apply gateway_internal_excludes_primitive;exact INTERNAL).
  pose proof(gateway_reap_source_internal slots child source trace after SOURCE INSTRUCTION NOT_PRIMITIVE STEP)as AFTER_SOURCE.
  destruct(gateway_reap_internal_memory(Clight.globalenv prog)slots child source trace after
    actual_reap_seconds_layout actual_reap_nanoseconds_layout SOURCE INSTRUCTION NOT_PRIMITIVE STEP)
    as[SAME|[(chunk&position&value&STORE)|(returned&RETURNED&FREE)]].
  - apply gateway_reap_assertion_context;[exact AFTER_SOURCE|rewrite SAME;exact CONTEXT].
  - apply gateway_reap_assertion_context;[exact AFTER_SOURCE|].
    eapply gateway_reap_context_store;[exact thread|exact SCOPE|exact CONTEXT|exact STORE].
  - destruct after;inversion RETURNED;subst;split;[exact AFTER_SOURCE|].
    eapply gateway_reap_context_free;[exact thread|exact SCOPE|exact CONTEXT|exact FREE].
Qed.

Lemma gateway_reap_actual_external ef types result_type convention arguments continuation before world
    result after next observed:
  gateway_reap_assertion(Callstate(External ef types result_type convention)arguments continuation before)world->
  gateway_external backend ef types result_type convention arguments before world result after next observed->
  gateway_reap_assertion(Returnstate result continuation after)next /\io observed=None.
Proof.
  intros[[[site[DEFINITION ARGUMENTS]]FRAME]CONTEXT]OPERATION.
  assert(NOT_CLOCK:site<>reap_site_clock)by(intro SAME;subst site;discriminate).
  assert(API:gateway_runtime_operation backend(reap_site_definition site)(reap_site_values slots child site)
    before world result after next observed).
  { rewrite <-DEFINITION,<-ARGUMENTS;exact OPERATION. }
  destruct(gateway_reap_api_effect backend io observation native stable discipline thread_errno thread runtime
    saved slots allocated allocation_world readonly selected reference owner allocation_before child site
    before world result after next observed CHILD NOT_CLOCK ALLOCATION SCOPE CONTEXT API)as[AFTER IO].
  split;[apply gateway_reap_assertion_context;[right;exact FRAME|exact AFTER]|exact IO].
Qed.

Lemma gateway_reap_regular_instruction source:
  gateway_reap_regular source->internal_state source->gateway_reap_source_instruction source.
Proof.
  destruct source as[function body continuation environment temporaries memory|
    definition arguments continuation memory|returned continuation memory];cbn;[tauto|destruct definition;tauto|tauto].
Qed.

Theorem gateway_reap_regular_step source world event after descriptor:
  gateway_reap_assertion source world->gateway_reap_regular source->
  gateway_step backend(Clight.globalenv prog)(gateway_live source world)event after->
  gateway_reap_state after /\gateway_received_event io descriptor event=[].
Proof.
  intros READY REGULAR STEP;inversion STEP;subst;cbn[gateway_reap_state].
  - split;[eapply gateway_reap_internal_assertion;
      [exact READY|eapply gateway_reap_regular_instruction;eassumption|eassumption|eassumption]|reflexivity].
  - match goal with API:gateway_external _ _ _ _ _ _ _ _ _ _ _ _|-_=>
      destruct(gateway_reap_actual_external _ _ _ _ _ _ _ _ _ _ _ _ READY API)as[AFTER IO]end.
    split;[exact AFTER|unfold gateway_received_event;rewrite IO;reflexivity].
  - destruct READY as[[FUNCTION[ENV[PARAMETER[BODY CONT]]]]CONTEXT];contradiction.
  - split;[eapply gateway_reap_assertion_ambient;eassumption|reflexivity].
  - split;[exact READY|reflexivity].
  - split;[exact I|reflexivity].
  - match goal with API:gateway_external _ _ _ _ _ _ _ _ _ _ _ _|-_=>
      destruct(gateway_reap_actual_external _ _ _ _ _ _ _ _ _ _ _ _ READY API)as[AFTER IO]end.
    split;[exact I|unfold gateway_received_event;rewrite IO;reflexivity].
  - destruct READY as[[FUNCTION[ENV[PARAMETER[BODY CONT]]]]CONTEXT];contradiction.
Qed.

End ReapState.
