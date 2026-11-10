(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual SDK comparison decides equality of the same reply magic. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Events Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayOperations GatewayReadonly GatewayThreadRuntime GatewayStreamInterface
  GatewayReadContext GatewayRuntime GatewayBootstrapABI GatewayBootstrapRuntime GatewayBootstrapRetention GatewayResponseLiteral
  GatewayResponseWord GatewayResponseCompareSource GatewayPrimitiveCalls GatewayPrimitiveQuiet GatewaySendRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_response_compare_context {World}native stable discipline stream response readonly initial bytes magic memory world:=
  @gateway_response_context World native stable discipline stream response readonly initial bytes memory world /\
  gateway_bootstrap_protected native stable memory world(Vptr magic Ptrofs.zero)gateway_response_magic.

Lemma gateway_response_compare_preserved {World}native stable discipline stream response readonly initial bytes magic before world after next:
  @gateway_response_compare_context World native stable discipline stream response readonly initial bytes magic before world->
  discipline None after next->gateway_access_retained native stable before world next->
  gateway_native_frame native stable gateway_native_no_output world before after->
  gateway_response_compare_context native stable discipline stream response readonly initial bytes magic after next.
Proof.
  intros[RESPONSE MAGIC]SIDE ACCESS FRAME;split.
  - eapply gateway_response_context_preserved;[exact RESPONSE|exact SIDE|exact ACCESS|exact FRAME].
  - eapply gateway_bootstrap_protected_retained;[exact MAGIC|exact ACCESS|exact FRAME].
Qed.

Lemma gateway_response_compare_ambient {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)stream response readonly initial bytes magic:
  gateway_runtime_discipline backend(gateway_response_compare_context native stable discipline stream response readonly initial bytes magic).
Proof.
  intros before world after next GOOD INTERFERENCE.
  destruct(gateway_thread_ambient _ _ _ _ _ _ runtime None before world after next(proj1(proj1(proj1 GOOD)))INTERFERENCE)
    as[SIDE[ACCESS FRAME]].
  exact(gateway_response_compare_preserved native stable discipline stream response readonly initial bytes magic
    before world after next GOOD SIDE ACCESS FRAME).
Qed.

Lemma gateway_response_compare_input {World}native stable discipline stream response readonly initial bytes before world:
  Z.of_nat(length bytes)=24->
  @gateway_response_context World native stable discipline stream response readonly initial bytes before world->
  gateway_bootstrap_protected native stable before world(Vptr response Ptrofs.zero)(firstn 8 bytes).
Proof.
  intros LENGTH[RAW LOADED].
  destruct(gateway_response_word_slice before response bytes 0 8 LENGTH ltac:(lia)LOADED)as[COUNT LOAD].
  change(length(firstn 8 bytes)=8%nat)in COUNT;change(Mem.loadbytes before response 0 8=Some(Memdata.inj_bytes(firstn 8 bytes)))in LOAD.
  exists response,Ptrofs.zero;split;[reflexivity|]. split.
  - exists response,Ptrofs.zero;split;[reflexivity|]. split.
    + rewrite COUNT;change(8<=18446744073709551616);lia.
    + rewrite COUNT;exact LOAD.
  - intros position RANGE;left;exact(proj1(proj2(proj2 RAW))).
Qed.

Theorem actual_response_compare {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno module_filename canonicalizes
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    (strings:gateway_bootstrap_runtime backend io native stable discipline module_filename canonicalizes)
    stream response readonly initial bytes magic before world events returned after next:
  Z.of_nat(length bytes)=24->
  gateway_response_compare_context native stable discipline stream response readonly initial bytes magic before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(gateway_bootstrap_signature gateway_memory_compare_api)(response_compare_arguments response magic)Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next)->
  (exists status,returned=Vint status /\(status=Int.zero<->firstn 8 bytes=gateway_response_magic)) /\
  gateway_response_compare_context native stable discipline stream response readonly initial bytes magic after next /\
  gateway_received_bytes io(stream_descriptor initial)events=[] /\gateway_sent_bytes io(stream_descriptor initial)events=[].
Proof.
  intros LENGTH READY RUN.
  set(context:=gateway_response_compare_context native stable discipline stream response readonly initial bytes magic).
  assert(CLOSED:gateway_runtime_discipline backend context).
  { apply gateway_response_compare_ambient with(io:=io)(thread_errno:=thread_errno);exact runtime. }
  assert(EFFECT:forall memory current result changed future observed,context memory current->
    gateway_bootstrap_operation backend gateway_memory_compare_api(response_compare_arguments response magic)
      memory current result changed future observed->
    gateway_bootstrap_post io native stable discipline gateway_native_no_output memory current changed future observed /\
    exists status,result=Vint status /\(status=Int.zero<->firstn 8 bytes=gateway_response_magic)).
  { intros memory current result changed future observed[INPUT MAGIC]OPERATION.
    assert(COUNT:length(firstn 8 bytes)=8%nat)by(rewrite length_firstn;lia).
    eapply gateway_memory_compare_operation with(first:=Vptr response Ptrofs.zero)(second:=Vptr magic Ptrofs.zero).
    - exact strings.
    - exact(proj1(proj1 INPUT)).
    - eapply gateway_response_compare_input;[exact LENGTH|exact INPUT].
    - exact MAGIC.
    - rewrite COUNT;reflexivity.
    - rewrite COUNT;change(8<=18446744073709551615);lia.
    - rewrite COUNT;exact OPERATION. }
  destruct(gateway_bootstrap_signature gateway_memory_compare_api)as[function|external types result_type convention]eqn:SIGNATURE;
    [discriminate SIGNATURE|].
  assert(POST:forall memory current result changed future observed,context memory current->
    gateway_external backend external types result_type convention(response_compare_arguments response magic)
      memory current result changed future observed->
    (exists status,result=Vint status /\(status=Int.zero<->firstn 8 bytes=gateway_response_magic)) /\context changed future).
  { intros memory current result changed future observed INPUT OPERATION.
    assert(OP:gateway_bootstrap_operation backend gateway_memory_compare_api(response_compare_arguments response magic)
      memory current result changed future observed).
    { unfold gateway_bootstrap_operation,gateway_runtime_operation;rewrite SIGNATURE;exact OPERATION. }
    destruct(EFFECT memory current result changed future observed INPUT OP)as[[SIDE[ACCESS[FRAME IO]]]VALUE].
    split;[exact VALUE|]. eapply gateway_response_compare_preserved;[exact INPUT|exact SIDE|exact ACCESS|exact FRAME]. }
  destruct(gateway_actual_primitive_context backend(Clight.globalenv prog)external types result_type convention(response_compare_arguments response magic)
    context(fun result memory current=>(exists status,result=Vint status /\(status=Int.zero<->firstn 8 bytes=gateway_response_magic)) /\context memory current)
    CLOSED ltac:(intros result memory current changed future[VALUE INPUT]INTERFERENCE;split;[exact VALUE|eapply CLOSED;eassumption])POST
    before world events returned after next READY RUN)
    as(prefix&suffix&memory&current&changed&future&observed&EVENTS&PENDING&PREFIX&CALLED&OPERATION&OUTPUT&SUFFIX&FINAL).
  assert(OP:gateway_bootstrap_operation backend gateway_memory_compare_api(response_compare_arguments response magic)
    memory current returned changed future observed).
  { unfold gateway_bootstrap_operation,gateway_runtime_operation;rewrite SIGNATURE;exact OPERATION. }
  destruct(EFFECT memory current returned changed future observed CALLED OP)as[[SIDE[ACCESS[FRAME IO]]]VALUE].
  split;[exact(proj1 FINAL)|]. split;[exact(proj2 FINAL)|].
  eapply gateway_external_no_io_projection;[exact EVENTS|exact PENDING|exact IO|exact SUFFIX].
Qed.
