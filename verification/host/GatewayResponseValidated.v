(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A header from the same verified writer reaches the actual parser. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewayContexts GatewayReadonly GatewayFramedRuntime GatewaySourcePaths
  GatewayThreadRuntime GatewayStreamInterface GatewayStreamLayout GatewayReadContext GatewayExchangeSetup GatewayExchangeTransport
  GatewayResponseReturn GatewayResponseWord GatewayResponseStatusSource GatewayResponseStatus GatewayResponseLengthSource GatewayResponseLength
  GatewayResponseBudget GatewayResponseCompareSource GatewayResponseCompareRuntime GatewayResponseReservedSource GatewayResponseReserved
  GatewayResponseParserSource GatewayResponseLiteral GatewayResponseProtected GatewayProtectedMemory GatewayProtectedThreads
  GatewayBootstrapRuntime GatewayProtectedBootstrap GatewayBootstrapABI GatewayPrimitiveCalls GatewaySendRuntime GatewayTransferMath.
Import ListNotations.
Open Scope Z_scope.

(* This is an input-data relation. The full caller must derive it from the same
   engine writer and private queue; it asserts no native helper or parser result. *)
Record gateway_response_header_layout(bytes:list Byte.int)(status remaining:int64):Prop:={
  gateway_response_header_magic:firstn 8 bytes=gateway_response_magic;
  gateway_response_header_status:gateway_response_word_value bytes 8 4=Vlong status;
  gateway_response_header_length:gateway_response_word_value bytes 16 8=Vlong remaining;
  gateway_response_header_reserved:gateway_response_word_value bytes 12 4=Vlong Int64.zero;
  gateway_response_header_status_bound:Int64.unsigned status<=3;
  gateway_response_header_length_bound:Int64.unsigned remaining<=536870912
}.

Definition gateway_response_no_io {Event}io descriptor(events:list(gateway_event Event)):Prop:=
  gateway_received_bytes io descriptor events=[] /\gateway_sent_bytes io descriptor events=[].
Lemma gateway_response_no_io_append {Event}io descriptor(first second:list(gateway_event Event)):
  gateway_response_no_io io descriptor first->gateway_response_no_io io descriptor second->
  gateway_response_no_io io descriptor(first++second).
Proof. intros[A B][C D];split;[rewrite gateway_received_bytes_append,A,C|rewrite gateway_sent_bytes_append,B,D];reflexivity. Qed.
Lemma gateway_response_quiet_no_io {Event}io descriptor(events:list(gateway_event Event)):
  Forall gateway_quiet_event events->gateway_response_no_io io descriptor events.
Proof. intro QUIET;split;[apply gateway_quiet_received_empty|apply gateway_quiet_sent_empty];exact QUIET. Qed.

Section ValidatedHeader.
Context {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno module_filename canonicalizes
  (thread:gateway_thread_runtime backend io native stable discipline thread_errno)
  (strings:gateway_bootstrap_runtime backend io native stable discipline module_filename canonicalizes)
  (protected immutable:block->Prop)(snapshot:mem).
Let owned:=gateway_protected_native native protected immutable.
Let side:=gateway_protected_discipline discipline native protected immutable snapshot.
Let runtime:=gateway_protected_threads backend io native stable discipline thread_errno thread protected immutable snapshot.
Let text_runtime:=gateway_protected_bootstrap backend io native stable discipline module_filename canonicalizes strings protected immutable snapshot.

Theorem actual_expected_header_reaches_parser allocation_before allocated environment temporaries stream response magic initial readonly bytes status remaining
    before world events value after next:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  environment!_stream=Some(stream,Tstruct _host_stream noattr)->environment!_response=Some(response,tarray tuchar 24)->
  Genv.find_symbol(Clight.globalenv prog)___stringlit_25=Some magic->protected magic->immutable magic->
  Mem.loadbytes snapshot magic 0 8=Some(inj_bytes gateway_response_magic)->Z.of_nat(length bytes)=24->
  gateway_response_header_layout bytes status remaining->
  gateway_response_context owned stable side stream response readonly initial bytes before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Returnstate(Vint Int.zero)(response_transfer_cont environment temporaries)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists prefix suffix memory current parser_temps,
    events=prefix++suffix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate(Vint Int.zero)(response_transfer_cont environment temporaries)before)world)prefix
      (gateway_live(Callstate(Internal f_host_value)(response_parser_arguments stream)(response_parser_cont environment parser_temps)memory)current) /\
    gateway_response_no_io io(stream_descriptor initial)prefix /\
    parser_temps!_status=Some(Vlong status) /\parser_temps!_failed=Some(Vint Int.zero) /\
    gateway_response_context owned stable side stream response readonly(gateway_response_budget initial remaining)bytes memory current /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(Internal f_host_value)(response_parser_arguments stream)(response_parser_cont environment parser_temps)memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros ALLOC STREAM RESPONSE MAGIC_SYMBOL SELECTED IMMUTABLE MAGIC_LOAD LENGTH
    [MAGIC STATUS SIZE RESERVED STATUS_BOUND SIZE_BOUND]READY RUN.
  destruct(actual_response_status_from_read backend io owned stable side thread_errno runtime allocation_before allocated environment temporaries stream response
    initial readonly bytes before world events value after next ALLOC RESPONSE LENGTH READY RUN)
    as(p1&b1&r1&c1&cw1&m1&w1&E1&Q1&P1&B1&C1&R1).
  rewrite STATUS in B1,R1.
  set(status_temps:=response_header_temps temporaries).
  destruct(actual_response_length_from_status backend io owned stable side thread_errno runtime allocation_before allocated environment status_temps
    (Vlong status)stream response initial readonly bytes m1 w1 r1 value after next ALLOC RESPONSE LENGTH C1 R1)
    as(p2&b2&r2&c2&cw2&m2&w2&E2&Q2&P2&B2&C2&R2).
  rewrite SIZE in B2,R2.
  set(length_temps:=response_length_temps(Vlong status)status_temps).
  set(context:=gateway_response_context owned stable side stream response readonly initial bytes).
  set(updated:=gateway_response_context owned stable side stream response readonly(gateway_response_budget initial remaining)bytes).
  assert(LOCAL_MAGIC:environment!___stringlit_25=None).
  { eapply actual_exchange_setup_unshadowed;[exact ALLOC|cbn;intuition discriminate]. }
  assert(LOCAL_COMPARE:environment!_memcmp=None).
  { eapply actual_exchange_setup_unshadowed;[exact ALLOC|cbn;intuition discriminate]. }
  destruct(gateway_source_path_cut backend(Clight.globalenv prog)(gateway_bootstrap_signature gateway_memory_compare_api)
    (response_compare_arguments response magic)(response_compare_cont environment(PTree.set _t'37(Vlong remaining)length_temps))context
    (Returnstate(Vlong remaining)(response_length_cont environment length_temps)m2)updated
    (actual_response_compare_path backend io owned stable side thread_errno runtime environment length_temps m2 stream response magic initial readonly bytes remaining
      STREAM RESPONSE LOCAL_MAGIC MAGIC_SYMBOL LOCAL_COMPARE)m2 w2 r2 value after next C2 R2)
    as(p3&r3&c3&cw3&E3&Q3&P3&C3&R3).
  cbn[gateway_replace_memory]in P3.
  set(compare_temps:=PTree.set _t'37(Vlong remaining)length_temps).
  destruct(gateway_return_cut backend(Clight.globalenv prog)(gateway_bootstrap_signature gateway_memory_compare_api)(response_compare_arguments response magic)
    (response_compare_cont environment compare_temps)c3 cw3 r3(Returnstate value Kstop after)next I ltac:(cbn;lia)R3)
    as(b3&r4&compared&m3&w3&E4&B3&R4).
  assert(COMPARE_READY:gateway_response_compare_context owned stable side stream response readonly(gateway_response_budget initial remaining)bytes magic c3 cw3).
  { split;[exact C3|].
    eapply gateway_response_literal_from_protected;
      [exact(proj2(proj1(proj1 C3)))|exact SELECTED|exact IMMUTABLE|exact MAGIC_LOAD]. }
  destruct(actual_response_compare backend io owned stable side thread_errno module_filename canonicalizes runtime text_runtime stream response readonly
    (gateway_response_budget initial remaining)bytes magic c3 cw3 b3 compared m3 w3 LENGTH COMPARE_READY B3)
    as[[code[VALUE EQUAL]][COMPARE_FINAL[IN3 OUT3]]].
  assert(ZERO:code=Int.zero)by(apply(proj2 EQUAL);exact MAGIC).
  subst code;subst compared.
  assert(STATUS_LOOK:compare_temps!_status=Some(Vlong status)).
  { unfold compare_temps,length_temps,response_length_temps;rewrite PTree.gso by discriminate;apply PTree.gss. }
  destruct(actual_response_reserved_from_compare backend io owned stable side thread_errno runtime allocation_before allocated environment compare_temps status
    stream response(gateway_response_budget initial remaining)readonly bytes m3 w3 r4 value after next ALLOC RESPONSE LENGTH STATUS_LOOK STATUS_BOUND
    (proj1 COMPARE_FINAL)R4)
    as(p4&b4&r5&c4&cw4&m4&w4&E5&Q4&P4&B4&C4&R5).
  rewrite RESERVED in B4,R5.
  set(reserved_temps:=response_reserved_temps compare_temps).
  assert(FAILED_LOOK:reserved_temps!_failed=Some(Vint Int.zero)).
  { unfold reserved_temps,response_reserved_temps,compare_temps,length_temps,response_length_temps,status_temps,response_header_temps.
    do 6(rewrite PTree.gso by discriminate);apply PTree.gss. }
  assert(PARSER_LOCAL:environment!_host_value=None).
  { eapply actual_exchange_setup_unshadowed;[exact ALLOC|cbn;intuition discriminate]. }
  assert(PARSER_FUNCTION:gateway_function_binding(Clight.globalenv prog)_host_value(Internal f_host_value)).
  { apply gateway_actual_function_binding;vm_compute;reflexivity. }
  assert(UPDATED_CLOSED:gateway_ambient_closed backend updated).
  { apply gateway_response_context_ambient with(io:=io)(thread_errno:=thread_errno);exact runtime. }
  destruct(gateway_source_path_cut backend(Clight.globalenv prog)(Internal f_host_value)(response_parser_arguments stream)
    (response_parser_cont environment(response_parser_temps remaining reserved_temps))updated
    (Returnstate(Vlong Int64.zero)(response_reserved_cont environment reserved_temps)m4)updated
    (actual_response_parser_path backend(Clight.globalenv prog)updated UPDATED_CLOSED environment reserved_temps m4 stream
      (gateway_response_budget initial remaining)STREAM PARSER_LOCAL PARSER_FUNCTION
      (proj1(proj2(proj2(proj2(proj2(proj2 actual_stream_layout))))))FAILED_LOOK SIZE_BOUND
      ltac:(intros memory current GOOD;exact(gateway_read_stream_cells _ _ _ _ _ _ _ _(proj2(proj2(proj2(proj2(proj1 GOOD))))))))
    m4 w4 r5 value after next C4 R5)
    as(p5&suffix&memory&current&E6&Q5&P5&FINAL&SUFFIX).
  cbn[gateway_replace_memory]in P5.
  exists((p1++b1)++(p2++b2)++p3++b3++(p4++b4)++p5),suffix,memory,current,(response_parser_temps remaining reserved_temps).
  split;[rewrite E1,E2,E3,E4,E5,E6;repeat rewrite<-app_assoc;reflexivity|]. split.
  - eapply gateway_steps_append;[eapply gateway_steps_append;[exact P1|
      exact(gateway_plug_steps backend(Clight.globalenv prog)_ _ _(response_status_cont environment status_temps)I B1)]|].
    eapply gateway_steps_append;[eapply gateway_steps_append;[exact P2|
      exact(gateway_plug_steps backend(Clight.globalenv prog)_ _ _(response_length_cont environment length_temps)I B2)]|].
    eapply gateway_steps_append;[exact P3|].
    eapply gateway_steps_append;[exact(gateway_plug_steps backend(Clight.globalenv prog)_ _ _(response_compare_cont environment compare_temps)I B3)|].
    eapply gateway_steps_append;[eapply gateway_steps_append;[exact P4|
      exact(gateway_plug_steps backend(Clight.globalenv prog)_ _ _(response_reserved_cont environment reserved_temps)I B4)]|exact P5].
  - split.
    + apply gateway_response_no_io_append;[apply gateway_response_quiet_no_io;exact Q1|].
      apply gateway_response_no_io_append;[apply gateway_response_quiet_no_io;exact Q2|].
      apply gateway_response_no_io_append;[apply gateway_response_quiet_no_io;exact Q3|].
      apply gateway_response_no_io_append.
      * change(gateway_response_no_io io(stream_descriptor(gateway_response_budget initial remaining))b3);split;assumption.
      * apply gateway_response_no_io_append;[apply gateway_response_quiet_no_io;exact Q4|apply gateway_response_quiet_no_io;exact Q5].
    + split.
      * unfold response_parser_temps,reserved_temps,response_reserved_temps;do 6(rewrite PTree.gso by discriminate);exact STATUS_LOOK.
      * split.
        -- unfold response_parser_temps;do 4(rewrite PTree.gso by discriminate);exact FAILED_LOOK.
        -- split;assumption.
Qed.
End ValidatedHeader.
