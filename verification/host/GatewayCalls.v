(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.acceptance: Actual source argument evaluation produces the nested call. *)
From Stdlib Require Import List Lia.
From compcert Require Import AST Values Memory Events Maps Integers Ctypes Ctypesdefs Cop Clight.
Require Import Machine LocalAccess ClightSteps StoreSteps.
From HostGateway Require Import GatewayMachine GatewayContexts GatewayCallPath GatewayOperations GatewayReturns GatewayInstructions.
Import ListNotations.

Theorem gateway_source_call_occurrence {World Event}(backend:gateway_backend World Event)ge
    function destination expression arguments continuation environment temporaries before world events
    returned after final_world :
  gateway_steps backend ge
    (gateway_live(State function(Scall destination expression arguments)continuation environment temporaries before)world)events
    (gateway_live(Returnstate returned Kstop after)final_world) ->
  exists prefix suffix memory called_world definition values,
    events=prefix++gateway_source E0::suffix /\Forall(fun event=>event=gateway_ambient)prefix /\
    gateway_steps backend ge
      (gateway_live(State function(Scall destination expression arguments)continuation environment temporaries before)world)prefix
      (gateway_live(State function(Scall destination expression arguments)continuation environment temporaries memory)called_world) /\
    step2 ge(State function(Scall destination expression arguments)continuation environment temporaries memory)E0
      (Callstate definition values(Kcall destination function environment temporaries continuation)memory) /\
    gateway_steps backend ge
      (gateway_live(Callstate definition values(Kcall destination function environment temporaries continuation)memory)called_world)
      suffix(gateway_live(Returnstate returned Kstop after)final_world).
Proof.
  revert before world;induction events as[|event rest IH];intros before world RUN.
  - inversion RUN.
  - inversion RUN as[|first observed middle remaining last HEAD TAIL];subst.
    assert(INTERNAL:~gateway_at_primitive
      (State function(Scall destination expression arguments)continuation environment temporaries before))by(cbn;tauto).
    destruct(gateway_nonprimitive_step backend ge _ _ _ _ INTERNAL HEAD)
      as[[trace[next_source[EVENT[REAL TARGET]]]]|
        [[changed[next_world[EVENT[INTERFERENCE TARGET]]]]|[EVENT TARGET]]];subst.
    + inversion REAL;subst;try match goal with BAD:_=_\/_=_|-_=>destruct BAD;discriminate end.
      match goal with CALL:gateway_steps _ _
        (gateway_live(Callstate ?definition ?values _ _)_ )_ _|-_=>
        exists[],rest,before,world,definition,values end.
      cbn;split;[reflexivity|]. split;[constructor|]. split;[constructor|]. split;assumption.
    + cbn[gateway_replace_memory]in TAIL.
      destruct(IH changed next_world TAIL)
        as[prefix[suffix[memory[called_world[definition[values[EVENTS[PENDING[PREFIX[CALL REST]]]]]]]]]].
      exists(gateway_ambient::prefix),suffix,memory,called_world,definition,values.
      split;[cbn;congruence|]. split;[constructor;[reflexivity|exact PENDING]|]. split.
      * econstructor;[apply gateway_interleaved;exact INTERFERENCE|exact PREFIX].
      * split;assumption.
    + destruct(gateway_dead_steps _ _ _ _ _ _ TAIL)as[_ BAD];discriminate.
Qed.


Theorem gateway_ambient_run_ready {World Event}(backend:gateway_backend World Event)ge(ready:mem->World->Prop)
    (discipline:forall before world after next,ready before world ->
      gateway_interference backend before world after next ->ready after next)
    source before world events after next :
  ready before world ->Forall(fun event=>event=gateway_ambient)events ->
  gateway_steps backend ge(gateway_live(gateway_replace_memory source before)world)events
    (gateway_live(gateway_replace_memory source after)next) ->ready after next.
Proof.
  intros READY AMBIENT RUN.
  eapply(GatewayOperations.gateway_pending_run_ready backend ge ready discipline source before world events after next READY);[|exact RUN].
  eapply Forall_impl;[|exact AMBIENT]. intros event SAME;left;exact SAME.
Qed.

Theorem gateway_ignored_call_then_constant_cont {World Event}(backend:gateway_backend World Event)ge
    function expression arguments environment temporaries memory world returned_expression value converted
    events actual after final_world continuation :
  call_cont continuation=Kstop ->
  (forall memory,LocalAccess.expression_value ge environment temporaries memory returned_expression value) ->
  (forall memory,Cop.sem_cast value(typeof returned_expression)(fn_return function)memory=Some converted) ->
  gateway_steps backend ge
    (gateway_live(State function(Scall None expression arguments)
      (Kseq(Sreturn(Some returned_expression))continuation)environment temporaries memory)world)events
    (gateway_live(Returnstate actual Kstop after)final_world) ->actual=converted.
Proof.
  intros CONTINUATION EXPRESSION CAST RUN.
  destruct(gateway_source_call_occurrence backend ge function None expression arguments
    (Kseq(Sreturn(Some returned_expression))continuation)environment temporaries memory world events actual after final_world RUN)
    as[prefix[suffix[called_memory[called_world[definition[values[EVENTS[AMBIENT[PREFIX[CALL REST]]]]]]]]]].
  destruct(gateway_return_cut backend ge definition values
    (Kcall None function environment temporaries(Kseq(Sreturn(Some returned_expression))continuation))
    called_memory called_world suffix(Returnstate actual Kstop after)final_world
    ltac:(reflexivity)ltac:(cbn[gateway_continuation gateway_cont_weight];lia)REST)
    as[callee_events[caller_events[ignored[returned_memory[returned_world[SUFFIX[CALLEE CALLER]]]]]]].
  assert(SCRIPT:GatewayReturns.gateway_constant_path ge converted
    (Returnstate ignored(Kcall None function environment temporaries
      (Kseq(Sreturn(Some returned_expression))continuation))returned_memory)).
  { eapply GatewayReturns.gateway_constant_next with(next:=State function Sskip
      (Kseq(Sreturn(Some returned_expression))continuation)environment temporaries returned_memory).
    - cbn;tauto.
    - intro another;apply StoreSteps.unchanged_store_edge,ClightSteps.edge_returnstate.
    - eapply GatewayReturns.gateway_constant_next with(next:=State function(Sreturn(Some returned_expression))continuation
        environment temporaries returned_memory).
      + cbn;tauto.
      + intro another;apply StoreSteps.unchanged_store_edge,ClightSteps.edge_skip_seq.
      + eapply GatewayReturns.gateway_constant_at_return with(value:=value);[exact CONTINUATION|exact EXPRESSION|exact CAST]. }
  eapply GatewayReturns.gateway_constant_path_actual;[exact SCRIPT|exact CALLER].
Qed.

Theorem gateway_ignored_call_then_constant {World Event}(backend:gateway_backend World Event)ge
    function expression arguments environment temporaries memory world returned_expression value converted
    events actual after final_world :
  (forall memory,LocalAccess.expression_value ge environment temporaries memory returned_expression value) ->
  (forall memory,Cop.sem_cast value(typeof returned_expression)(fn_return function)memory=Some converted) ->
  gateway_steps backend ge
    (gateway_live(State function(Scall None expression arguments)
      (Kseq(Sreturn(Some returned_expression))Kstop)environment temporaries memory)world)events
    (gateway_live(Returnstate actual Kstop after)final_world) ->actual=converted.
Proof.
  intros EXPRESSION CAST RUN.
  eapply gateway_ignored_call_then_constant_cont with(continuation:=Kstop);
    [reflexivity|exact EXPRESSION|exact CAST|exact RUN].
Qed.

Theorem gateway_error_sequence_returns_failure {World Event}(backend:gateway_backend World Event)ge
    function identifier error expression arguments continuation environment temporaries before world
    events returned after final_world :
  fn_return function=Ctypesdefs.tint ->call_cont continuation=Kstop ->
  gateway_steps backend ge
    (gateway_live(State function
      (Ssequence(Ssequence(Sset identifier error)(Scall None expression arguments))
        (Sreturn(Some(Eunop Oneg(Econst_int Integers.Int.one Ctypesdefs.tint)Ctypesdefs.tint))))
      continuation environment temporaries before)world)events
    (gateway_live(Returnstate returned Kstop after)final_world) ->
  returned=Vint(Integers.Int.neg Integers.Int.one).
Proof.
  intros TYPE CONTINUATION RUN.
  set(failure:=Sreturn(Some(Eunop Oneg(Econst_int Integers.Int.one Ctypesdefs.tint)Ctypesdefs.tint))).
  destruct(gateway_uniform_instruction_next backend ge function
    (Ssequence(Ssequence(Sset identifier error)(Scall None expression arguments))failure)
    continuation environment temporaries before world events returned after final_world
    (State function(Ssequence(Sset identifier error)(Scall None expression arguments))
      (Kseq failure continuation)environment temporaries before)
    ltac:(cbn;tauto)ltac:(intro memory;apply unchanged_store_edge,edge_seq)RUN)
    as[prefix1[suffix1[memory1[world1[EVENTS1[AMBIENT1[PREFIX1 REST1]]]]]]].
  cbn[gateway_replace_memory]in REST1.
  destruct(gateway_uniform_instruction_next backend ge function
    (Ssequence(Sset identifier error)(Scall None expression arguments))(Kseq failure continuation)
    environment temporaries memory1 world1 suffix1 returned after final_world
    (State function(Sset identifier error)(Kseq(Scall None expression arguments)(Kseq failure continuation))
      environment temporaries memory1)
    ltac:(cbn;tauto)ltac:(intro memory;apply unchanged_store_edge,edge_seq)REST1)
    as[prefix2[suffix2[memory2[world2[EVENTS2[AMBIENT2[PREFIX2 REST2]]]]]]].
  cbn[gateway_replace_memory]in REST2.
  destruct(gateway_set_result_cut backend ge _ _ _ _ _ _ _ _ _ _ _ _ REST2)
    as[prefix3[suffix3[memory3[world3[value[EVENTS3[AMBIENT3[PREFIX3[VALUE REST3]]]]]]]]].
  destruct(gateway_uniform_instruction_next backend ge function Sskip
    (Kseq(Scall None expression arguments)(Kseq failure continuation))
    environment(PTree.set identifier value temporaries)memory3 world3 suffix3 returned after final_world
    (State function(Scall None expression arguments)(Kseq failure continuation)
      environment(PTree.set identifier value temporaries)memory3)
    ltac:(cbn;tauto)ltac:(intro memory;apply unchanged_store_edge,edge_skip_seq)REST3)
    as[prefix4[suffix4[memory4[world4[EVENTS4[AMBIENT4[PREFIX4 REST4]]]]]]].
  cbn[gateway_replace_memory]in REST4.
  eapply gateway_ignored_call_then_constant_cont with(continuation:=continuation)
    (value:=Vint(Integers.Int.neg Integers.Int.one));[exact CONTINUATION| | |exact REST4].
  - intro memory;apply old_expression_value;eapply value_unary;[constructor|reflexivity].
  - intro memory;rewrite TYPE;reflexivity.
Qed.
