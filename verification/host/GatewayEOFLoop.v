(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: A returned successful exchange observed real EOF after all
   retries. *)
From Stdlib Require Import ZArith List Lia Arith.Wf_nat.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewayThreadRuntime GatewayRuntimeABI GatewayReadContext
  GatewayStreamInterface GatewayStreamRelations GatewayReadonly GatewayPrimitiveCalls GatewayBufferReference GatewayTransferMath GatewaySendRuntime
  GatewayExchangeSetup GatewayExchangeTransport GatewayEOFNative GatewayEOFSource GatewayEOFReceiveSource GatewayEOFErrno
  GatewayEOFCountSource GatewayEOFCountPaths GatewayEOFLoopIteration GatewayEOFRetry GatewayErrnoFragment
  GatewayMemoryPrefixes GatewayFramedRuntime.
Import ListNotations.
Open Scope Z_scope.

Section Loop.
Context {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
  (thread:gateway_thread_runtime backend io native stable discipline thread_errno)
  (held:gateway_eof_receive_runtime backend io native stable discipline).
Variables(stream extra:Values.block)(readonly:Values.block->Z->Prop)(reference:mem)(owner:World).
Variables(allocation_before allocated:mem)(environment:env).
Hypotheses
  (ALLOC:alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated)
  (STREAM:environment!_stream=Some(stream,Tstruct _host_stream noattr))
  (EXTRA:environment!_extra=Some(extra,tuchar)).
Local Definition context initial:=gateway_owned_buffer_context native stable discipline stream extra Ptrofs.zero Ptrofs.zero
  initial 1 readonly reference owner None.
Local Lemma context_closed initial:gateway_ambient_closed backend(context initial).
Proof. apply gateway_owned_buffer_context_ambient with(io:=io)(thread_errno:=thread_errno);exact thread. Qed.

Lemma gateway_eof_count_result count descriptor temporaries:
  (exchange_eof_count_temps count(exchange_eof_receive_temps descriptor temporaries))!_result=temporaries!_result.
Proof.
  unfold exchange_eof_count_temps,exchange_eof_receive_temps,exchange_eof_ready_temps.
  do 4(rewrite PTree.gso by discriminate);reflexivity.
Qed.

Theorem actual_eof_loop_before_return fuel:
  forall events,(length events<fuel)%nat->
  forall temporaries initial before world value after next,
  stream_descriptor initial<>stream_control initial->context initial before world->value<>Vnullptr->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_exchange exchange_eof_loop exchange_eof_cont environment temporaries before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists prefix suffix memory current final_temps updated observed,
    events=prefix++suffix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange exchange_eof_loop exchange_eof_cont environment temporaries before)world)prefix
      (gateway_live(State f_host_exchange exchange_cleanup_phase Kstop environment final_temps memory)current) /\
    context updated memory current /\gateway_stream_transport_after initial updated /\
    final_temps!_result=temporaries!_result /\
    gateway_received_bytes io(stream_descriptor initial)prefix=[] /\gateway_sent_bytes io(stream_descriptor initial)prefix=[] /\
    In(gateway_primitive observed)prefix /\io observed=Some(gateway_native_receive(stream_descriptor initial)1 0[]) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange exchange_cleanup_phase Kstop environment final_temps memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  induction fuel as[|fuel IH];intros events LIMIT temporaries initial before world value after next SEPARATE READY NONNULL RUN;[lia|].
  destruct(actual_eof_loop_receive backend io native stable discipline thread_errno thread held stream extra readonly reference owner
    allocation_before allocated environment temporaries initial before world events value after next
    ALLOC STREAM EXTRA SEPARATE READY NONNULL RUN)
    as(p1&r1&m1&w1&updated&count&bytes&E1&RANGE&LENGTH&P1&READ1&SEND1&C1&TRANSPORT&LOAD1&EOF1&S1).
  assert(POSITIVE:(0<length p1)%nat).
  { destruct p1;[inversion P1|cbn;lia]. }
  destruct(actual_eof_count_bound_prefix backend(Clight.globalenv prog)(context updated)(context_closed updated)
    environment(exchange_eof_receive_temps(stream_descriptor updated)temporaries)(Int64.repr count)
    m1 w1 r1 value after next C1 S1)
    as(p2&r2&m2&w2&E2&Q2&P2&C2&S2).
  set(temps:=exchange_eof_count_temps(Int64.repr count)(exchange_eof_receive_temps(stream_descriptor updated)temporaries)).
  assert(COUNT:temps!_count=Some(Vlong(Int64.repr count)))by(apply PTree.gss).
  assert(RESULT:temps!_result=temporaries!_result)by(apply gateway_eof_count_result).
  assert(CASES:count=(-1)\/count=0\/count=1)by lia.
  destruct CASES as[NEGATIVE|[ZERO|ONE]];subst count.
  - assert(EMPTY:bytes=[]);[apply length_zero_iff_nil;lia|]. rewrite EMPTY in READ1.
    assert(ERRNO_LOCAL:environment!___errno_location=None).
    { eapply actual_exchange_setup_unshadowed;[exact ALLOC|cbn;intuition discriminate]. }
    assert(ERRNO_FUNCTION:gateway_function_binding(Clight.globalenv prog)___errno_location gateway_errno_location_definition).
    { apply gateway_actual_function_binding;vm_compute;reflexivity. }
    destruct(actual_eof_negative_retry backend(Clight.globalenv prog)io(context updated)(context_closed updated)
      environment temps m2 w2 r2 value after next ERRNO_LOCAL ERRNO_FUNCTION
      ltac:(intros api_before api_world api_result api_after api_next api_event INPUT API;
        exact(gateway_errno_owned_context backend io native stable discipline thread_errno thread
          stream extra Ptrofs.zero Ptrofs.zero updated 1 readonly reference owner None
          api_before api_world api_result api_after api_next api_event INPUT API))
      COUNT C2 NONNULL S2)
      as(p3&r3&m3&w3&temps3&E3&Q3&P3&C3&F3&S3).
    assert(SMALLER:(length r3<fuel)%nat).
    { rewrite E1,E2,E3 in LIMIT;repeat rewrite length_app in LIMIT;lia. }
    assert(DISTINCT:stream_descriptor updated<>stream_control updated).
    { destruct TRANSPORT as[A[B REST]];rewrite A,B;exact SEPARATE. }
    destruct(IH r3 SMALLER temps3 updated m3 w3 value after next DISTINCT C3 NONNULL S3)
      as(p4&suffix&memory&current&final_temps&final&observed&E4&P4&FINAL&FINAL_TRANSPORT&RESULT4&READ4&SEND4&EOF4&IO4&SUFFIX).
    exists(p1++p2++p3++p4),suffix,memory,current,final_temps,final,observed.
    split;[rewrite E1,E2,E3,E4;repeat rewrite<-app_assoc;reflexivity|]. split.
    + eapply gateway_steps_append;[exact P1|]. eapply gateway_steps_append;[exact P2|].
      eapply gateway_steps_append;[exact P3|exact P4].
    + split;[exact FINAL|]. split;[eapply gateway_transport_transitive;[exact TRANSPORT|exact FINAL_TRANSPORT]|]. split.
      * rewrite RESULT4,(F3 _result ltac:(reflexivity));exact RESULT.
      * split.
        -- rewrite !gateway_received_bytes_append,READ1,(gateway_quiet_received_empty io(stream_descriptor initial)p2 Q2).
           destruct(Q3(stream_descriptor initial))as[A B];rewrite A.
           rewrite<-(gateway_transport_descriptor initial updated TRANSPORT);exact READ4.
        -- split.
           ++ rewrite !gateway_sent_bytes_append,SEND1,(gateway_quiet_sent_empty io(stream_descriptor initial)p2 Q2).
              destruct(Q3(stream_descriptor initial))as[A B];rewrite B.
              rewrite<-(gateway_transport_descriptor initial updated TRANSPORT);exact SEND4.
           ++ split.
              ** apply in_or_app;right;apply in_or_app;right;apply in_or_app;right;exact EOF4.
              ** split;[rewrite<-(gateway_transport_descriptor initial updated TRANSPORT);exact IO4|exact SUFFIX].
  - assert(EMPTY:bytes=[]);[apply length_zero_iff_nil;lia|]. rewrite EMPTY in READ1.
    destruct(gateway_memory_prefix_cut backend(Clight.globalenv prog)_ _ _ _ m2 w2 r2(Returnstate value Kstop after)next
      (actual_eof_zero_source_path backend(Clight.globalenv prog)(context updated)(context_closed updated)environment temps m2 COUNT)
      I C2 S2)
      as(p3&suffix&memory&current&E3&Q3&P3&FINAL&SUFFIX).
    cbn[gateway_replace_memory]in P3,SUFFIX.
    destruct(EOF1 eq_refl)as[observed[OCCURRENCE IO]].
    exists(p1++p2++p3),suffix,memory,current,(exchange_eof_nonnegative_temps temps),updated,observed.
    split;[rewrite E1,E2,E3;repeat rewrite<-app_assoc;reflexivity|]. split.
    + eapply gateway_steps_append;[exact P1|]. eapply gateway_steps_append;[exact P2|exact P3].
    + split;[exact FINAL|]. split;[exact TRANSPORT|]. split.
      * unfold exchange_eof_nonnegative_temps;rewrite PTree.gso by discriminate;exact RESULT.
      * split.
        -- rewrite !gateway_received_bytes_append,READ1,(gateway_quiet_received_empty io(stream_descriptor initial)p2 Q2),
             (gateway_quiet_received_empty io(stream_descriptor initial)p3 Q3);reflexivity.
        -- split.
           ++ rewrite !gateway_sent_bytes_append,SEND1,(gateway_quiet_sent_empty io(stream_descriptor initial)p2 Q2),
                (gateway_quiet_sent_empty io(stream_descriptor initial)p3 Q3);reflexivity.
           ++ split;[apply in_or_app;left;exact OCCURRENCE|]. split;assumption.
  - exfalso;apply NONNULL.
    exact(actual_eof_positive_one_failure backend(Clight.globalenv prog)environment temps m2 COUNT m2 w2 r2 value after next S2).
Qed.

Theorem actual_eof_loop_complete temporaries initial before world events value after next:
  stream_descriptor initial<>stream_control initial->context initial before world->value<>Vnullptr->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_exchange exchange_eof_loop exchange_eof_cont environment temporaries before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists prefix suffix memory current final_temps updated observed,
    events=prefix++suffix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange exchange_eof_loop exchange_eof_cont environment temporaries before)world)prefix
      (gateway_live(State f_host_exchange exchange_cleanup_phase Kstop environment final_temps memory)current) /\
    context updated memory current /\gateway_stream_transport_after initial updated /\
    final_temps!_result=temporaries!_result /\
    gateway_received_bytes io(stream_descriptor initial)prefix=[] /\gateway_sent_bytes io(stream_descriptor initial)prefix=[] /\
    In(gateway_primitive observed)prefix /\io observed=Some(gateway_native_receive(stream_descriptor initial)1 0[]) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange exchange_cleanup_phase Kstop environment final_temps memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof. eapply actual_eof_loop_before_return with(fuel:=S(length events));lia||eassumption. Qed.
End Loop.
