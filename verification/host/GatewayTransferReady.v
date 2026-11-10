(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: A successful positive transfer executes actual readiness
   successfully first. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayOperations GatewayReadonly
  GatewayTransferSource GatewayReturnTypes GatewayGuardReturn.
From HostGateway Require Import GatewayTransferCalls GatewayTransferLoop.
Import ListNotations.
Open Scope Z_scope.

Theorem actual_positive_receive_ready_execution {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    stream_block stream_offset data_block data_offset amount before world events after next
    (ready:mem->World->Prop)(discipline:gateway_runtime_discipline backend ready)symbol :
  ready before world ->0<amount<=Int64.max_unsigned ->
  Genv.find_symbol ge _host_ready=Some symbol ->Genv.find_funct_ptr ge symbol=Some(Internal f_host_ready) ->
  gateway_steps backend ge
    (gateway_live(Callstate(Internal f_host_transfer)
      [Vptr stream_block stream_offset;Vptr data_block data_offset;Vlong(Int64.repr amount);Vint Int.zero]Kstop before)world)
    events(gateway_live(Returnstate(Vint Int.zero)Kstop after)next) ->
  exists prefix readiness_events caller_events called called_world returned_memory returned_world,
    events=prefix++readiness_events++caller_events /\
    Forall(fun event=>event=gateway_source Events.E0 \/event=gateway_ambient)prefix /\
    gateway_steps backend ge
      (gateway_live(Callstate(Internal f_host_transfer)
        [Vptr stream_block stream_offset;Vptr data_block data_offset;Vlong(Int64.repr amount);Vint Int.zero]Kstop before)world)
      prefix(gateway_live(Callstate(Internal f_host_ready)[Vptr stream_block stream_offset;Vint Int.one]
        (transfer_ready_cont(transfer_loop_values(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount))called)
        called_world) /\ready called called_world /\
    gateway_steps backend ge
      (gateway_live(Callstate(Internal f_host_ready)[Vptr stream_block stream_offset;Vint Int.one]Kstop called)called_world)
      readiness_events(gateway_live(Returnstate(Vint Int.zero)Kstop returned_memory)returned_world) /\
    gateway_steps backend ge
      (gateway_live(Returnstate(Vint Int.zero)
        (transfer_ready_cont(transfer_loop_values(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount))returned_memory)
        returned_world)caller_events(gateway_live(Returnstate(Vint Int.zero)Kstop after)next).
Proof.
  intros READY AMOUNT SYMBOL FUNCTION RUN.
  set(temporaries:=transfer_loop_values(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount).
  destruct(gateway_retained_call_ready_cut backend ge ready discipline(Internal f_host_ready)
    [Vptr stream_block stream_offset;Vint Int.one](transfer_ready_cont temporaries)
    (Callstate(Internal f_host_transfer)
      [Vptr stream_block stream_offset;Vptr data_block data_offset;Vlong(Int64.repr amount);Vint Int.zero]Kstop before)
    world events(Vint Int.zero)after next
    (actual_positive_transfer_call_ready_path ge stream_block stream_offset data_block data_offset amount before
      symbol AMOUNT SYMBOL FUNCTION)READY RUN)
    as[prefix[suffix[called[called_world[EVENTS[PURE[PREFIX[INPUT REST]]]]]]]].
  destruct(gateway_return_cut backend ge(Internal f_host_ready)[Vptr stream_block stream_offset;Vint Int.one]
    (transfer_ready_cont temporaries)called called_world suffix(Returnstate(Vint Int.zero)Kstop after)next
    ltac:(reflexivity)ltac:(cbn[transfer_ready_cont gateway_continuation gateway_cont_weight];lia)REST)
    as[readiness_events[caller_events[result[returned_memory[returned_world[SUFFIX[READINESS CALLER]]]]]]].
  pose proof(gateway_actual_int_return backend ge f_host_ready _ _ _ _ _ _ _
    actual_host_ready_return_profile READINESS)as TYPE.
  assert(ZERO:result=Vint Int.zero).
  { eapply gateway_successful_checked_result with(function:=f_host_transfer)(identifier:=_t'2)
      (following:=Kseq transfer_after_ready transfer_iteration_cont);
      [reflexivity|reflexivity|exact TYPE|exact CALLER]. }
  subst result.
  exists prefix,readiness_events,caller_events,called,called_world,returned_memory,returned_world.
  split;[rewrite EVENTS,SUFFIX;reflexivity|]. split;[exact PURE|]. split;[exact PREFIX|].
  split;[exact INPUT|]. split;assumption.
Qed.

Theorem actual_positive_loop_ready_execution {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    temporaries size stream_block stream_offset before world events after next
    (ready:mem->World->Prop)(discipline:gateway_runtime_discipline backend ready)symbol :
  ready before world ->0<size<=Int64.max_unsigned ->temporaries!_size=Some(Vlong(Int64.repr size)) ->
  temporaries!_stream=Some(Vptr stream_block stream_offset) ->temporaries!_sending=Some(Vint Int.zero) ->
  Genv.find_symbol ge _host_ready=Some symbol ->Genv.find_funct_ptr ge symbol=Some(Internal f_host_ready) ->
  gateway_steps backend ge
    (gateway_live(State f_host_transfer transfer_loop transfer_loop_cont empty_env temporaries before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next) ->
  exists prefix readiness_events caller_events called called_world changed changed_world,
    events=prefix++readiness_events++caller_events /\Forall gateway_quiet_event prefix /\
    gateway_steps backend ge
      (gateway_live(State f_host_transfer transfer_loop transfer_loop_cont empty_env temporaries before)world)prefix
      (gateway_live(Callstate(Internal f_host_ready)[Vptr stream_block stream_offset;Vint Int.one]
        (transfer_ready_cont temporaries)called)called_world) /\ready called called_world /\
    gateway_steps backend ge
      (gateway_live(Callstate(Internal f_host_ready)[Vptr stream_block stream_offset;Vint Int.one]Kstop called)called_world)
      readiness_events(gateway_live(Returnstate(Vint Int.zero)Kstop changed)changed_world) /\
    gateway_steps backend ge
      (gateway_live(Returnstate(Vint Int.zero)(transfer_ready_cont temporaries)changed)changed_world)caller_events
      (gateway_live(Returnstate(Vint Int.zero)Kstop after)next).
Proof.
  intros READY SIZE SIZE_LOOK STREAM RECEIVE SYMBOL FUNCTION RUN.
  destruct(gateway_retained_callback_execution backend ge ready discipline
    (State f_host_transfer transfer_loop transfer_loop_cont empty_env temporaries before)world events(Vint Int.zero)after next
    (Internal f_host_ready)[Vptr stream_block stream_offset;Vint Int.one](transfer_ready_cont temporaries)
    ltac:(reflexivity)ltac:(cbn[transfer_ready_cont gateway_cont_weight];lia)READY
    (actual_positive_transfer_loop_ready_path ge temporaries stream_block stream_offset size before symbol
      SIZE SIZE_LOOK STREAM RECEIVE SYMBOL FUNCTION)RUN)
    as[prefix[readiness_events[caller_events[called[called_world[result[changed[changed_world
      [EVENTS[QUIET[PREFIX[CALLED[OPERATION CALLER]]]]]]]]]]]]].
  pose proof(gateway_actual_int_return backend ge f_host_ready _ _ _ _ _ _ _
    actual_host_ready_return_profile OPERATION)as TYPE.
  assert(ZERO:result=Vint Int.zero).
  { eapply gateway_successful_checked_result with(function:=f_host_transfer)(identifier:=_t'2)
      (following:=Kseq transfer_after_ready transfer_iteration_cont);
      [reflexivity|reflexivity|exact TYPE|exact CALLER]. }
  subst result.
  exists prefix,readiness_events,caller_events,called,called_world,changed,changed_world.
  split;[exact EVENTS|]. split;[exact QUIET|]. split;[exact PREFIX|]. split;[exact CALLED|]. split;assumption.
Qed.
