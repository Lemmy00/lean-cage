(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: Actual outgoing progress derives successful POLLOUT readiness. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayOperations GatewayReadonly
  GatewayTransferSource GatewayReturnTypes GatewayGuardReturn GatewayTransferCalls GatewaySendSource
  GatewayStreamInterface GatewaySendRuntime.
Import ListNotations.
Open Scope Z_scope.

Theorem actual_positive_send_loop_ready_execution {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    temporaries size stream_block stream_offset before world events after next
    (ready:mem->World->Prop)(discipline:gateway_runtime_discipline backend ready)symbol :
  ready before world ->0<size<=Int64.max_unsigned ->temporaries!_size=Some(Vlong(Int64.repr size)) ->
  temporaries!_stream=Some(Vptr stream_block stream_offset) ->temporaries!_sending=Some(Vint Int.one) ->
  Genv.find_symbol ge _host_ready=Some symbol ->Genv.find_funct_ptr ge symbol=Some(Internal f_host_ready) ->
  gateway_steps backend ge
    (gateway_live(State f_host_transfer transfer_loop transfer_loop_cont empty_env temporaries before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next) ->
  exists prefix readiness_events caller_events called called_world changed changed_world,
    events=prefix++readiness_events++caller_events /\Forall gateway_quiet_event prefix /\
    gateway_steps backend ge
      (gateway_live(State f_host_transfer transfer_loop transfer_loop_cont empty_env temporaries before)world)prefix
      (gateway_live(Callstate(Internal f_host_ready)[Vptr stream_block stream_offset;Vint(Int.repr 4)]
        (transfer_send_ready_cont temporaries)called)called_world) /\ready called called_world /\
    gateway_steps backend ge
      (gateway_live(Callstate(Internal f_host_ready)[Vptr stream_block stream_offset;Vint(Int.repr 4)]Kstop called)called_world)
      readiness_events(gateway_live(Returnstate(Vint Int.zero)Kstop changed)changed_world) /\
    gateway_steps backend ge
      (gateway_live(Returnstate(Vint Int.zero)(transfer_send_ready_cont temporaries)changed)changed_world)caller_events
      (gateway_live(Returnstate(Vint Int.zero)Kstop after)next).
Proof.
  intros READY SIZE SIZE_LOOK STREAM RECEIVE SYMBOL FUNCTION RUN.
  destruct(gateway_retained_callback_execution backend ge ready discipline
    (State f_host_transfer transfer_loop transfer_loop_cont empty_env temporaries before)world events(Vint Int.zero)after next
    (Internal f_host_ready)[Vptr stream_block stream_offset;Vint(Int.repr 4)](transfer_send_ready_cont temporaries)
    ltac:(reflexivity)ltac:(cbn[transfer_send_ready_cont gateway_cont_weight];lia)READY
    (actual_positive_send_loop_ready_path ge temporaries stream_block stream_offset size before symbol
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

(* This is supplied by the actual readiness source, not a kernel helper contract. *)
Definition gateway_ready_no_data_send_source {World Event}(backend:gateway_backend World Event)ge
    (io:Event->option gateway_native_io)(native_private:World->block->Prop)
    (stable_readonly:World->block->Z->Prop)(side:mem->World->Prop):Prop:=
  forall before world stream_block stream_offset initial data_block data_offset amount readonly direction
      events after next,
    side before world->native_private world stream_block->native_private world data_block->
    (forall block position,readonly block position->stable_readonly world block position)->
    gateway_read_inputs before stream_block stream_offset initial data_block data_offset amount readonly->
    stream_descriptor initial<>stream_control initial->
    (direction=Int.repr 1 \/direction=Int.repr 4)->
    gateway_steps backend ge
      (gateway_live(Callstate(Internal f_host_ready)[Vptr stream_block stream_offset;Vint direction]Kstop before)world)
      events(gateway_live(Returnstate(Vint Int.zero)Kstop after)next)->
    gateway_sent_bytes io(stream_descriptor initial)events=[].
