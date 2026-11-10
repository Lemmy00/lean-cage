(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Container success contains its actual nonnull guarded builtin allocation. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayObjects GatewayRegistry GatewayBindings
  GatewayValueEntry GatewayContainerLength GatewayContainerGuards GatewayContainerAllocation GatewayContainerNull GatewaySourcePaths
  GatewayStreamInterface GatewayStreamLayout GatewayFramedRuntime GatewayThreadRuntime.
Import ListNotations.

Lemma actual_gateway_container_binding container:
  exists definition,gateway_object_api_definition(gateway_container_api container)=Some definition /\
    gateway_function_binding(Clight.globalenv prog)(gateway_object_api_ident(gateway_container_api container))definition /\
    type_of_fundef definition=gateway_container_constructor_type container.
Proof.
  destruct container;eexists;split;[reflexivity| |reflexivity|];split;
    [apply gateway_actual_function_binding;vm_compute;reflexivity|reflexivity|
      apply gateway_actual_function_binding;vm_compute;reflexivity|reflexivity].
Qed.

Theorem gateway_actual_container_constructor_cut {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    io native stable discipline thread_errno(runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    container slots arguments parameters stream_block stream_offset initial readonly original size before world events value after next
    symbol definition:
  gateway_value_stream arguments=Vptr stream_block stream_offset ->parameters!_stream=Some(gateway_value_stream arguments) ->
  stream_member_layout ge _nodes 32 ->
  Genv.find_symbol ge(gateway_object_api_ident(gateway_container_api container))=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some definition ->type_of_fundef definition=gateway_container_constructor_type container ->
  gateway_container_counted native stable discipline container slots stream_block stream_offset initial readonly original size before world ->
  gateway_steps backend ge
    (gateway_live(Returnstate(Vint Int.zero)(gateway_value_container_size_cont slots parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value<>Vnullptr ->
  exists called_parameters prefix constructing suffix constructor_before constructor_world result constructor_after constructor_next,
    events=prefix++constructing++suffix /\Forall(fun event=>event=gateway_source E0 \/event=gateway_ambient)prefix /\
    called_parameters!_stream=Some(gateway_value_stream arguments) /\called_parameters!_depth=parameters!_depth /\
    gateway_container_counted native stable discipline container slots stream_block stream_offset initial readonly original size constructor_before constructor_world /\
    gateway_steps backend ge
      (gateway_live(Callstate definition(gateway_container_constructor_values container)Kstop constructor_before)constructor_world)constructing
      (gateway_live(Returnstate result Kstop constructor_after)constructor_next) /\result<>Vnullptr /\
    gateway_steps backend ge
      (gateway_live(Returnstate result(gateway_container_constructor_cont container slots called_parameters)constructor_after)constructor_next)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros STREAM STREAM_PARAMETER LAYOUT SYMBOL FUNCTION TYPE INPUT RUN NONNULL.
  assert(BOUND:Int64.ltu(gateway_container_capacity container(stream_nodes initial))size=false).
  { destruct(Int64.ltu(gateway_container_capacity container(stream_nodes initial))size)eqn:BOUND;[|reflexivity].
    exfalso;apply NONNULL;eapply(gateway_container_bound_failure backend ge io native stable discipline thread_errno runtime
      container slots arguments parameters stream_block stream_offset initial readonly original size before STREAM STREAM_PARAMETER LAYOUT BOUND);
      [exact INPUT|exact RUN]. }
  destruct(gateway_container_allocation_path backend ge io native stable discipline thread_errno runtime container slots arguments parameters
    stream_block stream_offset initial readonly original size before symbol definition STREAM STREAM_PARAMETER LAYOUT SYMBOL FUNCTION TYPE BOUND)
    as(called_parameters &PATH &CALLED_STREAM &CALLED_DEPTH).
  destruct(gateway_source_path_cut backend ge _ _ _ _ _ _ PATH before world events value after next INPUT RUN)
    as(prefix &rest &constructor_before &constructor_world &EVENTS &QUIET &PREFIX &READY &FROM_CONSTRUCTOR).
  destruct(gateway_return_cut backend ge definition(gateway_container_constructor_values container)
    (gateway_container_constructor_cont container slots called_parameters)constructor_before constructor_world rest(Returnstate value Kstop after)next
    ltac:(destruct container;cbn;exact I)ltac:(destruct container;cbn;lia)FROM_CONSTRUCTOR)
    as(constructing &suffix &result &constructor_after &constructor_next &REST_EVENTS &CONSTRUCTOR_RUN &REST).
  assert(CONSTRUCTED:result<>Vnullptr).
  { intro NULL;subst result;apply NONNULL;eapply gateway_actual_container_allocation_failure;exact REST. }
  exists called_parameters,prefix,constructing,suffix,constructor_before,constructor_world,result,constructor_after,constructor_next.
  split;[rewrite EVENTS,REST_EVENTS;reflexivity|]. split;[exact QUIET|]. split;[exact CALLED_STREAM|].
  split;[exact CALLED_DEPTH|]. split;[exact READY|]. split;[exact CONSTRUCTOR_RUN|]. split;assumption.
Qed.
