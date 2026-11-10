(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Array success consumes the same actual zero-status append operation. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayPython GatewayObjects GatewayContainerABI
  GatewayContainerArraySource GatewayContainerArrayStatus GatewayObjectExecution GatewaySourcePaths GatewayFramedRuntime.
Import ListNotations.

Theorem gateway_actual_array_append_cut {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects(abi:gateway_container_abi_runtime backend python objects)
    (property:mem->World->Prop)slots parameters parent parent_offset child child_offset values
    before world events value after next append_symbol definition release_symbol release_definition:
  gateway_object_api_definition gateway_api_list_append=Some definition ->gateway_ambient_closed backend property ->
  parameters!_container=Some(Vptr parent parent_offset) ->
  (forall memory current,property memory current ->
    gateway_objects_ready(python current)(objects current)memory /\
    gateway_rooted(python current)(objects current)(Vptr parent parent_offset) /\
    gateway_rooted(python current)(objects current)(Vptr child child_offset) /\
    gateway_object_values(objects current)(Vptr parent parent_offset)=Some(gateway_list_object values)) ->
  (forall memory current,property memory current ->Mem.weak_valid_pointer memory child(Ptrofs.unsigned child_offset)=true) ->
  (forall memory current,property memory current ->Mem.loadv Mint64 memory(Vptr(GatewayValueEntry.gateway_value_tag_slot slots)Ptrofs.zero)=
    Some(Vlong(Int64.repr 7))) ->
  Genv.find_symbol ge _PyList_Append=Some append_symbol ->Genv.find_funct_ptr ge append_symbol=Some definition ->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr);tptr(Tstruct __object noattr)]tint cc_default ->
  Genv.find_symbol ge _Py_DecRef=Some release_symbol ->Genv.find_funct_ptr ge release_symbol=Some release_definition ->
  type_of_fundef release_definition=Tfunction[tptr(Tstruct __object noattr)]tvoid cc_default ->
  property before world ->gateway_steps backend ge
    (gateway_live(Returnstate(Vptr child child_offset)(GatewayContainerLoopSource.gateway_container_first_cont slots parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value<>Vnullptr ->
  exists called_parameters prefix appending suffix append_before append_world append_after append_next,
    events=prefix++appending++suffix /\Forall(fun event=>event=gateway_source E0 \/event=gateway_ambient)prefix /\
    called_parameters!_container=Some(Vptr parent parent_offset) /\called_parameters!_first=Some(Vptr child child_offset) /\
    called_parameters!_stream=parameters!_stream /\called_parameters!_depth=parameters!_depth /\
    called_parameters!_index__1=parameters!_index__1 /\property append_before append_world /\
    gateway_steps backend ge
      (gateway_live(Callstate definition[Vptr parent parent_offset;Vptr child child_offset]Kstop append_before)append_world)appending
      (gateway_live(Returnstate(Vint Int.zero)Kstop append_after)append_next) /\
    gateway_steps backend ge
      (gateway_live(Returnstate(Vint Int.zero)(gateway_container_append_cont slots called_parameters)append_after)append_next)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros DEFINITION CLOSED PARENT INPUTS POINTER LOADED SYMBOL FUNCTION TYPE RELEASE_SYMBOL RELEASE_FUNCTION RELEASE_TYPE INPUT RUN NONNULL.
  destruct(gateway_container_array_append_path backend ge property slots parameters parent parent_offset child child_offset before append_symbol definition
    CLOSED PARENT POINTER LOADED SYMBOL FUNCTION TYPE)
    as(called_parameters &PATH &CALLED_PARENT &CALLED_CHILD &CALLED_STREAM &CALLED_DEPTH &CALLED_INDEX).
  destruct(gateway_source_path_cut backend ge _ _ _ _ _ _ PATH before world events value after next INPUT RUN)
    as(prefix &rest &append_before &append_world &EVENTS &QUIET &PREFIX &READY &FROM_APPEND).
  destruct(gateway_return_cut backend ge definition[Vptr parent parent_offset;Vptr child child_offset]
    (gateway_container_append_cont slots called_parameters)append_before append_world rest(Returnstate value Kstop after)next
    ltac:(cbn;exact I)ltac:(cbn;lia)FROM_APPEND)
    as(appending &suffix &returned &append_after &append_next &REST_EVENTS &APPEND_RUN &REST).
  destruct(gateway_actual_object_integer_return backend ge gateway_api_list_append definition[Vptr parent parent_offset;Vptr child child_offset]
    property append_before append_world appending returned append_after append_next DEFINITION CLOSED
    ltac:(intros memory current raw changed following observed GOOD OPERATION;
      destruct(INPUTS memory current GOOD)as[SIDE[PARENT_ROOT[CHILD_ROOT DESCRIPTION]]];
      eapply gateway_list_append_integer;[exact abi|exact SIDE|exact PARENT_ROOT|exact CHILD_ROOT|exact DESCRIPTION|exact OPERATION])
    READY APPEND_RUN)as[status SAME];subst returned.
  pose proof(gateway_successful_append_status_zero backend ge slots called_parameters status child child_offset append_after append_next suffix value after next
    release_symbol release_definition CALLED_CHILD RELEASE_SYMBOL RELEASE_FUNCTION RELEASE_TYPE REST NONNULL)as ZERO;subst status.
  exists called_parameters,prefix,appending,suffix,append_before,append_world,append_after,append_next.
  split;[rewrite EVENTS,REST_EVENTS;reflexivity|]. split;[exact QUIET|]. split;[exact CALLED_PARENT|]. split;[exact CALLED_CHILD|].
  split;[exact CALLED_STREAM|]. split;[exact CALLED_DEPTH|]. split;[exact CALLED_INDEX|]. split;[exact READY|]. split;assumption.
Qed.
