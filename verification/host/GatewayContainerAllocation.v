(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual guarded tag selects the empty builtin container constructor. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayObjects GatewayValueEntry GatewayContainerLength
  GatewayContainerGuards GatewaySourceDynamic GatewaySourcePaths GatewayFramedRuntime GatewayStreamInterface GatewayStreamLayout GatewayThreadRuntime.
Import ListNotations.

Definition gateway_container_api container:=
  match container with gateway_container_array=>gateway_api_list_new|gateway_container_object=>gateway_api_dict_new end.
Definition gateway_container_constructor_values container :list Values.val:=
  match container with gateway_container_array=>[Vlong Int64.zero]|gateway_container_object=>[]end.
Definition gateway_container_constructor_destination container:=
  match container with gateway_container_array=>_t'30|gateway_container_object=>_t'31 end.
Definition gateway_container_constructor_type container:=
  Tfunction(match container with gateway_container_array=>[tlong]|gateway_container_object=>[]end)
    (tptr(Tstruct __object noattr))cc_default.
Definition gateway_container_after_bound:=match gateway_value_container_after_size with Ssequence _ rest=>rest|_=>Sskip end.
Definition gateway_container_allocate:=match gateway_container_after_bound with Ssequence first _=>first|_=>Sskip end.
Definition gateway_container_after_allocate:=match gateway_container_after_bound with Ssequence _ rest=>rest|_=>Sskip end.
Definition gateway_container_assign:=match gateway_container_allocate with Ssequence _ rest=>rest|_=>Sskip end.
Definition gateway_container_cast container:=Sset _t'29
  (Ecast(Etempvar(gateway_container_constructor_destination container)(tptr(Tstruct __object noattr)))
    (tptr(Tstruct __object noattr))).
Definition gateway_container_constructor_cont container slots parameters:=
  Kcall(Some(gateway_container_constructor_destination container))f_host_value(gateway_value_environment slots)parameters
    (Kseq(gateway_container_cast container)(Kseq gateway_container_assign
      (Kseq gateway_container_after_allocate(Kseq gateway_value_after_container Kstop)))).

Ltac gateway_container_finish_constructor ge closed definition symbol symbol_binding function_binding type_binding memory :=
  lazymatch goal with
  |-gateway_source_path _ _ ?definition ?values ?continuation _ _ _=>
    eapply gateway_source_same with(target:=Callstate definition values continuation memory)
  end;
    [exact closed|cbn;tauto|
      intros;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero);
        [reflexivity|
          apply old_expression_value;eapply value_function;[reflexivity|exact symbol_binding|reflexivity]|
          first[apply no_argument_values|
            eapply cons_argument_values with(v:=Vint Int.zero);[gateway_source_dynamic_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|
              reflexivity|apply no_argument_values]]|
          change(Genv.find_funct_ptr ge symbol=Some definition);exact function_binding|exact type_binding]|
      apply gateway_source_reached;auto].

Theorem gateway_container_allocation_path {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    io native stable discipline thread_errno(runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    container slots arguments parameters stream_block stream_offset initial readonly original size memory symbol definition:
  gateway_value_stream arguments=Vptr stream_block stream_offset ->parameters!_stream=Some(gateway_value_stream arguments) ->
  stream_member_layout ge _nodes 32 ->
  Genv.find_symbol ge(gateway_object_api_ident(gateway_container_api container))=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some definition ->type_of_fundef definition=gateway_container_constructor_type container ->
  Int64.ltu(gateway_container_capacity container(stream_nodes initial))size=false ->
  exists called_parameters,gateway_source_path backend ge definition(gateway_container_constructor_values container)
    (gateway_container_constructor_cont container slots called_parameters)
    (gateway_container_counted native stable discipline container slots stream_block stream_offset initial readonly original size)
    (Returnstate(Vint Int.zero)(gateway_value_container_size_cont slots parameters)memory)
    (gateway_container_counted native stable discipline container slots stream_block stream_offset initial readonly original size) /\
    called_parameters!_stream=Some(gateway_value_stream arguments) /\called_parameters!_depth=parameters!_depth.
Proof.
  intros STREAM STREAM_PARAMETER LAYOUT SYMBOL FUNCTION TYPE BOUND.
  pose proof(gateway_container_counted_ambient backend io native stable discipline thread_errno runtime
    container slots stream_block stream_offset initial readonly original size)as CLOSED.
  destruct container;eexists.
  all:split;
    [gateway_source_dynamic_call CLOSED ltac:(fun _=>gateway_container_current_loads)ltac:(fun _=>gateway_container_guard_reduce);
      gateway_container_finish_constructor ge CLOSED definition symbol SYMBOL FUNCTION TYPE memory|
      split;unfold set_opttemp;repeat rewrite PTree.gso by discriminate;assumption||reflexivity].
Qed.
