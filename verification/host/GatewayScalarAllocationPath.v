(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Allocation receives the guarded scalar length plus its terminating byte. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayValueEntry GatewayScalarLength GatewayScalarContext
  GatewayScalarGuards GatewayScalarLimits GatewaySourceDynamic GatewaySourcePaths GatewayFramedRuntime
  GatewayStreamInterface GatewayStreamLayout GatewayThreadRuntime.
Import ListNotations.

Definition gateway_value_scalar_maximum_setup:=match gateway_value_scalar_after_size with Ssequence first _=>first|_=>Sskip end.
Definition gateway_value_scalar_after_maximum:=match gateway_value_scalar_after_size with Ssequence _ rest=>rest|_=>Sskip end.
Definition gateway_value_scalar_bound_test:=match gateway_value_scalar_after_maximum with Ssequence first _=>first|_=>Sskip end.
Definition gateway_value_scalar_after_bound:=match gateway_value_scalar_after_maximum with Ssequence _ rest=>rest|_=>Sskip end.
Definition gateway_value_scalar_allocate:=match gateway_value_scalar_after_bound with Ssequence first _=>first|_=>Sskip end.
Definition gateway_value_scalar_after_allocate:=match gateway_value_scalar_after_bound with Ssequence _ rest=>rest|_=>Sskip end.
Definition gateway_value_scalar_assign_buffer:=match gateway_value_scalar_allocate with Ssequence _ rest=>rest|_=>Sskip end.
Definition gateway_value_scalar_malloc_cont slots parameters:=
  Kcall(Some _t'9)f_host_value(gateway_value_environment slots)parameters
    (Kseq gateway_value_scalar_assign_buffer(Kseq gateway_value_scalar_after_allocate(Kseq gateway_value_after_scalar Kstop))).

Ltac gateway_scalar_finish_malloc ge closed symbol symbol_binding function_binding size memory :=
  lazymatch goal with
  |-gateway_source_path _ _ ?definition ?values ?continuation _ _ _=>
    eapply gateway_source_same with(target:=Callstate definition values continuation memory)
  end;
    [exact closed|cbn;tauto|
      intros;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero);
        [reflexivity|
          apply old_expression_value;eapply value_function;[reflexivity|exact symbol_binding|reflexivity]|
          apply cons_argument_values with(v:=Vlong(Int64.add size Int64.one));
            [gateway_source_dynamic_expression ltac:(fun _=>gateway_scalar_current_loads)
              ltac:(fun _=>gateway_scalar_guard_reduce)|
              rewrite gateway_scalar_allocation_argument;reflexivity|apply no_argument_values]|
          change(Genv.find_funct_ptr ge symbol=Some(External EF_malloc[tulong](tptr tvoid)cc_default));exact function_binding|
          reflexivity]|
      apply gateway_source_reached;auto].

Theorem gateway_scalar_allocation_path {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    io native stable discipline thread_errno(runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    scalar slots arguments parameters stream_block stream_offset initial readonly original size memory symbol :
  gateway_value_stream arguments=Vptr stream_block stream_offset ->parameters!_stream=Some(gateway_value_stream arguments) ->
  stream_member_layout ge _remaining 24 ->
  Genv.find_symbol ge _malloc=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some(External EF_malloc[tulong](tptr tvoid)cc_default) ->
  Int64.ltu(Int64.repr(gateway_scalar_maximum scalar))size=false ->Int64.ltu(stream_remaining initial)size=false ->
  exists called_parameters,gateway_source_path backend ge(External EF_malloc[tulong](tptr tvoid)cc_default)
    [Vlong(Int64.repr(Int64.unsigned size+1))](gateway_value_scalar_malloc_cont slots called_parameters)
    (gateway_value_sized native stable discipline scalar slots stream_block stream_offset initial readonly original size)
    (Returnstate(Vint Int.zero)(gateway_value_scalar_size_cont slots parameters)memory)
    (gateway_value_sized native stable discipline scalar slots stream_block stream_offset initial readonly original size) /\
    called_parameters!_stream=Some(gateway_value_stream arguments).
Proof.
  intros STREAM STREAM_PARAMETER LAYOUT SYMBOL FUNCTION MAXIMUM REMAINING.
  pose proof(gateway_value_sized_ambient backend io native stable discipline thread_errno runtime
    scalar slots stream_block stream_offset initial readonly original size)as CLOSED.
  destruct scalar;eexists.
  all:split;
    [gateway_source_dynamic_call CLOSED ltac:(fun _=>gateway_scalar_current_loads)ltac:(fun _=>gateway_scalar_guard_reduce);
      gateway_scalar_finish_malloc ge CLOSED symbol SYMBOL FUNCTION size memory|
      unfold set_opttemp;repeat rewrite PTree.gso by discriminate;exact STREAM_PARAMETER].
Qed.
