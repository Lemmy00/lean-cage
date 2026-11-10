(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The bytes constructor receives the actual scalar buffer and decoded size. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayValueEntry GatewayValueExpressions GatewayScalarLength
  GatewayScalarContext GatewayScalarTerminate GatewaySourceDynamic GatewaySourcePaths GatewayFramedRuntime
  GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.

Definition gateway_scalar_cleanup:=match gateway_scalar_after_terminator with
  Ssequence _(Ssequence _ cleanup)=>cleanup|_=>Sskip end.
Definition gateway_scalar_constructor_assign identifier:=
  Sset _value(Etempvar identifier(tptr(Tstruct __object noattr))).
Definition gateway_scalar_constructor_cont identifier slots parameters:=
  Kcall(Some identifier)f_host_value(gateway_value_environment slots)parameters
    (Kseq(gateway_scalar_constructor_assign identifier)(Kseq gateway_scalar_cleanup(Kseq gateway_value_after_scalar Kstop))).

Ltac gateway_scalar_terminated_loads :=
  match goal with GOOD:gateway_scalar_terminated_ready _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _|-_=>
    first[apply gateway_value_tag_expression;exact(proj2(proj1(proj1(proj1(proj1 GOOD)))))|
      apply gateway_value_size_expression;exact(proj2(proj1(proj1(proj1 GOOD))))]end.

Theorem gateway_scalar_bytes_path {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    io native stable discipline thread_errno(runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    heap_allocation slots parameters stream_block stream_offset initial readonly original size object bytes memory symbol definition :
  parameters!_bytes=Some(Vptr object Ptrofs.zero) ->
  Genv.find_symbol ge _PyBytes_FromStringAndSize=Some symbol ->Genv.find_funct_ptr ge symbol=Some definition ->
  type_of_fundef definition=Tfunction[tptr tschar;tlong](tptr(Tstruct __object noattr))cc_default ->
  exists called_parameters,gateway_source_path backend ge definition[Vptr object Ptrofs.zero;Vlong size]
    (gateway_scalar_constructor_cont _t'22 slots called_parameters)
    (gateway_scalar_terminated_ready native stable discipline heap_allocation gateway_scalar_bytes slots stream_block stream_offset
      initial readonly original size object bytes)
    (gateway_scalar_terminated_state slots size parameters memory)
    (gateway_scalar_terminated_ready native stable discipline heap_allocation gateway_scalar_bytes slots stream_block stream_offset
      initial readonly original size object bytes) /\called_parameters!_bytes=Some(Vptr object Ptrofs.zero).
Proof.
  intros BUFFER_PARAMETER SYMBOL FUNCTION TYPE.
  pose proof(gateway_scalar_terminated_ambient backend io native stable discipline thread_errno runtime heap_allocation gateway_scalar_bytes
    slots stream_block stream_offset initial readonly original size object bytes)as CLOSED.
  eexists;split.
  - unfold gateway_scalar_terminated_state.
    gateway_source_dynamic_call CLOSED ltac:(fun _=>gateway_scalar_terminated_loads)ltac:(fun _=>reflexivity).
    lazymatch goal with |-gateway_source_path _ _ ?callee ?values ?continuation _ _ _=>
      eapply gateway_source_same with(target:=Callstate callee values continuation memory)end.
    + exact CLOSED.
    + cbn;tauto.
    + intros;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
      * reflexivity.
      * apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
      * apply cons_argument_values with(v:=Vptr object Ptrofs.zero).
        -- apply old_expression_value,value_temp;unfold gateway_scalar_terminated_parameters;
             repeat rewrite PTree.gso by discriminate;exact BUFFER_PARAMETER.
        -- reflexivity.
        -- apply cons_argument_values with(v:=Vlong size).
           ++ gateway_source_dynamic_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
           ++ reflexivity.
           ++ apply no_argument_values.
      * exact FUNCTION.
      * exact TYPE.
    + apply gateway_source_reached;auto.
  - unfold gateway_scalar_terminated_parameters;repeat rewrite PTree.gso by discriminate;exact BUFFER_PARAMETER.
Qed.
