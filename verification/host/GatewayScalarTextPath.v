(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Text construction selects the actual strict-mode source literal. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayValueEntry GatewayValueExpressions GatewayScalarLength
  GatewayScalarContext GatewayScalarTerminate GatewayScalarBytesPath GatewaySourceDynamic GatewaySourcePaths GatewayFramedRuntime
  GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.

Theorem gateway_scalar_text_path {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    io native stable discipline thread_errno(runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    heap_allocation slots parameters stream_block stream_offset initial readonly original size object bytes memory symbol definition mode_symbol :
  parameters!_bytes=Some(Vptr object Ptrofs.zero) ->
  Genv.find_symbol ge _PyUnicode_DecodeUTF8=Some symbol ->Genv.find_funct_ptr ge symbol=Some definition ->
  type_of_fundef definition=Tfunction[tptr tschar;tlong;tptr tschar](tptr(Tstruct __object noattr))cc_default ->
  Genv.find_symbol ge ___stringlit_8=Some mode_symbol ->
  exists called_parameters,gateway_source_path backend ge definition[Vptr object Ptrofs.zero;Vlong size;Vptr mode_symbol Ptrofs.zero]
    (gateway_scalar_constructor_cont _t'21 slots called_parameters)
    (gateway_scalar_terminated_ready native stable discipline heap_allocation gateway_scalar_text slots stream_block stream_offset
      initial readonly original size object bytes)
    (gateway_scalar_terminated_state slots size parameters memory)
    (gateway_scalar_terminated_ready native stable discipline heap_allocation gateway_scalar_text slots stream_block stream_offset
      initial readonly original size object bytes) /\called_parameters!_bytes=Some(Vptr object Ptrofs.zero).
Proof.
  intros BUFFER_PARAMETER SYMBOL FUNCTION TYPE MODE.
  pose proof(gateway_scalar_terminated_ambient backend io native stable discipline thread_errno runtime heap_allocation gateway_scalar_text
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
           ++ apply cons_argument_values with(v:=Vptr mode_symbol Ptrofs.zero).
              ** apply location_read_value with(b:=mode_symbol)(ofs:=Ptrofs.zero).
                 --- apply global_location_value;[unfold gateway_value_environment;repeat rewrite PTree.gso by discriminate;apply PTree.gempty|exact MODE].
                 --- apply deref_loc_reference;reflexivity.
              ** reflexivity.
              ** apply no_argument_values.
      * exact FUNCTION.
      * exact TYPE.
    + apply gateway_source_reached;auto.
  - unfold gateway_scalar_terminated_parameters;repeat rewrite PTree.gso by discriminate;exact BUFFER_PARAMETER.
Qed.
