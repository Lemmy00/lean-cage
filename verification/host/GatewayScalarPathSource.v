(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Returned path bytes reach the actual NUL scan and filesystem decoder. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayValueEntry GatewayScalarLength GatewayScalarContext
  GatewayScalarTerminate GatewayScalarBytesPath GatewaySourceDynamic GatewaySourcePaths GatewayFramedRuntime
  GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.

Fixpoint gateway_scalar_guard_by_temp(wanted:ident)(body:statement):option statement:=
  match body with
  |Sifthenelse(Etempvar actual _)first second=>if Pos.eqb wanted actual then Some body else
    match gateway_scalar_guard_by_temp wanted first with Some found=>Some found|None=>gateway_scalar_guard_by_temp wanted second end
  |Ssequence first second|Sifthenelse _ first second|Sloop first second=>
    match gateway_scalar_guard_by_temp wanted first with Some found=>Some found|None=>gateway_scalar_guard_by_temp wanted second end
  |_=>None end.
Definition gateway_path_scan_guard:=Eval vm_compute in
  match gateway_scalar_guard_by_temp _t'24 gateway_scalar_after_terminator with Some guard=>guard|None=>Sskip end.
Definition gateway_path_scan_cont slots parameters:=
  Kcall(Some _t'24)f_host_value(gateway_value_environment slots)parameters
    (Kseq gateway_path_scan_guard(Kseq gateway_scalar_cleanup(Kseq gateway_value_after_scalar Kstop))).

Theorem gateway_scalar_path_scan_source {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    io native stable discipline thread_errno(runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    heap_allocation slots parameters stream_block stream_offset initial readonly original size object bytes memory symbol definition:
  parameters!_bytes=Some(Vptr object Ptrofs.zero) ->Genv.find_symbol ge _memchr=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some definition ->
  type_of_fundef definition=Tfunction[tptr tvoid;tint;tulong](tptr tvoid)cc_default ->
  exists called_parameters,gateway_source_path backend ge definition[Vptr object Ptrofs.zero;Vint Int.zero;Vlong size]
    (gateway_path_scan_cont slots called_parameters)
    (gateway_scalar_terminated_ready native stable discipline heap_allocation gateway_scalar_path slots stream_block stream_offset
      initial readonly original size object bytes)
    (gateway_scalar_terminated_state slots size parameters memory)
    (gateway_scalar_terminated_ready native stable discipline heap_allocation gateway_scalar_path slots stream_block stream_offset
      initial readonly original size object bytes) /\
    called_parameters!_bytes=Some(Vptr object Ptrofs.zero) /\called_parameters!_value=Some Vnullptr.
Proof.
  intros BUFFER SYMBOL FUNCTION TYPE.
  pose proof(gateway_scalar_terminated_ambient backend io native stable discipline thread_errno runtime heap_allocation gateway_scalar_path
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
             repeat rewrite PTree.gso by discriminate;exact BUFFER.
        -- reflexivity.
        -- apply cons_argument_values with(v:=Vint Int.zero).
           ++ apply old_expression_value,value_int.
           ++ reflexivity.
           ++ apply cons_argument_values with(v:=Vlong size).
              ** gateway_source_dynamic_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
              ** reflexivity.
              ** apply no_argument_values.
      * exact FUNCTION.
      * exact TYPE.
    + apply gateway_source_reached;auto.
  - split;unfold gateway_scalar_terminated_parameters;
      [repeat rewrite PTree.gso by discriminate;exact BUFFER|repeat rewrite PTree.gso by discriminate;apply PTree.gss].
Qed.

Theorem gateway_scalar_path_decoder_source {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    io native stable discipline thread_errno(runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    heap_allocation slots parameters stream_block stream_offset initial readonly original size object bytes memory symbol definition:
  parameters!_bytes=Some(Vptr object Ptrofs.zero) ->Genv.find_symbol ge _PyUnicode_DecodeFSDefaultAndSize=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some definition ->
  type_of_fundef definition=Tfunction[tptr tschar;tlong](tptr(Tstruct __object noattr))cc_default ->
  exists called_parameters,gateway_source_path backend ge definition[Vptr object Ptrofs.zero;Vlong size]
    (gateway_scalar_constructor_cont _t'23 slots called_parameters)
    (gateway_scalar_terminated_ready native stable discipline heap_allocation gateway_scalar_path slots stream_block stream_offset
      initial readonly original size object bytes)
    (Returnstate Vnullptr(gateway_path_scan_cont slots parameters)memory)
    (gateway_scalar_terminated_ready native stable discipline heap_allocation gateway_scalar_path slots stream_block stream_offset
      initial readonly original size object bytes) /\called_parameters!_bytes=Some(Vptr object Ptrofs.zero).
Proof.
  intros BUFFER SYMBOL FUNCTION TYPE.
  pose proof(gateway_scalar_terminated_ambient backend io native stable discipline thread_errno runtime heap_allocation gateway_scalar_path
    slots stream_block stream_offset initial readonly original size object bytes)as CLOSED.
  eexists;split.
  - gateway_source_dynamic_call CLOSED ltac:(fun _=>gateway_scalar_terminated_loads)ltac:(fun _=>reflexivity).
    lazymatch goal with |-gateway_source_path _ _ ?callee ?values ?continuation _ _ _=>
      eapply gateway_source_same with(target:=Callstate callee values continuation memory)end.
    + exact CLOSED.
    + cbn;tauto.
    + intros;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
      * reflexivity.
      * apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
      * apply cons_argument_values with(v:=Vptr object Ptrofs.zero).
        -- apply old_expression_value,value_temp;unfold set_opttemp;
             repeat rewrite PTree.gso by discriminate;exact BUFFER.
        -- reflexivity.
        -- apply cons_argument_values with(v:=Vlong size).
           ++ gateway_source_dynamic_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
           ++ reflexivity.
           ++ apply no_argument_values.
      * exact FUNCTION.
      * exact TYPE.
    + apply gateway_source_reached;auto.
  - unfold set_opttemp;repeat rewrite PTree.gso by discriminate;exact BUFFER.
Qed.
