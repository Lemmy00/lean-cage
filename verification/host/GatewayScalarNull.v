(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A failed scalar allocation follows the actual CPython error-call branch. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayScalarAllocationPath GatewayValueEntry GatewayScalarLength
  GatewaySourcePaths GatewaySourceTactics GatewayFramedRuntime GatewayNoMemory GatewayReturns GatewayFrames.
Import ListNotations.

Definition gateway_scalar_buffer_guard:=match gateway_value_scalar_after_allocate with Ssequence first _=>first|_=>Sskip end.
Definition gateway_scalar_after_buffer_guard:=match gateway_value_scalar_after_allocate with Ssequence _ rest=>rest|_=>Sskip end.
Definition gateway_scalar_null_branch:=match gateway_scalar_buffer_guard with Sifthenelse _ first _=>first|_=>Sskip end.
Definition gateway_scalar_no_memory_call:=match gateway_scalar_null_branch with Ssequence first _=>first|_=>Sskip end.
Definition gateway_scalar_no_memory_return:=match gateway_scalar_null_branch with Ssequence _ rest=>rest|_=>Sskip end.
Definition gateway_scalar_null_parameters parameters:=PTree.set _bytes Vnullptr(PTree.set _t'9 Vnullptr parameters).
Definition gateway_scalar_no_memory_cont slots parameters:=
  Kcall(Some _t'10)f_host_value(gateway_value_environment slots)(gateway_scalar_null_parameters parameters)
    (Kseq gateway_scalar_no_memory_return(Kseq gateway_scalar_after_buffer_guard(Kseq gateway_value_after_scalar Kstop))).

Theorem gateway_scalar_null_path {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:Memory.mem->World->Prop)slots parameters memory symbol :
  gateway_ambient_closed backend property ->Genv.find_symbol ge _PyErr_NoMemory=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some gateway_no_memory_definition ->
  gateway_source_path backend ge gateway_no_memory_definition[](gateway_scalar_no_memory_cont slots parameters)property
    (Returnstate Vnullptr(gateway_value_scalar_malloc_cont slots parameters)memory)property.
Proof.
  intros CLOSED SYMBOL FUNCTION.
  eapply gateway_source_same with(target:=State f_host_value Sskip
    (Kseq gateway_value_scalar_assign_buffer(Kseq gateway_value_scalar_after_allocate(Kseq gateway_value_after_scalar Kstop)))
    (gateway_value_environment slots)(PTree.set _t'9 Vnullptr parameters)memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_returnstate|].
  gateway_path_skip CLOSED.
  eapply gateway_source_same with(target:=State f_host_value Sskip
    (Kseq gateway_value_scalar_after_allocate(Kseq gateway_value_after_scalar Kstop))
    (gateway_value_environment slots)(gateway_scalar_null_parameters parameters)memory).
  - exact CLOSED.
  - cbn;tauto.
  - intros;apply certified_set_edge,old_expression_value,value_temp;apply PTree.gss.
  - gateway_path_skip CLOSED.
    change gateway_value_scalar_after_allocate with(Ssequence gateway_scalar_buffer_guard gateway_scalar_after_buffer_guard).
    gateway_path_seq CLOSED.
    eapply gateway_source_same with(target:=State f_host_value gateway_scalar_null_branch
      (Kseq gateway_scalar_after_buffer_guard(Kseq gateway_value_after_scalar Kstop))
      (gateway_value_environment slots)(gateway_scalar_null_parameters parameters)memory).
    + exact CLOSED.
    + cbn;tauto.
    + intros;eapply certified_if_edge with(b:=true).
      * apply old_expression_value;eapply value_unary;[apply value_temp;apply PTree.gss|reflexivity].
      * reflexivity.
    + change gateway_scalar_null_branch with(Ssequence gateway_scalar_no_memory_call gateway_scalar_no_memory_return).
      gateway_path_seq CLOSED.
      eapply gateway_source_same with(target:=Callstate gateway_no_memory_definition[]
        (gateway_scalar_no_memory_cont slots parameters)memory).
      * exact CLOSED.
      * cbn;tauto.
      * intros;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
        -- reflexivity.
        -- apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
        -- apply no_argument_values.
        -- change(Genv.find_funct_ptr ge symbol=Some gateway_no_memory_definition);exact FUNCTION.
        -- reflexivity.
      * apply gateway_source_reached;auto.
Qed.

Lemma gateway_scalar_no_memory_return_path ge slots parameters memory :
  gateway_constant_path ge Vnullptr(Returnstate Vnullptr(gateway_scalar_no_memory_cont slots parameters)memory).
Proof.
  eapply gateway_constant_next with(next:=State f_host_value Sskip
    (Kseq gateway_scalar_no_memory_return(Kseq gateway_scalar_after_buffer_guard(Kseq gateway_value_after_scalar Kstop)))
    (gateway_value_environment slots)(PTree.set _t'10 Vnullptr(gateway_scalar_null_parameters parameters))memory).
  - cbn;tauto.
  - intros;apply unchanged_store_edge,edge_returnstate.
  - eapply gateway_constant_next with(next:=State f_host_value gateway_scalar_no_memory_return
      (Kseq gateway_scalar_after_buffer_guard(Kseq gateway_value_after_scalar Kstop))(gateway_value_environment slots)
      (PTree.set _t'10 Vnullptr(gateway_scalar_null_parameters parameters))memory).
    + cbn;tauto.
    + intros;apply unchanged_store_edge,edge_skip_seq.
    + eapply gateway_constant_at_return with(value:=Vnullptr).
      * reflexivity.
      * intros;apply old_expression_value,value_temp;apply PTree.gss.
      * intros;reflexivity.
Qed.
