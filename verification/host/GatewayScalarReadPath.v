(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The payload read uses the same checked scalar buffer and size. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayValueEntry GatewayScalarLength GatewayScalarContext
  GatewayScalarAllocationPath GatewayScalarNull GatewayScalarBuffer GatewaySourceDynamic GatewaySourcePaths
  GatewayFramedRuntime GatewayStreamInterface GatewayThreadRuntime GatewayCheckedCalls GatewayFailurePaths
  GatewayUnaryExpressions.
Import ListNotations.

Definition gateway_scalar_read_test:=match gateway_scalar_after_buffer_guard with
  Ssequence(Ssequence _ test)_=>test|_=>Sskip end.
Definition gateway_scalar_read_failure:=match gateway_scalar_read_test with Sifthenelse _ failure _=>failure|_=>Sskip end.
Definition gateway_scalar_after_read:=match gateway_scalar_after_buffer_guard with Ssequence _ rest=>rest|_=>Sskip end.
Definition gateway_scalar_read_cont slots parameters:=
  Kcall(Some _t'11)f_host_value(gateway_value_environment slots)parameters
    (Kseq gateway_scalar_read_test(Kseq gateway_scalar_after_read(Kseq gateway_value_after_scalar Kstop))).

Lemma gateway_scalar_read_checked slots parameters :gateway_scalar_read_cont slots parameters=
  gateway_checked_call_cont _t'11 f_host_value(gateway_value_environment slots)parameters gateway_scalar_read_failure
    (Kseq gateway_scalar_after_read(Kseq gateway_value_after_scalar Kstop)).
Proof. reflexivity. Qed.

Lemma gateway_scalar_read_failure_null:gateway_must_null gateway_scalar_read_failure.
Proof. vm_compute;tauto. Qed.

Lemma gateway_scalar_buffer_nonnull {World}native stable discipline heap_allocation scalar slots stream_block stream_offset
    initial readonly original size object memory world :
  @gateway_scalar_buffer_ready World native stable discipline heap_allocation scalar slots stream_block stream_offset initial
    readonly original size object memory world ->
  sem_unary_operation Onotbool(Vptr object Ptrofs.zero)(tptr tschar)memory=Some(Vint Int.zero).
Proof.
  intros[_[[_[_[_[BOUND[HEADER OWNED]]]]]REST]].
  assert(VALID:Mem.weak_valid_pointer memory object 0=true).
  { apply Mem.valid_pointer_implies,Mem.valid_pointer_nonempty_perm.
    eapply Mem.perm_implies;[apply(OWNED 0);lia|constructor]. }
  change(option_map(fun flag=>Val.of_bool(negb flag))
    (if Mem.weak_valid_pointer memory object 0 then Some true else None)=Some(Vint Int.zero)).
  rewrite VALID;reflexivity.
Qed.

Theorem gateway_scalar_payload_read_path {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    io native stable discipline thread_errno(runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    heap_allocation scalar slots arguments parameters stream_block stream_offset initial readonly original size object memory symbol :
  gateway_value_stream arguments=Vptr stream_block stream_offset ->parameters!_stream=Some(gateway_value_stream arguments) ->
  Genv.find_symbol ge _host_read=Some symbol ->Genv.find_funct_ptr ge symbol=Some(Internal f_host_read) ->
  exists called_parameters,gateway_source_path backend ge(Internal f_host_read)
    [gateway_value_stream arguments;Vptr object Ptrofs.zero;Vlong size](gateway_scalar_read_cont slots called_parameters)
    (gateway_scalar_buffer_ready native stable discipline heap_allocation scalar slots stream_block stream_offset initial
      readonly original size object)
    (Returnstate(Vptr object Ptrofs.zero)(gateway_value_scalar_malloc_cont slots parameters)memory)
    (gateway_scalar_buffer_ready native stable discipline heap_allocation scalar slots stream_block stream_offset initial
      readonly original size object) /\
    called_parameters!_stream=Some(gateway_value_stream arguments) /\called_parameters!_bytes=Some(Vptr object Ptrofs.zero).
Proof.
  intros STREAM STREAM_PARAMETER SYMBOL FUNCTION.
  pose proof(gateway_scalar_buffer_ambient backend io native stable discipline thread_errno runtime heap_allocation scalar slots
    stream_block stream_offset initial readonly original size object)as CLOSED.
  eexists;split.
  - gateway_source_dynamic_call CLOSED
      ltac:(fun _=>lazymatch goal with
        |-expression_value _ _ _ _ (Evar _size _) _=>apply gateway_value_size_expression;exact(proj2(proj1 H))
        | |-expression_value _ _ _ _ (Eunop _ _ _) _=>
          eapply gateway_unary_expression_value with(value:=Vptr object Ptrofs.zero)(result:=Vint Int.zero);
            [gateway_source_dynamic_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|
              eapply gateway_scalar_buffer_nonnull;exact H]
        end)
      ltac:(fun _=>reflexivity).
    lazymatch goal with |-gateway_source_path _ _ ?definition ?values ?continuation _ _ _=>
      eapply gateway_source_same with(target:=Callstate definition values continuation memory)end.
    + exact CLOSED.
    + cbn;tauto.
    + intros; eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
      * reflexivity.
      * apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
      * apply cons_argument_values with(v:=gateway_value_stream arguments).
        -- apply old_expression_value,value_temp;unfold set_opttemp;repeat rewrite PTree.gso by discriminate;exact STREAM_PARAMETER.
        -- rewrite STREAM;reflexivity.
        -- apply cons_argument_values with(v:=Vptr object Ptrofs.zero).
           ++ gateway_source_dynamic_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
           ++ reflexivity.
           ++ apply cons_argument_values with(v:=Vlong size).
              ** gateway_source_dynamic_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
              ** reflexivity.
              ** apply no_argument_values.
      * change(Genv.find_funct_ptr ge symbol=Some(Internal f_host_read));exact FUNCTION.
      * reflexivity.
    + apply gateway_source_reached;auto.
  - split;unfold set_opttemp;repeat rewrite PTree.gso by discriminate;[exact STREAM_PARAMETER|apply PTree.gss].
Qed.
