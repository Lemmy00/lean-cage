(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The real scalar source terminates exactly its owned payload buffer. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayValueEntry GatewayScalarLength GatewayScalarContext
  GatewayScalarBuffer GatewayScalarReadPath GatewayScalarPayloadMemory GatewayNativeMemory GatewayHeapMemory GatewaySourceDynamic
  GatewaySourceSegments GatewayFramedRuntime GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_scalar_terminator_setup:=match gateway_scalar_after_read with Ssequence setup _=>setup|_=>Sskip end.
Definition gateway_scalar_after_terminator:=match gateway_scalar_after_read with Ssequence _ rest=>rest|_=>Sskip end.
Definition gateway_scalar_terminator_store:=match gateway_scalar_terminator_setup with Ssequence _ store=>store|_=>Sskip end.
Definition gateway_scalar_terminated_parameters size parameters:=PTree.set _t'75(Vlong size)(PTree.set _t'11(Vint Int.zero)parameters).
Definition gateway_scalar_terminated_state slots size parameters memory:=
  State f_host_value Sskip(Kseq gateway_scalar_after_terminator(Kseq gateway_value_after_scalar Kstop))
    (gateway_value_environment slots)(gateway_scalar_terminated_parameters size parameters)memory.

Definition gateway_scalar_terminated_ready {World}native stable discipline heap_allocation scalar slots stream_block stream_offset
    initial readonly original size object bytes memory world :Prop:=
  @gateway_scalar_payload_ready World native stable discipline heap_allocation scalar slots stream_block stream_offset initial readonly
    original size object bytes memory world /\
    Mem.loadbytes memory object 0(Int64.unsigned size+1)=Some(inj_bytes(bytes++[Byte.zero])).

Lemma gateway_scalar_terminated_ambient {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    heap_allocation scalar slots stream_block stream_offset initial readonly original size object bytes :
  GatewayOperations.gateway_runtime_discipline backend(gateway_scalar_terminated_ready native stable discipline heap_allocation scalar
    slots stream_block stream_offset initial readonly original size object bytes).
Proof.
  intros before world after next[READY BYTES]INTERFERENCE;split.
  - eapply gateway_scalar_payload_ambient;[exact runtime|exact READY|exact INTERFERENCE].
  - destruct READY as[[_[[SIDE[PRIVATE HEAP]]REST]]MORE].
    destruct(gateway_thread_ambient _ _ _ _ _ _ runtime None _ _ _ _ SIDE INTERFERENCE)as[_[_ FRAME]].
    eapply Mem.loadbytes_unchanged_on;[exact FRAME| |exact BYTES].
    intros position RANGE;split;[left;exact PRIVATE|unfold gateway_native_no_output;tauto].
Qed.

Lemma gateway_scalar_terminator_offset size:Ptrofs.unsigned(Ptrofs.of_int64 size)=Int64.unsigned size.
Proof.
  unfold Ptrofs.of_int64;rewrite Ptrofs.unsigned_repr;[reflexivity|].
  change Ptrofs.max_unsigned with Int64.max_unsigned;apply Int64.unsigned_range_2.
Qed.

Lemma gateway_scalar_terminator_access memory object size :
  gateway_heap_block memory object(Int64.unsigned size+1) ->
  Mem.valid_access memory Mint8signed object(Int64.unsigned size)Writable.
Proof.
  intros[BOUND[HEADER OWNED]];split.
  - intros position RANGE;eapply Mem.perm_implies;[apply OWNED;cbn[size_chunk]in RANGE;pose proof(Int64.unsigned_range size);lia|constructor].
  - change(1|Int64.unsigned size);apply Z.divide_1_l.
Qed.

Ltac gateway_scalar_to_terminator closed :=
  lazymatch goal with
  | |-gateway_source_segment _ _ _ (Returnstate ?value ?saved ?memory) _ _=>
      let call:=eval hnf in saved in lazymatch call with
      |Kcall ?destination ?function ?environment ?parameters ?continuation=>
        eapply gateway_segment_same with(next:=State function Sskip continuation environment(set_opttemp destination value parameters)memory);
          [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_returnstate|gateway_scalar_to_terminator closed]
      end
  | |-gateway_source_segment _ _ _ (State ?function ?body ?continuation ?environment ?parameters ?memory) _ _=>
      let statement:=eval hnf in body in lazymatch statement with
      |Ssequence ?first ?rest=>eapply gateway_segment_same with(next:=State function first(Kseq rest continuation)environment parameters memory);
          [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|gateway_scalar_to_terminator closed]
      |Sskip=>lazymatch continuation with
        |Kseq ?following ?rest=>eapply gateway_segment_same with(next:=State function following rest environment parameters memory);
            [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|gateway_scalar_to_terminator closed]
        end
      |Sifthenelse ?expression ?yes ?no=>
        eapply gateway_segment_same with(next:=State function no continuation environment parameters memory);
          [exact closed|cbn;tauto|intros;eapply certified_if_edge with(b:=false);
            [gateway_source_dynamic_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|reflexivity]|
            gateway_scalar_to_terminator closed]
      |Sset ?identifier ?expression=>
        let result:=open_constr:(_ : Values.val)in
        eapply gateway_segment_same with(next:=State function Sskip continuation environment(PTree.set identifier result parameters)memory);
          [exact closed|cbn;tauto|intros;apply certified_set_edge;apply gateway_value_size_expression;
            match goal with GOOD:gateway_scalar_payload_ready _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _|-_=>
              exact(proj2(proj1(proj1 GOOD)))end|
            gateway_scalar_to_terminator closed]
      |Sassign _ _=>idtac
      end
  end.

Theorem gateway_scalar_terminator_segment {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    io native stable discipline thread_errno(runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    heap_allocation scalar slots parameters stream_block stream_offset initial readonly original size object bytes memory :
  parameters!_bytes=Some(Vptr object Ptrofs.zero) ->
  gateway_source_segment backend ge
    (gateway_scalar_payload_ready native stable discipline heap_allocation scalar slots stream_block stream_offset initial readonly
      original size object bytes)
    (Returnstate(Vint Int.zero)(gateway_scalar_read_cont slots parameters)memory)
    (gateway_scalar_terminated_state slots size parameters memory)
    (gateway_scalar_terminated_ready native stable discipline heap_allocation scalar slots stream_block stream_offset initial readonly
      original size object bytes).
Proof.
  intro BUFFER_PARAMETER.
  pose proof(gateway_scalar_payload_ambient backend io native stable discipline thread_errno runtime heap_allocation scalar slots
    stream_block stream_offset initial readonly original size object bytes)as CLOSED.
  gateway_scalar_to_terminator CLOSED.
  eapply gateway_segment_next with(next:=gateway_scalar_terminated_state slots size parameters memory)
    (middle:=gateway_scalar_terminated_ready native stable discipline heap_allocation scalar slots stream_block stream_offset initial
      readonly original size object bytes).
  - exact CLOSED.
  - cbn;tauto.
  - intros changed current READY.
    pose proof READY as[[_[HEAP REST]]MORE].
    destruct(Mem.valid_access_store changed Mint8signed object(Int64.unsigned size)(Vint Int.zero)
      (gateway_scalar_terminator_access changed object size(proj2(proj2(proj2 HEAP)))))as[stored STORE].
    exists stored;split.
    + eapply assignment_source_edge with(b:=object)(ofs:=Ptrofs.of_int64 size)(v:=Vint Int.zero)(w:=Vint Int.zero).
      * apply pointer_location_value;eapply binary_expression_value with(v:=Vptr object Ptrofs.zero)(w:=Vlong size).
        -- apply old_expression_value,value_temp;unfold gateway_scalar_terminated_parameters,set_opttemp;
             repeat rewrite PTree.gso by discriminate;exact BUFFER_PARAMETER.
        -- apply old_expression_value,value_temp;unfold gateway_scalar_terminated_parameters;apply PTree.gss.
        -- change (Some (Vptr object (Ptrofs.add Ptrofs.zero (Ptrofs.mul Ptrofs.one (Ptrofs.of_int64 size)))) =
             Some (Vptr object (Ptrofs.of_int64 size))).
           rewrite Ptrofs.add_zero_l,Ptrofs.mul_commut,Ptrofs.mul_one;reflexivity.
      * apply old_expression_value;apply value_int.
      * reflexivity.
      * apply assign_loc_value with(chunk:=Mint8signed);[reflexivity|].
        unfold Mem.storev;rewrite gateway_scalar_terminator_offset,zle_true;[exact STORE|].
        destruct(proj2(proj2(proj2 HEAP)))as[BOUND REST_HEAP].
        change Ptrofs.modulus with 18446744073709551616;change Int64.max_unsigned with 18446744073709551615 in BOUND;
          cbn[size_chunk];lia.
    + eapply gateway_scalar_buffer_terminate;[exact runtime|exact READY|exact STORE].
  - apply gateway_segment_here.
Qed.
