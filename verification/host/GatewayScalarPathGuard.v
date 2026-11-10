(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A positive scan takes the actual path-error branch before cleanup. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayNativeMemory GatewayScalarLength GatewayScalarTerminate
  GatewayScalarPathSource GatewayScalarBytesPath GatewaySourceSegments GatewaySourceTactics GatewayFramedRuntime
  GatewayStreamInterface GatewayThreadRuntime GatewayValueEntry.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_path_scan_failure:=match gateway_path_scan_guard with Sifthenelse _ failed _=>failed|_=>Sskip end.
Definition gateway_path_scan_failed_state slots parameters scanned memory:=State f_host_value gateway_path_scan_failure
  (Kseq gateway_scalar_cleanup(Kseq gateway_value_after_scalar Kstop))(gateway_value_environment slots)
  (set_opttemp(Some _t'24)scanned parameters)memory.

Lemma gateway_scalar_present_scan_pointer {World}native stable discipline heap_allocation scalar slots stream_block stream_offset
    initial readonly original size object bytes memory world earlier later:
  @gateway_scalar_terminated_ready World native stable discipline heap_allocation scalar slots stream_block stream_offset initial readonly original
    size object bytes memory world ->bytes=earlier++Byte.zero::later ->
  bool_val(Vptr object(Ptrofs.add Ptrofs.zero(Ptrofs.repr(Z.of_nat(length earlier)))))(tptr tvoid)memory=Some true.
Proof.
  intros[[[_[[_[PRIVATE[ORIGIN[BOUND[HEADER OWNED]]]]]SEPARATE]][COUNT PAYLOAD]]TERMINATED]BYTES.
  assert(POSITION:0<=Z.of_nat(length earlier)<Int64.unsigned size).
  { rewrite BYTES,length_app in COUNT.
    change(Z.of_nat((length earlier+S(length later))%nat)=Int64.unsigned size)in COUNT.
    rewrite Nat2Z.inj_add,Nat2Z.inj_succ in COUNT;pose proof(Nat2Z.is_nonneg(length earlier));
      pose proof(Nat2Z.is_nonneg(length later));lia. }
  assert(RANGE:0<=Z.of_nat(length earlier)<=Ptrofs.max_unsigned).
  { change Ptrofs.max_unsigned with Int64.max_unsigned;lia. }
  rewrite Ptrofs.add_zero_l.
  change((if Mem.weak_valid_pointer memory object(Ptrofs.unsigned(Ptrofs.repr(Z.of_nat(length earlier))))
    then Some true else None)=Some true).
  rewrite Ptrofs.unsigned_repr by exact RANGE.
  assert(VALID:Mem.weak_valid_pointer memory object(Z.of_nat(length earlier))=true).
  { apply Mem.valid_pointer_implies,Mem.valid_pointer_nonempty_perm.
    eapply Mem.perm_implies;[apply OWNED;lia|constructor]. }
  rewrite VALID;reflexivity.
Qed.

Theorem gateway_path_positive_scan_segment {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    io native stable discipline thread_errno(runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    heap_allocation slots parameters stream_block stream_offset initial readonly original size object bytes memory earlier later:
  bytes=earlier++Byte.zero::later ->
  gateway_source_segment backend ge
    (gateway_scalar_terminated_ready native stable discipline heap_allocation gateway_scalar_path slots stream_block stream_offset initial readonly original
      size object bytes)
    (Returnstate(Vptr object(Ptrofs.add Ptrofs.zero(Ptrofs.repr(Z.of_nat(length earlier)))))(gateway_path_scan_cont slots parameters)memory)
    (gateway_path_scan_failed_state slots parameters(Vptr object(Ptrofs.add Ptrofs.zero(Ptrofs.repr(Z.of_nat(length earlier)))))memory)
    (gateway_scalar_terminated_ready native stable discipline heap_allocation gateway_scalar_path slots stream_block stream_offset initial readonly original
      size object bytes).
Proof.
  intro BYTES.
  pose proof(gateway_scalar_terminated_ambient backend io native stable discipline thread_errno runtime heap_allocation gateway_scalar_path slots
    stream_block stream_offset initial readonly original size object bytes)as CLOSED.
  eapply gateway_segment_same with(next:=State f_host_value Sskip
    (Kseq gateway_path_scan_guard(Kseq gateway_scalar_cleanup(Kseq gateway_value_after_scalar Kstop)))(gateway_value_environment slots)
    (set_opttemp(Some _t'24)(Vptr object(Ptrofs.add Ptrofs.zero(Ptrofs.repr(Z.of_nat(length earlier)))))parameters)memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_returnstate|].
  gateway_segment_skip CLOSED.
  eapply gateway_segment_same with(next:=gateway_path_scan_failed_state slots parameters
    (Vptr object(Ptrofs.add Ptrofs.zero(Ptrofs.repr(Z.of_nat(length earlier)))))memory).
  - exact CLOSED.
  - cbn;tauto.
  - intros changed current READY;eapply certified_if_edge with(b:=true).
    + apply old_expression_value,value_temp;apply PTree.gss.
    + eapply gateway_scalar_present_scan_pointer;[exact READY|exact BYTES].
  - apply gateway_segment_here.
Qed.
