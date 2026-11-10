(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Decimal construction uses the same terminated owned buffer;
   canonical decimal syntax is produced by the source scan rather than the SDK contract. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers Values Memory.
From HostGateway Require Import GatewayMachine GatewayPython GatewayObjects GatewayScalarLength GatewayScalarConstructorCalls
  GatewayScalarDecoding.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_scalar_integer_request {World}python objects detached stable heap_allocation slots stream_block stream_offset initial readonly original
    size object bytes memory world decimal_float integer:
  @gateway_scalar_private_ready World python objects detached stable heap_allocation gateway_scalar_long slots stream_block stream_offset initial readonly original
    size object bytes memory world->Int64.unsigned size<=32->gateway_decimal bytes integer->
  gateway_constructor_request decimal_float(objects world)memory gateway_api_long_string
    [Vptr object Ptrofs.zero;Vnullptr;Vint(Int.repr 10)](gateway_long_object integer).
Proof.
  intros READY BOUND DECIMAL;eapply gateway_request_long_string with(bytes:=bytes);[|exact DECIMAL].
  destruct(gateway_scalar_received_object python objects detached stable heap_allocation gateway_scalar_long slots stream_block stream_offset initial readonly original
    size object bytes memory world READY)as(candidate &offset &POINTER &LIVE &RANGE &LOAD).
  inversion POINTER;subst candidate offset.
  pose proof READY as[[[STORAGE[COUNT BYTES]]TERMINATED]PRIVATE].
  exists object,Ptrofs.zero;split;[reflexivity|]. split;[exact LIVE|]. split.
  - change(0+Z.of_nat(length(bytes++[Byte.zero]))<=Ptrofs.modulus).
    rewrite length_app,Nat2Z.inj_add;cbn[length Z.of_nat];change Ptrofs.modulus with 18446744073709551616;lia.
  - change(Mem.loadbytes memory object 0(Z.of_nat(length(bytes++[Byte.zero])))=Some(inj_bytes(bytes++[Byte.zero]))).
    rewrite length_app,Nat2Z.inj_add;cbn[length Z.of_nat];rewrite COUNT;exact TERMINATED.
Qed.
