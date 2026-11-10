(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Retained caller spans preserve the actual selected C strings. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory.
From HostGateway Require Import GatewayErrorRuntime.
Open Scope Z_scope.

Definition gateway_cstring_covered(readonly:block->Z->Prop)pointer(bytes:list Byte.int):Prop:=
  forall object offset,pointer=Vptr object offset->forall position,
    Ptrofs.unsigned offset<=position<Ptrofs.unsigned offset+Z.of_nat(length bytes)+1->readonly object position.

Theorem gateway_cstring_readonly_retained readonly pointer bytes before after:
  gateway_error_cstring before pointer bytes->gateway_cstring_covered readonly pointer bytes->
  Mem.unchanged_on readonly before after->gateway_error_cstring after pointer bytes.
Proof.
  intros[object[offset[POINTER[NONZERO[BOUND LOADED]]]]]COVER FRAME.
  exists object,offset;split;[exact POINTER|]. split;[exact NONZERO|]. split;[exact BOUND|].
  eapply Mem.loadbytes_unchanged_on;[exact FRAME| |exact LOADED].
  intros position INSIDE;apply(COVER object offset POINTER position);lia.
Qed.
