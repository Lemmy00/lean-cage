(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Checked scalar sizes leave room for the actual terminating byte without overflow. *)
From Stdlib Require Import ZArith Lia.
From compcert Require Import Coqlib Integers.
From HostGateway Require Import GatewayScalarLength GatewayScalarGuards.
Open Scope Z_scope.

Lemma gateway_scalar_maximum_range scalar :0<=gateway_scalar_maximum scalar<=268435456.
Proof. destruct scalar;cbn;lia. Qed.

Theorem gateway_scalar_allocation_bound scalar size :
  Int64.unsigned size<=gateway_scalar_maximum scalar ->0<Int64.unsigned size+1<=Int64.max_unsigned.
Proof.
  intro BOUND;pose proof(Int64.unsigned_range size);pose proof(gateway_scalar_maximum_range scalar).
  change Int64.max_unsigned with 18446744073709551615;lia.
Qed.

Theorem gateway_scalar_allocation_argument size :
  Int64.add size Int64.one=Int64.repr(Int64.unsigned size+1).
Proof. unfold Int64.add;rewrite Int64.unsigned_one;reflexivity. Qed.

Theorem gateway_scalar_allocation_unsigned scalar size :
  Int64.unsigned size<=gateway_scalar_maximum scalar ->
  Int64.unsigned(Int64.add size Int64.one)=Int64.unsigned size+1.
Proof.
  intro BOUND;rewrite gateway_scalar_allocation_argument;apply Int64.unsigned_repr.
  pose proof(gateway_scalar_allocation_bound scalar size BOUND);lia.
Qed.
