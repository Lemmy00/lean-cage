(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Numeric releases retain the allocation counter and vacant
   source places while removing only the selected already-owned operand. *)
From compcert Require Import Values.
From HostGateway Require Import GatewayReferenceLedger.

Lemma gateway_reference_numeric_release_next ledger final owner pointer:
  gateway_reference_apply(gateway_reference_release owner pointer)(gateway_reference_valid ledger)=gateway_reference_valid final->
  gateway_reference_next final=gateway_reference_next ledger.
Proof.
  unfold gateway_reference_apply;destruct(gateway_reference_take owner(gateway_reference_entries ledger))as[[selected remaining]|];[|discriminate].
  destruct(Val.eq pointer(gateway_reference_pointer selected));[|discriminate].
  intro APPLY;injection APPLY as SAME;subst final;reflexivity.
Qed.

Lemma gateway_reference_numeric_release_keeps_vacant ledger final owner pointer place:
  gateway_reference_take place(gateway_reference_entries ledger)=None->
  gateway_reference_apply(gateway_reference_release owner pointer)(gateway_reference_valid ledger)=gateway_reference_valid final->
  gateway_reference_take place(gateway_reference_entries final)=None.
Proof.
  intro VACANT;unfold gateway_reference_apply.
  destruct(gateway_reference_take owner(gateway_reference_entries ledger))as[[selected remaining]|]eqn:TAKE;[|discriminate].
  destruct(Val.eq pointer(gateway_reference_pointer selected));[|discriminate].
  intro APPLY;injection APPLY as SAME;subst final;apply gateway_reference_take_none;intros entry MEMBER.
  apply(proj1(gateway_reference_take_none _ _)VACANT);apply(proj2(gateway_reference_take_members _ _ _ _ TAKE));exact MEMBER.
Qed.
