(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-reporting.proof: Name the actual composite without expanding its proof fields. *)
Definition checked_composite (value : option composite)
 (size : match value with Some co => co_sizeof co | None => 0 end = 144) : composite.
Proof. destruct value as[co|];[exact co|exfalso;discriminate]. Defined.
Lemma checked_composite_present value size : value = Some (checked_composite value size).
Proof. destruct value;[reflexivity|discriminate size]. Qed.
Definition reporting_composite : composite :=
 checked_composite ((genv_cenv result_ge) ! _result) (proj1 result_abi_layout).
Lemma reporting_composite_lookup : (genv_cenv result_ge) ! _result = Some reporting_composite.
Proof. apply checked_composite_present. Qed.
Lemma reporting_composite_members : co_members reporting_composite = result_members.
Proof. unfold result_members;rewrite reporting_composite_lookup;reflexivity. Qed.
