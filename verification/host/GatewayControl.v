(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The real signed-size guard precedes every native field use. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs
  Ctypes Ctypesdefs Cop Clight.
Require Import ClightSteps StoreSteps LocalAccess.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewaySource GatewayImport.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Definition size_bindings (size maximum : Z) : temp_env :=
  PTree.set _maximum (Vlong(Int64.repr maximum))
    (PTree.set _size (Vlong(Int64.repr size)) (PTree.empty Values.val)).

Lemma actual_size_function_entry ge before size maximum :
  function_entry2 ge f_host_gateway_size
    [Vlong(Int64.repr size);Vlong(Int64.repr maximum)]before empty_env
    (size_bindings size maximum)before.
Proof.
  constructor.
  - repeat(apply list_norepet_cons;[cbn;intuition discriminate|]);apply list_norepet_nil.
  - repeat(apply list_norepet_cons;[cbn;intuition discriminate|]);apply list_norepet_nil.
  - unfold list_disjoint,var_names;cbn;intuition.
  - constructor.
  - reflexivity.
Qed.

Lemma size_nonnegative ge le m size :
  0 <= size <= Int64.max_signed -> le ! _size = Some(Vlong(Int64.repr size)) ->
  evaluated ge empty_env le m
    (Ebinop Olt (Etempvar _size tlong) (Econst_int Int.zero tint) tint) (Vint Int.zero).
Proof.
  intros RANGE LOOK. eapply value_binary;[apply value_temp;exact LOOK|constructor|].
  change (Some(Val.of_bool(Int64.lt(Int64.repr size)Int64.zero))=Some(Vint Int.zero)).
  change (0<=size<=9223372036854775807) in RANGE.
  unfold Int64.lt.
  rewrite Int64.signed_repr by(change(-9223372036854775808<=size<=9223372036854775807);lia).
  rewrite Int64.signed_zero,zlt_false by lia. reflexivity.
Qed.

Lemma size_comparison ge le m size maximum :
  0 <= size <= Int64.max_signed -> 0 <= maximum <= Int64.max_signed ->
  le ! _size = Some(Vlong(Int64.repr size)) ->
  le ! _maximum = Some(Vlong(Int64.repr maximum)) ->
  evaluated ge empty_env le m
    (Ebinop Ogt (Ecast(Etempvar _size tlong)tulong) (Etempvar _maximum tulong) tint)
    (Vint(if zlt maximum size then Int.one else Int.zero)).
Proof.
  intros SIZE MAXIMUM LOOK MAXLOOK.
  eapply value_binary.
  - eapply value_cast with(v:=Vlong(Int64.repr size));[apply value_temp;exact LOOK|reflexivity].
  - apply value_temp;exact MAXLOOK.
  - change (Some(Val.of_bool(Int64.ltu(Int64.repr maximum)(Int64.repr size)))=
      Some(Vint(if zlt maximum size then Int.one else Int.zero))).
    change(0<=size<=9223372036854775807)in SIZE.
    change(0<=maximum<=9223372036854775807)in MAXIMUM.
    unfold Int64.ltu.
    rewrite (Int64.unsigned_repr maximum) by(change(0<=maximum<=18446744073709551615);lia).
    rewrite (Int64.unsigned_repr size) by(change(0<=size<=18446744073709551615);lia).
    destruct(zlt maximum size);reflexivity.
Qed.

Theorem actual_size_guard_accepts ge k m size maximum :
  0 <= size <= maximum -> maximum <= Int64.max_signed ->
  path ge
    (State f_host_gateway_size (fn_body f_host_gateway_size) k empty_env
      (size_bindings size maximum)m)
    (Returnstate(Vint Int.zero)(call_cont k)m).
Proof.
  intros BOUNDS MAXIMUM.
  unfold f_host_gateway_size;cbn[fn_body].
  eapply path_next;[apply edge_seq|].
  eapply path_next;[eapply edge_if with(b:=false);[apply size_nonnegative with(size:=size);
    [lia|reflexivity]|reflexivity]|].
  cbn. eapply path_next;[apply edge_skip_seq|].
  eapply path_next;[apply edge_seq|].
  eapply path_next;[eapply edge_if with(b:=false)|].
  - pose proof(size_comparison ge (size_bindings size maximum)m size maximum
      ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(reflexivity)) as VALUE.
    rewrite zlt_false in VALUE by lia. exact VALUE.
  - reflexivity.
  - cbn. eapply path_next;[apply edge_skip_seq|].
    eapply path_next;[eapply edge_return;[constructor|reflexivity]|constructor].
Qed.

Theorem actual_size_guard_rejects_large ge k m size maximum :
  0 <= maximum < size -> size <= Int64.max_signed ->
  path ge
    (State f_host_gateway_size (fn_body f_host_gateway_size) k empty_env
      (size_bindings size maximum)m)
    (Returnstate(Vint(Int.neg Int.one))(call_cont k)m).
Proof.
  intros BOUNDS SIZE.
  unfold f_host_gateway_size;cbn[fn_body].
  eapply path_next;[apply edge_seq|].
  eapply path_next;[eapply edge_if with(b:=false);[apply size_nonnegative with(size:=size);
    [lia|reflexivity]|reflexivity]|].
  cbn. eapply path_next;[apply edge_skip_seq|].
  eapply path_next;[apply edge_seq|].
  eapply path_next;[eapply edge_if with(b:=true)|].
  - pose proof(size_comparison ge (size_bindings size maximum)m size maximum
      ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(reflexivity)) as VALUE.
    rewrite zlt_true in VALUE by lia. exact VALUE.
  - reflexivity.
  - cbn. eapply path_next;[eapply edge_return;
      [eapply value_unary;[constructor|reflexivity]|reflexivity]|constructor].
Qed.

Theorem shared_native_bound_accepts size maximum :
  0 <= size <= maximum ->
  Lean.eq (LeanCage_Host_GatewayChecks_bounded
    (Nat_of_nat(Z.to_nat size))(Nat_of_nat(Z.to_nat maximum))) Bool_true.
Proof.
  intro BOUND.
  change (Lean.eq (Nat_ble (Nat_of_nat(Z.to_nat size))(Nat_of_nat(Z.to_nat maximum))) Bool_true).
  apply Nat_ble_eq_true_of_le,nat_le_Nat_le;rewrite !nat2Natid;lia.
Qed.

Theorem shared_native_bound_is_actual size maximum :
  0 <= size -> 0 <= maximum ->
  Lean.eq (LeanCage_Host_GatewayChecks_bounded
    (Nat_of_nat(Z.to_nat size))(Nat_of_nat(Z.to_nat maximum))) Bool_true ->
  size <= maximum.
Proof.
  intros SIZE MAXIMUM CHECKED.
  change (Lean.eq (Nat_ble (Nat_of_nat(Z.to_nat size))(Nat_of_nat(Z.to_nat maximum))) Bool_true) in CHECKED.
  pose proof(Nat_le_nat_le' _ _(Nat_le_of_ble_eq_true _ _ CHECKED)) as BOUND.
  rewrite !nat2Natid in BOUND;lia.
Qed.

Inductive checked_native_bound size maximum : Prop :=
| checked_native_bound_intro :
  Lean.eq (LeanCage_Host_GatewayChecks_bounded
    (Nat_of_nat(Z.to_nat size))(Nat_of_nat(Z.to_nat maximum))) Bool_true ->
  checked_native_bound size maximum.

Theorem actual_size_guard_shared_connection ge k m size maximum :
  0 <= size <= maximum -> maximum <= Int64.max_signed ->
  path ge
    (State f_host_gateway_size (fn_body f_host_gateway_size) k empty_env
      (size_bindings size maximum)m)
    (Returnstate(Vint Int.zero)(call_cont k)m) /\
  checked_native_bound size maximum.
Proof.
  intros BOUNDS MAXIMUM;split;[apply actual_size_guard_accepts;auto|].
  constructor;apply shared_native_bound_accepts;exact BOUNDS.
Qed.
