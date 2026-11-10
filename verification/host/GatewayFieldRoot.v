(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A successful actual bound check leads to the exact retained object. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs
  Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayPython GatewayAllocation GatewayPrefix
  GatewayControl GatewayFieldGuard.
Import ListNotations.
Open Scope Z_scope.

Definition field_incref_call :=
  match field_after_guard with Ssequence call _=>call|_=>Sskip end.
Definition field_after_incref :=
  match field_after_guard with Ssequence _ rest=>rest|_=>Sskip end.
Definition field_checked_values arguments size :=
  PTree.set _t'2 (Vint Int.zero)(field_guard_values arguments size).
Definition field_incref_cont locals arguments size k :=
  Kcall None f_host_field_bytes(field_environment locals)(field_checked_values arguments size)
    (Kseq field_after_incref k).

Lemma actual_field_incref_call (ge:Clight.genv) locals arguments size memory k symbol object objectOffset :
  field_object arguments=Vptr object objectOffset ->
  Genv.find_symbol ge _Py_IncRef=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some python_incref_definition ->
  store_edge ge
    (State f_host_field_bytes field_incref_call(Kseq field_after_incref k)
      (field_environment locals)(field_checked_values arguments size)memory)
    (Callstate python_incref_definition[field_object arguments]
      (field_incref_cont locals arguments size k)memory).
Proof.
  intros OBJECT SYMBOL FUNCTION.
  eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
  - eapply cons_argument_values with(v:=field_object arguments).
    + apply old_expression_value;apply value_temp;reflexivity.
    + rewrite OBJECT;reflexivity.
    + apply no_argument_values.
  - cbn;exact FUNCTION.
  - reflexivity.
Qed.

Theorem actual_field_guard_return_reaches_incref (ge:Clight.genv) locals arguments size memory k
    symbol object objectOffset :
  field_object arguments=Vptr object objectOffset ->
  Genv.find_symbol ge _Py_IncRef=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some python_incref_definition ->
  exists count,store_path ge(fun _=>True)
    (Returnstate(Vint Int.zero)(field_guard_cont locals arguments size k)memory)count
    (Callstate python_incref_definition[field_object arguments]
      (field_incref_cont locals arguments size k)memory).
Proof.
  intros OBJECT SYMBOL FUNCTION.
  exists 6%nat.
  eapply store_next;[exact I|apply unchanged_store_edge,edge_returnstate|].
  eapply store_next;[exact I|apply unchanged_store_edge,edge_skip_seq|].
  eapply store_next;[exact I|eapply certified_if_edge with(v:=Vint Int.zero)(b:=false);
    [apply old_expression_value;apply value_temp;reflexivity|reflexivity]|].
  eapply store_next;[exact I|apply unchanged_store_edge,edge_skip_seq|].
  eapply store_next;[exact I|apply unchanged_store_edge,edge_seq|].
  eapply store_next;[exact I|eapply actual_field_incref_call;eassumption|].
  constructor;exact I.
Qed.

Theorem actual_incref_retains_checked_bytes world next object before after bytes :
  python_values world object=Some(python_byte_value bytes) ->
  python_incref_return world object before next after ->
  python_values next object=Some(python_byte_value bytes) /\
  python_bytes_loaded after bytes /\
  (0<python_native_strong next object)%nat.
Proof.
  intros BYTES CALL.
  destruct(python_incref_supplies_native_reference _ _ _ _ _ CALL)as[NATIVE STRONG].
  assert(SAME:python_values next object=Some(python_byte_value bytes)).
  { rewrite(python_incref_values _ _ _ _ _ CALL);exact BYTES. }
  split;[exact SAME|]. split;[|exact NATIVE].
  destruct(python_incref_next_valid _ _ _ _ _ CALL)as[_[LOADED _]].
  eapply LOADED;eassumption.
Qed.
