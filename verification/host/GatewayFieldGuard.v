(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.acceptance: Real API output cells supply the actual native bound call. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs
  Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayPython GatewayAllocation GatewayPrefix GatewayControl.
Import ListNotations.
Open Scope Z_scope.

Definition field_guard_sequence :=
  match field_after_api with Ssequence guard _=>guard|_=>Sskip end.
Definition field_guard_test :=
  match field_guard_sequence with Ssequence _ test=>test|_=>Sskip end.
Definition field_guard_call :=
  match field_guard_sequence with Ssequence(Ssequence _ call)_=>call|_=>Sskip end.
Definition field_after_guard :=
  match field_after_api with Ssequence _ rest=>rest|_=>Sskip end.
Definition field_api_values arguments :=
  PTree.set _t'1 (Vint Int.zero)(field_parameters arguments).
Definition field_guard_values arguments size :=
  PTree.set _t'6 (Vlong(Int64.repr size))(field_api_values arguments).
Definition field_guard_cont locals arguments size k :=
  Kcall(Some _t'2)f_host_field_bytes(field_environment locals)(field_guard_values arguments size)
    (Kseq field_guard_test(Kseq field_after_guard k)).

Lemma actual_field_guard_call (ge:Clight.genv) locals arguments size memory k symbol :
  Genv.find_symbol ge _host_gateway_size=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some(Internal f_host_gateway_size) ->
  store_edge ge
    (State f_host_field_bytes field_guard_call
      (Kseq field_guard_test(Kseq field_after_guard k))
      (field_environment locals)(field_guard_values arguments size)memory)
    (Callstate(Internal f_host_gateway_size)
      [Vlong(Int64.repr size);Vlong(field_maximum arguments)]
      (field_guard_cont locals arguments size k)memory).
Proof.
  intros SYMBOL FUNCTION.
  eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
  - eapply cons_argument_values with(v:=Vlong(Int64.repr size)).
    + apply cast_expression_value with(v:=Vlong(Int64.repr size));
        [apply old_expression_value;apply value_temp;reflexivity|reflexivity].
    + reflexivity.
    + eapply cons_argument_values with(v:=Vlong(field_maximum arguments)).
      * apply cast_expression_value with(v:=Vlong(field_maximum arguments));
          [apply old_expression_value;apply value_temp;reflexivity|reflexivity].
      * reflexivity.
      * apply no_argument_values.
  - cbn;exact FUNCTION.
  - reflexivity.
Qed.

Theorem actual_field_api_return_reaches_guard (ge:Clight.genv) locals arguments size memory k symbol :
  Mem.load Mint64 memory(field_local_size locals)0=Some(Vlong(Int64.repr size)) ->
  Genv.find_symbol ge _host_gateway_size=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some(Internal f_host_gateway_size) ->
  exists count, store_path ge(fun _=>True)
    (Returnstate(Vint Int.zero)(field_api_cont locals arguments k)memory)count
    (Callstate(Internal f_host_gateway_size)
      [Vlong(Int64.repr size);Vlong(field_maximum arguments)]
      (field_guard_cont locals arguments size k)memory).
Proof.
  intros LOAD SYMBOL FUNCTION.
  exists 10%nat.
  eapply store_next;[exact I|apply unchanged_store_edge,edge_returnstate|].
  eapply store_next;[exact I|apply unchanged_store_edge,edge_skip_seq|].
  eapply store_next;[exact I|eapply certified_if_edge with(v:=Vint Int.zero)(b:=false);
    [apply old_expression_value;apply value_temp;reflexivity|reflexivity]|].
  eapply store_next;[exact I|apply unchanged_store_edge,edge_skip_seq|].
  change(store_path ge(fun _=>True)
    (State f_host_field_bytes(Ssequence field_guard_sequence field_after_guard)k
      (field_environment locals)(field_api_values arguments)memory)6%nat
    (Callstate(Internal f_host_gateway_size)
      [Vlong(Int64.repr size);Vlong(field_maximum arguments)]
      (field_guard_cont locals arguments size k)memory)).
  eapply store_next;[exact I|apply unchanged_store_edge,edge_seq|].
  eapply store_next;[exact I|apply unchanged_store_edge,edge_seq|].
  eapply store_next;[exact I|apply unchanged_store_edge,edge_seq|].
  eapply store_next;[exact I|eapply certified_set_edge|].
  - eapply location_read_value with(b:=field_local_size locals)(ofs:=Ptrofs.zero).
    + apply local_location_value;reflexivity.
    + eapply deref_loc_value;[reflexivity|exact LOAD].
  - eapply store_next;[exact I|apply unchanged_store_edge,edge_skip_seq|].
    eapply store_next;[exact I|eapply actual_field_guard_call;eassumption|].
    constructor;exact I.
Qed.

Theorem actual_python_bytes_feed_native_guard (ge:Clight.genv) world next locals arguments
    before after returned k symbol :
  field_local_data locals<>field_local_size locals ->
  python_bytes_return world(field_object arguments)
    (Vptr(field_local_data locals)Ptrofs.zero)(Vptr(field_local_size locals)Ptrofs.zero)
    before returned after next -> returned=Int.zero ->
  Genv.find_symbol ge _host_gateway_size=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some(Internal f_host_gateway_size) ->
  exists bytes count,
    python_values world(field_object arguments)=Some(python_byte_value bytes) /\ next=world /\
    store_path ge(fun _=>True)
      (Returnstate(Vint Int.zero)(field_api_cont locals arguments k)after)count
      (Callstate(Internal f_host_gateway_size)
        [Vlong(Int64.repr(Z.of_nat(List.length(python_bytes_contents bytes))));
         Vlong(field_maximum arguments)]
        (field_guard_cont locals arguments(Z.of_nat(List.length(python_bytes_contents bytes)))k)after).
Proof.
  intros DISTINCT API ZERO SYMBOL FUNCTION.
  destruct(python_bytes_success_loads _ _ _ _ _ _ _ _ DISTINCT API ZERO)
    as[bytes[NEXT[BYTES[DATA SIZE]]]].
  destruct(actual_field_api_return_reaches_guard ge locals arguments
    (Z.of_nat(List.length(python_bytes_contents bytes)))after k symbol SIZE SYMBOL FUNCTION)
    as[count PATH].
  exists bytes,count;auto.
Qed.
