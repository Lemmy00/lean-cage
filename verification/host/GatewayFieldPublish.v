(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The real publication tail stores the checked buffer and retained owner. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs
  Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayPython GatewayAllocation GatewayPrefix
  GatewayFieldGuard GatewayFieldRoot GatewayFieldStores GatewayFieldStorage GatewayFieldFree GatewayLayout.
Import ListNotations.
Open Scope Z_scope.

Definition field_size_values arguments size:=
  PTree.set _t'4(Vlong(Int64.repr size))(field_checked_values arguments size).
Definition field_published_values arguments size pointer:=
  PTree.set _t'3 pointer(field_size_values arguments size).

Ltac gateway_field_lookup:=
  unfold field_published_values,field_size_values,field_checked_values,field_guard_values,
    field_api_values,field_parameters;
  repeat first[rewrite PTree.gss|rewrite PTree.gso by discriminate];reflexivity.

Ltac field_structural:=
  eapply store_next;[exact I|apply unchanged_store_edge;
    first[apply edge_seq|apply edge_skip_seq|apply edge_returnstate]|].

Theorem actual_field_publication_tail (ge:Clight.genv) locals arguments size before after
    object offset buffer buffer_offset held held_offset continuation ref_result :
  field_target arguments=Vptr object offset ->field_object arguments=Vptr held held_offset ->
  object<>field_local_data locals ->object<>field_local_size locals ->
  field_member_layout ge _kind 0 ->field_member_layout ge _size 8 ->
  field_member_layout ge _data 16 ->field_member_layout ge _root 24 ->
  Mem.load Mint64 before(field_local_size locals)0=Some(Vlong(Int64.repr size)) ->
  Mem.load Mptr before(field_local_data locals)0=Some(Vptr buffer buffer_offset) ->
  field_store_sequence before object offset(field_kind arguments)(Int64.repr size)
    (Vptr buffer buffer_offset)(field_object arguments)after ->
  exists count,store_path ge(fun _=>True)
    (Returnstate ref_result(field_incref_cont locals arguments size continuation)before)count
    (State f_host_field_bytes(Sreturn(Some(Econst_int Int.zero tint)))continuation
      (field_environment locals)(field_published_values arguments size(Vptr buffer buffer_offset))after).
Proof.
  intros TARGET OWNER DATA_DISTINCT SIZE_DISTINCT KIND_LAYOUT SIZE_LAYOUT DATA_LAYOUT ROOT_LAYOUT
    SIZE_LOAD DATA_LOAD[first[second[third[KIND[SIZE[DATA ROOT]]]]]].
  assert(SIZE_FIRST:Mem.load Mint64 first(field_local_size locals)0=Some(Vlong(Int64.repr size))).
  { rewrite(field_store_read_other _ _ _ _ _ _ _ _ _ KIND)by congruence;exact SIZE_LOAD. }
  assert(DATA_SECOND:Mem.load Mptr second(field_local_data locals)0=Some(Vptr buffer buffer_offset)).
  { rewrite(field_store_read_other _ _ _ _ _ _ _ _ _ SIZE)by congruence.
    rewrite(field_store_read_other _ _ _ _ _ _ _ _ _ KIND)by congruence;exact DATA_LOAD. }
  eexists.
  field_structural;field_structural;field_structural.
  eapply store_next;[exact I|eapply actual_field_assignment with
    (object:=object)(offset:=offset)(delta:=0)(chunk:=Mint32)
    (value:=Vint(field_kind arguments))(converted:=Vint(field_kind arguments))|].
  - change((field_checked_values arguments size)!_field=Some(Vptr object offset));
      replace(Vptr object offset)with(field_target arguments)by congruence;gateway_field_lookup.
  - exact KIND_LAYOUT.
  - reflexivity.
  - apply old_expression_value;apply value_temp;gateway_field_lookup.
  - reflexivity.
  - exact KIND.
  - field_structural;field_structural;field_structural.
    eapply store_next;[exact I|eapply certified_set_edge|].
    + eapply location_read_value with(b:=field_local_size locals)(ofs:=Ptrofs.zero).
      * apply local_location_value;reflexivity.
      * eapply deref_loc_value;[reflexivity|exact SIZE_FIRST].
    + field_structural.
      eapply store_next;[exact I|eapply actual_field_assignment with
        (object:=object)(offset:=offset)(delta:=8)(chunk:=Mint64)
        (value:=Vlong(Int64.repr size))(converted:=Vlong(Int64.repr size))|].
      * change((field_size_values arguments size)!_field=Some(Vptr object offset));
          replace(Vptr object offset)with(field_target arguments)by congruence;gateway_field_lookup.
      * exact SIZE_LAYOUT.
      * reflexivity.
      * apply cast_expression_value with(v:=Vlong(Int64.repr size));
          [apply old_expression_value;apply value_temp;gateway_field_lookup|reflexivity].
      * reflexivity.
      * exact SIZE.
      * field_structural;field_structural;field_structural.
        eapply store_next;[exact I|eapply certified_set_edge|].
        -- eapply location_read_value with(b:=field_local_data locals)(ofs:=Ptrofs.zero).
           ++ apply local_location_value;reflexivity.
           ++ eapply deref_loc_value;[reflexivity|exact DATA_SECOND].
        -- field_structural.
           eapply store_next;[exact I|eapply actual_field_assignment with
             (object:=object)(offset:=offset)(delta:=16)(chunk:=Mptr)
             (value:=Vptr buffer buffer_offset)(converted:=Vptr buffer buffer_offset)|].
           ++ change((field_published_values arguments size(Vptr buffer buffer_offset))!_field=
                Some(Vptr object offset));
                replace(Vptr object offset)with(field_target arguments)by congruence;gateway_field_lookup.
           ++ exact DATA_LAYOUT.
           ++ reflexivity.
           ++ apply old_expression_value;apply value_temp;gateway_field_lookup.
           ++ reflexivity.
           ++ exact DATA.
           ++ field_structural;field_structural.
              eapply store_next;[exact I|eapply actual_field_assignment with
                (object:=object)(offset:=offset)(delta:=24)(chunk:=Mptr)
                (value:=field_object arguments)(converted:=field_object arguments)|].
              ** change((field_published_values arguments size(Vptr buffer buffer_offset))!_field=
                   Some(Vptr object offset));
                   replace(Vptr object offset)with(field_target arguments)by congruence;gateway_field_lookup.
              ** exact ROOT_LAYOUT.
              ** reflexivity.
              ** apply old_expression_value;apply value_temp;gateway_field_lookup.
              ** rewrite OWNER;reflexivity.
              ** exact ROOT.
              ** field_structural;constructor;exact I.
Qed.

Theorem actual_field_publication_from_storage (ge:Clight.genv) locals arguments size before capacity
    object offset buffer buffer_offset held held_offset continuation ref_result :
  field_target arguments=Vptr object offset ->field_object arguments=Vptr held held_offset ->
  object<>field_local_data locals ->object<>field_local_size locals ->
  field_member_layout ge _kind 0 ->field_member_layout ge _size 8 ->
  field_member_layout ge _data 16 ->field_member_layout ge _root 24 ->
  Mem.load Mint64 before(field_local_size locals)0=Some(Vlong(Int64.repr size)) ->
  Mem.load Mptr before(field_local_data locals)0=Some(Vptr buffer buffer_offset) ->
  field_locals_owned before locals ->field_borrowed_storage before object offset capacity ->
  exists stored freed count,
    field_store_sequence before object offset(field_kind arguments)(Int64.repr size)
      (Vptr buffer buffer_offset)(field_object arguments)stored /\
    field_local_release locals stored freed /\
    store_path ge(fun _=>True)
      (Returnstate ref_result(field_incref_cont locals arguments size continuation)before)count
      (Returnstate(Vint Int.zero)(call_cont continuation)freed) /\
    field_wire_cells freed object offset(field_kind arguments)(Int64.repr size)
      (Vptr buffer buffer_offset)(field_object arguments).
Proof.
  intros TARGET OWNER NOT_DATA NOT_SIZE KIND_LAYOUT SIZE_LAYOUT DATA_LAYOUT ROOT_LAYOUT
    SIZE_LOAD DATA_LOAD LOCALS STORAGE.
  destruct(actual_field_storage_produces_stores before object offset capacity(field_kind arguments)
    (Int64.repr size)(Vptr buffer buffer_offset)(field_object arguments)STORAGE)
    as[stored[STORES[SCALARS PERMISSIONS]]].
  destruct LOCALS as[DISTINCT[DATA_OWN SIZE_OWN]].
  assert(STORED_LOCALS:field_locals_owned stored locals).
  { split;[exact DISTINCT|]. split;intros position RANGE;apply PERMISSIONS;
      [apply DATA_OWN|apply SIZE_OWN];exact RANGE. }
  destruct(actual_field_locals_release_exists ge stored locals STORED_LOCALS)
    as[freed[RELEASE FREE]].
  destruct(actual_field_publication_tail ge locals arguments size before stored object offset buffer buffer_offset
    held held_offset continuation ref_result TARGET OWNER NOT_DATA NOT_SIZE KIND_LAYOUT SIZE_LAYOUT
    DATA_LAYOUT ROOT_LAYOUT SIZE_LOAD DATA_LOAD STORES)as[count PATH].
  exists stored,freed,(count+1)%nat;split;[exact STORES|]. split;[exact RELEASE|]. split.
  - eapply store_path_trans;[exact PATH|].
    eapply store_next;[exact I|eapply certified_local_return_edge;
      [apply old_expression_value;constructor|reflexivity|exact FREE]|].
    constructor;exact I.
  - eapply actual_field_locals_free_keep_publication;try eassumption.
    eapply actual_field_store_contents.
    + destruct STORAGE as[BOUND[LIMIT REST]];lia.
    + eauto.
    + eauto.
    + exact STORES.
Qed.
