(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.main-inputs: Actual field-pointer addresses and initialization stores. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Errors Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll ScalarMemory.
From LeanCageMainNumber Require Import NumberInitial.
From LeanCageMain Require Import Main MainStructure MainMemory MainValues MainControl.
Import ListNotations.
Open Scope Z_scope.
Lemma field_lookup_sound (entry : option composite) ge id ofs :
 (match entry with Some co=>field_offset ge id(co_members co)=OK(ofs,Full)|None=>False end) ->
 exists co,entry=Some co /\ field_offset ge id(co_members co)=OK(ofs,Full).
Proof. destruct entry as[co|];intros GOOD;[exists co;auto|contradiction]. Qed.
Lemma policy_field_layout i id : In(i,id)policy_fields ->
 exists co,(genv_cenv main_ge)!_policy=Some co /\ field_offset main_ge id(co_members co)=OK(8*i,Full).
Proof.
 intros IN;apply field_lookup_sound.
 cbn[policy_fields]in IN;repeat destruct IN as[EQ|IN];try contradiction;
 inversion EQ;subst;vm_compute;reflexivity.
Qed.
Lemma policy_field_index i id : In(i,id)policy_fields -> 0<=i<10.
Proof. intros IN;cbn[policy_fields]in IN;repeat destruct IN as[EQ|IN];try contradiction;inversion EQ;lia. Qed.
Lemma main_policy_field e le m i id : e!_policy__1=None -> In(i,id)policy_fields ->
 location_value main_ge e le m(Efield(Evar _policy__1 policy_type)id tulong)
 main_policy_block(Ptrofs.repr(8*i)).
Proof.
 intros GLOBAL IN;destruct(policy_field_layout i id IN)as[co[CO FIELD]].
 replace(Ptrofs.repr(8*i))with(Ptrofs.add Ptrofs.zero(Ptrofs.repr(8*i)))by(rewrite Ptrofs.add_zero_l;reflexivity).
 eapply struct_location_value.
 - eapply location_read_value;[apply global_location_value;[exact GLOBAL|apply main_policy_binding]|].
   apply deref_loc_copy;reflexivity.
 - reflexivity.
 - exact CO.
 - exact FIELD.
Qed.
Lemma main_pointer_add_signed ge m b ty i : 0<=i<10 ->
 sem_binary_operation ge Oadd(Vptr b Ptrofs.zero)(tarray(tptr ty)10)(Vint(Int.repr i))tint m=
 Some(Vptr b(Ptrofs.repr(8*i))).
Proof.
 intros INDEX;change (Some(Vptr b(Ptrofs.add Ptrofs.zero(Ptrofs.mul(Ptrofs.repr 8)
  (Ptrofs.of_ints(Int.repr i)))))=Some(Vptr b(Ptrofs.repr(8*i)))).
 unfold Ptrofs.of_ints;rewrite Int.signed_repr by(change Int.min_signed with (-2147483648);change Int.max_signed with 2147483647;lia).
 rewrite Ptrofs.add_zero_l,Ptrofs.mul_signed,!Ptrofs.signed_repr by
  (change Ptrofs.min_signed with(-9223372036854775808);change Ptrofs.max_signed with 9223372036854775807;lia).
 reflexivity.
Qed.
Definition field_cell (pair : Z*ident) := {|scalar_chunk:=Mptr;scalar_offset:=8*fst pair;
 scalar_value:=Vptr main_policy_block(Ptrofs.repr(8*fst pair))|}.
Lemma field_initializer_edge e le m fields pair k after :
 e!_fields=Some(fields,tarray(tptr tulong)10) -> e!_policy__1=None -> In pair policy_fields ->
 Mem.store Mptr m fields(8*fst pair)(scalar_value(field_cell pair))=Some after ->
 store_edge main_ge(State f_main(field_initializer pair)k e le m)(State f_main Sskip k e le after).
Proof.
 destruct pair as[i id];intros LOCAL GLOBAL IN STORE;pose proof(policy_field_index i id IN)as INDEX.
 unfold field_initializer;cbn[fst snd];eapply assignment_source_edge.
 - apply pointer_location_value;eapply binary_expression_value.
   + apply main_array_value;exact LOCAL.
   + apply old_expression_value;apply value_int.
   + apply main_pointer_add_signed;exact INDEX.
 - apply main_address_value;apply main_policy_field with(i:=i)(id:=id);[exact GLOBAL|exact IN].
 - reflexivity.
 - eapply assign_loc_value;[reflexivity|].
   unfold Mem.storev;rewrite Ptrofs.unsigned_repr by(change Ptrofs.max_unsigned with 18446744073709551615;lia).
   destruct(zle _ _)as[LIMIT|OVER];[exact STORE|exfalso;change(8*i+8>18446744073709551616)in OVER;lia].
Qed.
Definition field_prefix fields before pairs after := exists done rest,
 pairs=done++rest /\ scalar_stores fields before(map field_cell done)after.
Lemma field_prefix_initial fields m pairs : field_prefix fields m pairs m.
Proof. exists [],pairs;split;[reflexivity|constructor]. Qed.
Lemma field_prefix_cons fields before pair pairs mid after :
 Mem.store Mptr before fields(8*fst pair)(scalar_value(field_cell pair))=Some mid ->
 field_prefix fields mid pairs after -> field_prefix fields before(pair::pairs)after.
Proof. intros STORE[done[rest[EQ STORES]]];exists(pair::done),rest;split;[cbn;congruence|]. econstructor;eassumption. Qed.
Theorem field_initializers_source fields pairs before after e le k tail :
 Forall(fun pair=>In pair policy_fields)pairs ->
 e!_fields=Some(fields,tarray(tptr tulong)10) -> e!_policy__1=None ->
 scalar_stores fields before(map field_cell pairs)after ->
 store_path main_ge(field_prefix fields before pairs)
 (State f_main(field_sequence pairs tail)k e le before)(3*length pairs)(State f_main tail k e le after).
Proof.
 revert before;induction pairs as[|pair pairs IH];intros before VALID LOCAL GLOBAL STORES.
 - inversion STORES;subst;apply store_done;apply field_prefix_initial.
 - inversion VALID as[|? ? IN REST];subst;inversion STORES as[|? ? ? mid ? STORE TAIL];subst.
   assert(GOOD : field_prefix fields before(pair::pairs)before)by apply field_prefix_initial.
   assert(MID : field_prefix fields before(pair::pairs)mid).
   { apply field_prefix_cons with(mid:=mid);[exact STORE|apply field_prefix_initial]. }
   cbn[field_sequence fold_right length];replace(3*S(length pairs))%nat with(S(S(S(3*length pairs))))%nat by lia.
   main_route;main_next;[apply field_initializer_edge with(fields:=fields)(pair:=pair);[exact LOCAL|exact GLOBAL|exact IN|exact STORE]|].
   main_route;eapply number_path_implication;[|apply IH;assumption].
   intros current MEMORY;eapply field_prefix_cons;eassumption.
Qed.
Theorem field_cells_valid : Forall(scalar_valid 80)(map field_cell policy_fields).
Proof. apply scalar_list_validb_sound;reflexivity. Qed.
Theorem field_cells_ordered : scalar_orderedb(map field_cell policy_fields)=true.
Proof. reflexivity. Qed.
Theorem field_initialization_exists fields m : Mem.range_perm m fields 0 80 Cur Freeable ->
 exists after,scalar_stores fields m(map field_cell policy_fields)after.
Proof. intros RANGE;apply scalar_stores_exist with(size:=80);[apply field_cells_valid|exact RANGE]. Qed.
Theorem initialized_fields_mapping fields before after :
 scalar_stores fields before(map field_cell policy_fields)after -> fields_mapping after fields main_policy_block.
Proof.
 intros STORES i INDEX.
 assert(IND : In i(map fst policy_fields)).
 { change(0=i \/ 1=i \/ 2=i \/ 3=i \/ 4=i \/ 5=i \/ 6=i \/ 7=i \/ 8=i \/ 9=i \/ False);lia. }
 apply in_map_iff in IND;destruct IND as[[j id][SAME IN]];cbn in SAME;subst j.
 pose proof(scalar_stores_fields _ _ _ _ STORES(scalar_orderedb_sound _ field_cells_ordered)
  (field_cell(i,id))(in_map field_cell _ _ IN))as LOAD.
 unfold Mem.loadv;rewrite Ptrofs.unsigned_repr by(change Ptrofs.max_unsigned with 18446744073709551615;lia).
 destruct(zle _ _)as[LIMIT|OVER];[exact LOAD|exfalso;change(8*i+8>18446744073709551616)in OVER;lia].
Qed.
