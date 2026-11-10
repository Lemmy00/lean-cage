(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: Reaper source stores target only its real pause allocation. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Errors Ctypes Ctypesdefs Cop Clight.
Require Import Machine LocalAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayReapStructure GatewayReapAllocation.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_reap_member_layout(ge:Clight.genv)field offset:Prop:=
  exists composite,(genv_cenv ge)!_timespec=Some composite /\field_offset ge field(co_members composite)=OK(offset,Full).

Definition actual_reap_timespec_members:members:=[Member_plain _tv_sec tlong;Member_plain _tv_nsec tlong].

Lemma actual_reap_members_from_source:
  option_map co_members((prog_comp_env prog)!_timespec)=Some actual_reap_timespec_members.
Proof. vm_compute;reflexivity. Qed.

Lemma actual_reap_seconds_layout:
  gateway_reap_member_layout(Clight.globalenv prog)_tv_sec 0.
Proof.
  pose proof actual_reap_members_from_source as MEMBERS.
  destruct((prog_comp_env prog)!_timespec)as[composite|]eqn:LOOK;[|discriminate].
  cbn in MEMBERS;injection MEMBERS as MEMBERS.
  exists composite;split;[exact LOOK|rewrite MEMBERS;reflexivity].
Qed.

Lemma actual_reap_nanoseconds_layout:
  gateway_reap_member_layout(Clight.globalenv prog)_tv_nsec 8.
Proof.
  pose proof actual_reap_members_from_source as MEMBERS.
  destruct((prog_comp_env prog)!_timespec)as[composite|]eqn:LOOK;[|discriminate].
  cbn in MEMBERS;injection MEMBERS as MEMBERS.
  exists composite;split;[exact LOOK|rewrite MEMBERS;reflexivity].
Qed.

Lemma actual_reap_pause_location ge slots temporaries memory location:
  gateway_reap_member_layout ge _tv_sec 0->gateway_reap_member_layout ge _tv_nsec 8->
  reap_pause_location location->exists offset,typeof location=tlong /\
    location_value ge(reap_environment slots)temporaries memory location(reap_pause_slot slots)offset.
Proof.
  intros SECONDS_LAYOUT NANOSECONDS_LAYOUT[SECONDS|NANOSECONDS];subst location.
  - destruct SECONDS_LAYOUT as[composite[LAYOUT FIELD]];exists(Ptrofs.add Ptrofs.zero(Ptrofs.repr 0));split;[reflexivity|].
    eapply struct_location_value with(id:=_timespec)(co:=composite)(att:=noattr)(delta:=0);
      [|reflexivity|exact LAYOUT|exact FIELD].
    eapply location_read_value;[apply local_location_value;apply PTree.gss|apply deref_loc_copy;reflexivity].
  - destruct NANOSECONDS_LAYOUT as[composite[LAYOUT FIELD]];exists(Ptrofs.add Ptrofs.zero(Ptrofs.repr 8));split;[reflexivity|].
    eapply struct_location_value with(id:=_timespec)(co:=composite)(att:=noattr)(delta:=8);
      [|reflexivity|exact LAYOUT|exact FIELD].
    eapply location_read_value;[apply local_location_value;apply PTree.gss|apply deref_loc_copy;reflexivity].
Qed.

Lemma gateway_reap_assignment_store ge slots temporaries before location object offset bitfield value after:
  gateway_reap_member_layout ge _tv_sec 0->gateway_reap_member_layout ge _tv_nsec 8->
  reap_pause_location location->
  eval_lvalue ge(reap_environment slots)temporaries before location object offset bitfield->
  assign_loc ge(typeof location)before object offset bitfield value after->
  exists chunk position,Mem.store chunk before(reap_pause_slot slots)position value=Some after.
Proof.
  intros SECONDS_LAYOUT NANOSECONDS_LAYOUT LOCATION LVALUE ASSIGN.
  destruct(actual_reap_pause_location ge slots temporaries before location SECONDS_LAYOUT NANOSECONDS_LAYOUT LOCATION)
    as[actual_offset[TYPE[REAL UNIQUE]]].
  destruct(UNIQUE _ _ _ LVALUE)as[OBJECT[OFFSET BITFIELD]];subst object offset bitfield.
  rewrite TYPE in ASSIGN;inversion ASSIGN;subst.
  all:try discriminate.
  match goal with ACCESS:access_mode tlong=By_value ?chunk|-_=>
    cbn in ACCESS;inversion ACCESS;subst chunk end.
  match goal with STORE:Mem.storev _ _ _ _=Some _|-_=>
    unfold Mem.storev in STORE;destruct(zle(Ptrofs.unsigned actual_offset+size_chunk Mint64)Ptrofs.modulus);
      [exists Mint64,(Ptrofs.unsigned actual_offset);exact STORE|discriminate]end.
Qed.

Theorem gateway_reap_internal_memory ge slots child source trace after:
  gateway_reap_member_layout ge _tv_sec 0->gateway_reap_member_layout ge _tv_nsec 8->
  gateway_reap_source slots child source->gateway_reap_source_instruction source->
  ~gateway_at_primitive source->step2 ge source trace after->
  memory_of after=memory_of source \/
  (exists chunk position value,Mem.store chunk(memory_of source)(reap_pause_slot slots)position value=Some(memory_of after)) \/
  (exists value,after=Returnstate value Kstop(memory_of after) /\
    Mem.free_list(memory_of source)(blocks_of_env ge(reap_environment slots))=Some(memory_of after)).
Proof.
  destruct source as[function body continuation environment temporaries memory|
    definition arguments continuation memory|returned continuation memory];intros SECONDS_LAYOUT NANOSECONDS_LAYOUT PROFILE SOURCE INTERNAL STEP.
  - destruct PROFILE as[FUNCTION[ENV[CHILD[BODY CONT]]]];subst function environment.
    inversion STEP;subst;cbn[gateway_reap_statement]in BODY;try contradiction.
    all:cbn[memory_of].
    all:try solve[left;reflexivity].
    + right;left;match goal with LVALUE:eval_lvalue _ _ _ _ _ _ _ _,ASSIGN:assign_loc _ _ _ _ _ _ _ _|-_=>
        destruct(gateway_reap_assignment_store ge slots temporaries memory _ _ _ _ _ _
          SECONDS_LAYOUT NANOSECONDS_LAYOUT BODY LVALUE ASSIGN)
          as[chunk[position STORE]];exists chunk,position,v;exact STORE end.
    + rewrite(gateway_reap_cont_call_cont continuation CONT);right;right;exists Vundef;split;[reflexivity|assumption].
    + assert(STOP:continuation=Kstop).
      { destruct continuation;try reflexivity;cbn[gateway_reap_cont]in CONT;try contradiction.
        all:match goal with CALL:is_call_cont _|-_=>cbn in CALL;contradiction end. }
      subst continuation;right;right;exists Vundef;split;[reflexivity|assumption].
  - contradiction.
  - inversion STEP;subst;left;reflexivity.
Qed.
