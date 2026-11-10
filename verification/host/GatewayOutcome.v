(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual Outcome ABI and property table bind all fourteen fields. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Errors
  Ctypes Ctypesdefs Cop Clight.
Require Import LocalAccess CallAccess StoreSteps ClightSteps.
From HostGateway Require Import GatewaySource GatewayRegistry GatewayObjects GatewayMachine.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_outcome_names :list(list Z):=
  [[114;101;113;117;101;115;116;95;105;100];
   [98;117;110;100;108;101;95;105;100];
   [99;111;109;109;97;110;100];
   [115;116;97;116;117;115];
   [114;101;112;111;114;116];
   [101;120;105;116;95;99;111;100;101];
   [118;109;95;99;108;101;97;110;117;112];
   [101;114;114;111;114];
   [115;116;100;111;117;116];
   [115;116;100;101;114;114];
   [102;105;108;101;115];
   [111;117;116;112;117;116];
   [112;117;98;108;105;99;97;116;105;111;110];
   [112;117;98;108;105;99;97;116;105;111;110;95;101;114;114;111;114]].
Definition gateway_outcome_name_symbols :list ident:=
  [___stringlit_50;___stringlit_29;___stringlit_49;___stringlit_48;___stringlit_47;___stringlit_46;
   ___stringlit_45;___stringlit_44;___stringlit_43;___stringlit_42;___stringlit_41;___stringlit_40;
   ___stringlit_39;___stringlit_38].

Theorem actual_outcome_fields_are_source_data :
  gvar_init v_host_outcome_fields=map(fun name=>Init_addrof name Ptrofs.zero)gateway_outcome_name_symbols.
Proof. reflexivity. Qed.

Definition gateway_outcome_property index name :Prop:=
  match skipn(5*index)(gvar_init v_host_outcome_properties)with
  |Init_addrof symbol offset::Init_addrof getter get_offset::Init_addrof setter set_offset::
      Init_int64 documentation::Init_int64 closure::_=>
    offset=Ptrofs.zero /\getter=_host_outcome_get /\get_offset=Ptrofs.zero /\
    setter=_host_outcome_set /\set_offset=Ptrofs.zero /\documentation=Int64.zero /\
    closure=Int64.repr(Z.of_nat index) /\
    nth_error(gvar_init v_host_outcome_fields)index=Some(Init_addrof symbol Ptrofs.zero) /\
    match gateway_program_definition symbol global_definitions with
    |Some(Gvar variable)=>registered_string variable name
    |_=>False end
  |_=>False end.

Theorem actual_outcome_all_fourteen_properties :
  Forall2 gateway_outcome_property(seq 0 14)gateway_outcome_names.
Proof. repeat constructor;reflexivity. Qed.

Theorem actual_outcome_property_selected index name :
  nth_error gateway_outcome_names index=Some name ->gateway_outcome_property index name.
Proof.
  intro SELECTED.
  do 14(destruct index as[|index];
    [cbn in SELECTED;inversion SELECTED;subst name;repeat split;reflexivity|]).
  destruct index;cbn in SELECTED;discriminate.
Qed.

Definition gateway_outcome_member_layout(ge:Clight.genv) :Prop:=
  exists composite,(genv_cenv ge)!__9090=Some composite /\
    field_offset(genv_cenv ge)_data(co_members composite)=OK(16,Full).
Definition gateway_actual_outcome_members :=
  [Member_plain _ob_base(Tstruct __object noattr);Member_plain _data(tptr(Tstruct __object noattr))].

Lemma actual_outcome_members_from_source :
  option_map co_members((prog_comp_env prog)!__9090)=Some gateway_actual_outcome_members.
Proof. vm_compute;reflexivity. Qed.

Lemma actual_python_object_size_from_source :
  option_map(fun composite=>(co_sizeof composite,co_alignof composite))
    ((prog_comp_env prog)!__object)=Some(16,8).
Proof. vm_compute;reflexivity. Qed.

Lemma gateway_outcome_layout_from_members environment :
  option_map co_members(environment!__9090)=Some gateway_actual_outcome_members ->
  option_map(fun composite=>(co_sizeof composite,co_alignof composite))(environment!__object)=Some(16,8) ->
  exists composite,environment!__9090=Some composite /\
    field_offset environment _data(co_members composite)=OK(16,Full).
Proof.
  intros MEMBERS HEADER.
  destruct(environment!__9090)as[composite|]eqn:LOOK;[|discriminate].
  destruct(environment!__object)as[header|]eqn:HEAD;[|discriminate].
  cbn in MEMBERS,HEADER;injection MEMBERS as MEMBERS;injection HEADER as SIZE ALIGNMENT.
  exists composite;split;[reflexivity|].
  rewrite MEMBERS;unfold gateway_actual_outcome_members,field_offset,field_offset_rec;cbn.
  unfold bitalignof,bitsizeof;cbn[sizeof alignof].
  rewrite HEAD;cbn;rewrite SIZE,ALIGNMENT;reflexivity.
Qed.

Theorem actual_outcome_member_layout :gateway_outcome_member_layout(Clight.globalenv prog).
Proof.
  apply gateway_outcome_layout_from_members.
  - exact actual_outcome_members_from_source.
  - exact actual_python_object_size_from_source.
Qed.

Definition gateway_outcome_member identifier :=
  Efield(Ederef(Etempvar identifier(tptr(Tstruct __9090 noattr)))(Tstruct __9090 noattr))
    _data(tptr(Tstruct __object noattr)).
Definition gateway_outcome_slot block offset :=Vptr block(Ptrofs.add offset(Ptrofs.repr 16)).

Lemma gateway_actual_outcome_member_location ge environment temporaries memory identifier block offset :
  temporaries!identifier=Some(Vptr block offset) ->gateway_outcome_member_layout ge ->
  location_value ge environment temporaries memory(gateway_outcome_member identifier)block
    (Ptrofs.add offset(Ptrofs.repr 16)).
Proof.
  intros POINTER[composite[LAYOUT MEMBER]].
  eapply struct_location_value with(id:=__9090)(co:=composite)(att:=noattr)(delta:=16).
  - eapply location_read_value with(b:=block)(ofs:=offset).
    + apply pointer_location_value,old_expression_value,value_temp;exact POINTER.
    + apply deref_loc_copy;reflexivity.
  - reflexivity.
  - exact LAYOUT.
  - exact MEMBER.
Qed.

Lemma gateway_actual_outcome_member_read ge environment temporaries memory identifier block offset data :
  temporaries!identifier=Some(Vptr block offset) ->gateway_outcome_member_layout ge ->
  Mem.loadv Mptr memory(gateway_outcome_slot block offset)=Some data ->
  expression_value ge environment temporaries memory(gateway_outcome_member identifier)data.
Proof.
  intros POINTER LAYOUT LOAD;eapply location_read_value.
  - eapply gateway_actual_outcome_member_location;eassumption.
  - eapply deref_loc_value;[reflexivity|exact LOAD].
Qed.

Lemma gateway_actual_outcome_data_assignment ge function environment temporaries before continuation
    object offset data data_block data_offset after :
  gateway_outcome_member_layout ge ->temporaries!_outcome=Some(Vptr object offset) ->
  temporaries!_copy=Some(Vptr data_block data_offset) ->data=Vptr data_block data_offset ->
  Mem.storev Mptr before(gateway_outcome_slot object offset)data=Some after ->
  store_edge ge
    (State function(Sassign(gateway_outcome_member _outcome)
      (Etempvar _copy(tptr(Tstruct __object noattr))))continuation environment temporaries before)
    (State function Sskip continuation environment temporaries after).
Proof.
  intros LAYOUT OBJECT COPY DATA STORE;subst data.
  eapply assignment_source_edge with(b:=object)(ofs:=Ptrofs.add offset(Ptrofs.repr 16))
    (v:=Vptr data_block data_offset)(w:=Vptr data_block data_offset).
  - eapply gateway_actual_outcome_member_location;eassumption.
  - apply old_expression_value,value_temp;exact COPY.
  - reflexivity.
  - eapply assign_loc_value;[reflexivity|exact STORE].
Qed.
