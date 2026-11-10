(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Outcome allocation and dispatch use the actual immutable type specification. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayRegistry GatewayCancellationInputs GatewayGlobals GatewayTypeRuntime GatewayErrorRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_outcome_type_name:=map Byte.repr
  [108;101;97;110;99;97;103;101;46;95;104;111;115;116;46;79;117;116;99;111;109;101].

Theorem actual_outcome_immutable_flag :
  gvar_init v_host_outcome_spec=[Init_addrof ___stringlit_120 Ptrofs.zero;Init_int32(Int.repr 24);Init_int32 Int.zero;
    Init_int32(Int.repr 16640);Init_space 4;Init_addrof _host_outcome_slots Ptrofs.zero] /\
  Int.and(Int.repr 16640)(Int.repr 256)=Int.repr 256.
Proof. split;reflexivity. Qed.

Theorem actual_outcome_name_literal:gateway_static_cstring ___stringlit_120 v___stringlit_120 gateway_outcome_type_name.
Proof.
  eapply gateway_static_string_from_registration.
  - vm_compute;reflexivity.
  - reflexivity.
  - reflexivity.
  - vm_compute;intuition discriminate.
  - change(23<=18446744073709551616);lia.
Qed.

Theorem actual_outcome_specification_globals :
  gateway_variable_binding(Clight.globalenv prog)_host_outcome_spec v_host_outcome_spec /\
  gateway_variable_binding(Clight.globalenv prog)_host_outcome_slots v_host_outcome_slots.
Proof.
  split;apply gateway_actual_variable_binding;vm_compute;reflexivity.
Qed.

Theorem actual_outcome_observation_property :
  match skipn 70(gvar_init v_host_outcome_properties)with
  |Init_addrof name offset::Init_addrof getter getter_offset::Init_int64 setter::Init_int64 documentation::Init_int64 closure::_=>
    name=_host_observation_name /\offset=Ptrofs.zero /\getter=_host_outcome_observation /\getter_offset=Ptrofs.zero /\
    setter=Int64.zero /\documentation=Int64.zero /\closure=Int64.zero /\
    registered_string v_host_observation_name[111;98;115;101;114;118;97;116;105;111;110]
  |_=>False end.
Proof. repeat split;reflexivity. Qed.

Definition gateway_outcome_description new initialize destroy traverse clear methods properties :gateway_type_description:={|
  gateway_type_basicsize:=24;gateway_type_itemsize:=0;gateway_type_flags:=Int.repr 16640;
  gateway_type_slots:=[(Int.repr 65,Vptr new Ptrofs.zero);(Int.repr 60,Vptr initialize Ptrofs.zero);
    (Int.repr 52,Vptr destroy Ptrofs.zero);(Int.repr 71,Vptr traverse Ptrofs.zero);(Int.repr 51,Vptr clear Ptrofs.zero);
    (Int.repr 64,Vptr methods Ptrofs.zero);(Int.repr 73,Vptr properties Ptrofs.zero)]|}.

Lemma gateway_outcome_allocator_is_default new initialize destroy traverse clear methods properties :
  gateway_type_default_slots(gateway_outcome_description new initialize destroy traverse clear methods properties).
Proof.
  intros code function MEMBER;cbn in MEMBER.
  repeat destruct MEMBER as[MEMBER|MEMBER];try contradiction;inversion MEMBER;discriminate.
Qed.

Local Opaque prog.
Theorem gateway_outcome_type_regions memory specification slots name_symbol :
  Genv.find_symbol(Clight.globalenv prog)_host_outcome_slots=Some slots ->
  Genv.find_symbol(Clight.globalenv prog)___stringlit_120=Some name_symbol ->
  Genv.load_store_init_data(Clight.genv_genv(Clight.globalenv prog))memory specification 0(gvar_init v_host_outcome_spec) ->
  Genv.load_store_init_data(Clight.genv_genv(Clight.globalenv prog))memory slots 0(gvar_init v_host_outcome_slots) ->
  gateway_error_cstring memory(Vptr name_symbol Ptrofs.zero)gateway_outcome_type_name ->
  exists new initialize destroy traverse clear methods properties,
    Genv.find_symbol(Clight.globalenv prog)_PyType_GenericNew=Some new /\
    Genv.find_symbol(Clight.globalenv prog)_host_outcome_init=Some initialize /\
    Genv.find_symbol(Clight.globalenv prog)_host_outcome_free=Some destroy /\
    Genv.find_symbol(Clight.globalenv prog)_host_outcome_traverse=Some traverse /\
    Genv.find_symbol(Clight.globalenv prog)_host_outcome_clear=Some clear /\
    Genv.find_symbol(Clight.globalenv prog)_host_outcome_methods=Some methods /\
    Genv.find_symbol(Clight.globalenv prog)_host_outcome_properties=Some properties /\
    gateway_type_spec_memory memory(Vptr specification Ptrofs.zero)
      (gateway_outcome_description new initialize destroy traverse clear methods properties).
Proof.
  intros SLOTS NAME_SYMBOL SPECIFICATION_DATA SLOT_DATA NAME_BYTES.
  change((exists name,Genv.find_symbol(Clight.globalenv prog)___stringlit_120=Some name /\
    Mem.load Mptr memory specification 0=Some(Vptr name Ptrofs.zero)) /\
    Mem.load Mint32 memory specification 8=Some(Vint(Int.repr 24)) /\
    Mem.load Mint32 memory specification 12=Some(Vint Int.zero) /\
    Mem.load Mint32 memory specification 16=Some(Vint(Int.repr 16640)) /\
    Genv.read_as_zero memory specification 20 4 /\
    (exists table,Genv.find_symbol(Clight.globalenv prog)_host_outcome_slots=Some table /\
      Mem.load Mptr memory specification 24=Some(Vptr table Ptrofs.zero)) /\True)in SPECIFICATION_DATA.
  destruct SPECIFICATION_DATA as[[name[NAME NAME_LOAD]][SIZE[ITEMSIZE[FLAGS[PADDING[[table[TABLE TABLE_LOAD]]END]]]]]].
  assert(SAME_TABLE:table=slots)by congruence;subst table.
  cbn[Genv.load_store_init_data gvar_init size_chunk]in SLOT_DATA.
  destruct SLOT_DATA as[NEW_CODE[PAD0[[new[NEW NEW_LOAD]]SLOT_DATA]]].
  destruct SLOT_DATA as[INIT_CODE[PAD1[[memoryize[INITIALIZE INIT_LOAD]]SLOT_DATA]]].
  destruct SLOT_DATA as[FREE_CODE[PAD2[[destroy[DESTROY FREE_LOAD]]SLOT_DATA]]].
  destruct SLOT_DATA as[TRAVERSE_CODE[PAD3[[traverse[TRAVERSE TRAVERSE_LOAD]]SLOT_DATA]]].
  destruct SLOT_DATA as[CLEAR_CODE[PAD4[[clear[CLEAR CLEAR_LOAD]]SLOT_DATA]]].
  destruct SLOT_DATA as[METHODS_CODE[PAD5[[methods[METHODS METHODS_LOAD]]SLOT_DATA]]].
  destruct SLOT_DATA as[PROPERTIES_CODE[PAD6[[properties[PROPERTIES PROPERTIES_LOAD]]SLOT_DATA]]].
  destruct SLOT_DATA as[ZERO_CODE END_SLOTS].
  assert(SAME_NAME:name_symbol=name)by congruence;subst name_symbol.
  exists new,memoryize,destroy,traverse,clear,methods,properties.
  split;[exact NEW|]. split;[exact INITIALIZE|]. split;[exact DESTROY|].
  split;[exact TRAVERSE|]. split;[exact CLEAR|]. split;[exact METHODS|]. split;[exact PROPERTIES|].
  exists specification,Ptrofs.zero,(Vptr name Ptrofs.zero),gateway_outcome_type_name,slots,Ptrofs.zero.
  split;[reflexivity|]. split;[change(32<=18446744073709551616);lia|]. split;[exact NAME_LOAD|].
  split;[exact NAME_BYTES|]. split;[discriminate|]. split;[exact SIZE|]. split;[exact ITEMSIZE|]. split;[exact FLAGS|].
  split;[exact TABLE_LOAD|]. split;[change(116<=18446744073709551616);lia|].
  unfold gateway_outcome_description;cbn[gateway_type_slots gateway_slot_memory].
  repeat split;assumption.
Qed.

Theorem actual_outcome_type_initial initial:Genv.init_mem prog=Some initial ->
  exists specification new initialize destroy traverse clear methods properties,
    Genv.find_symbol(Clight.globalenv prog)_host_outcome_spec=Some specification /\
    Genv.find_symbol(Clight.globalenv prog)_PyType_GenericNew=Some new /\
    Genv.find_symbol(Clight.globalenv prog)_host_outcome_init=Some initialize /\
    Genv.find_symbol(Clight.globalenv prog)_host_outcome_free=Some destroy /\
    Genv.find_symbol(Clight.globalenv prog)_host_outcome_traverse=Some traverse /\
    Genv.find_symbol(Clight.globalenv prog)_host_outcome_clear=Some clear /\
    Genv.find_symbol(Clight.globalenv prog)_host_outcome_methods=Some methods /\
    Genv.find_symbol(Clight.globalenv prog)_host_outcome_properties=Some properties /\
    gateway_type_spec_memory initial(Vptr specification Ptrofs.zero)
      (gateway_outcome_description new initialize destroy traverse clear methods properties).
Proof.
  intro INITIAL.
  destruct(proj1 actual_outcome_specification_globals)
    as(specification &SPECIFICATION &SPECIFICATION_VARIABLE).
  destruct(proj2 actual_outcome_specification_globals)
    as(slots &SLOTS &SLOTS_VARIABLE).
  destruct(Genv.init_mem_characterization(gv:=v_host_outcome_spec)(m:=initial)prog specification SPECIFICATION_VARIABLE INITIAL)
    as[_[_[SPECIFICATION_DATA _]]].
  destruct(Genv.init_mem_characterization(gv:=v_host_outcome_slots)(m:=initial)prog slots SLOTS_VARIABLE INITIAL)
    as[_[_[SLOT_DATA _]]].
  destruct(gateway_static_cstring_loaded ___stringlit_120 v___stringlit_120 gateway_outcome_type_name initial
    actual_outcome_name_literal INITIAL)as(name_symbol &NAME_SYMBOL &NAME_BYTES).
  destruct(gateway_outcome_type_regions initial specification slots name_symbol SLOTS NAME_SYMBOL
    (SPECIFICATION_DATA eq_refl)(SLOT_DATA eq_refl)NAME_BYTES)
    as(new &initialize &destroy &traverse &clear &methods &properties &RESULT).
  exists specification,new,initialize,destroy,traverse,clear,methods,properties;split;[exact SPECIFICATION|exact RESULT].
Qed.
