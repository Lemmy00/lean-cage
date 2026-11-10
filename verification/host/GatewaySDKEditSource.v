(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual guarded SDK edits use the selected headers and endpoint
   cells. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewaySpawnABI GatewaySpawnActions GatewaySDKCall
  GatewayExchangeSetup GatewayExchangeLoads GatewayPairContext GatewayMemoryPrefixes GatewayFramedRuntime GatewayPrefix.
Import ListNotations.
Open Scope Z_scope.

Inductive gateway_sdk_edit:=gateway_edit_group|gateway_edit_flags|gateway_edit_input|gateway_edit_output|
  gateway_edit_cancellation|gateway_edit_closefrom.
Definition sdk_edit_index edit:nat:=match edit with gateway_edit_group=>10|gateway_edit_flags=>11|
  gateway_edit_input=>12|gateway_edit_output=>13|gateway_edit_cancellation=>14|gateway_edit_closefrom=>15 end.
Definition sdk_edit_start edit:=exchange_setup_after(sdk_edit_index edit).
Definition sdk_edit_after edit:=exchange_setup_after(S(sdk_edit_index edit)).
Definition sdk_edit_statement edit:=exchange_setup_at(sdk_edit_index edit).
Definition sdk_edit_body edit:=match edit with gateway_edit_group=>sdk_edit_statement edit|
  _=>match sdk_edit_statement edit with Sifthenelse _ yes _=>yes|_=>Sskip end end.
Definition sdk_edit_prefix edit:=match sdk_edit_body edit with Ssequence prefix _=>prefix|_=>Sskip end.
Definition sdk_edit_bind edit:=match sdk_edit_body edit with Ssequence _ bind=>bind|_=>Sskip end.
Definition sdk_edit_call edit:=match sdk_edit_prefix edit with Ssequence _ call=>call|plain=>plain end.
Definition sdk_edit_load edit:=match sdk_edit_prefix edit with Ssequence load _=>load|_=>Sskip end.
Definition sdk_edit_destination edit:=match edit with gateway_edit_group=>_t'20|gateway_edit_flags=>_t'21|
  gateway_edit_input=>_t'22|gateway_edit_output=>_t'23|gateway_edit_cancellation=>_t'24|gateway_edit_closefrom=>_t'25 end.
Definition sdk_edit_loaded_temps edit data_right control_right temporaries:=match edit with
  gateway_edit_input=>PTree.set _t'82(Vint(Int.repr data_right))temporaries|
  gateway_edit_output=>PTree.set _t'81(Vint(Int.repr data_right))temporaries|
  gateway_edit_cancellation=>PTree.set _t'80(Vint(Int.repr control_right))temporaries|_=>temporaries end.
Definition sdk_edit_return_temps edit status data_right control_right temporaries:=PTree.set _setup(Vint status)
  (PTree.set(sdk_edit_destination edit)(Vint status)(sdk_edit_loaded_temps edit data_right control_right temporaries)).
Definition sdk_edit_api edit:=match edit with gateway_edit_group=>gateway_attributes_group_api|
  gateway_edit_flags=>gateway_attributes_flags_api|gateway_edit_closefrom=>gateway_actions_closefrom_api|
  _=>gateway_actions_dup_api end.
Definition sdk_edit_arguments edit actions attributes data_right control_right:=match edit with
  gateway_edit_group=>[Vptr attributes Ptrofs.zero;Vint Int.zero]|
  gateway_edit_flags=>[Vptr attributes Ptrofs.zero;Vint(Int.repr 2)]|
  gateway_edit_input=>[Vptr actions Ptrofs.zero;Vint(Int.repr data_right);Vint Int.zero]|
  gateway_edit_output=>[Vptr actions Ptrofs.zero;Vint(Int.repr data_right);Vint(Int.repr 1)]|
  gateway_edit_cancellation=>[Vptr actions Ptrofs.zero;Vint(Int.repr control_right);Vint(Int.repr 3)]|
  gateway_edit_closefrom=>[Vptr actions Ptrofs.zero;Vint(Int.repr 4)]end.
Definition sdk_edit_cont edit environment temporaries:=Kcall(Some(sdk_edit_destination edit))f_host_exchange environment temporaries
  (Kseq(sdk_edit_bind edit)(Kseq(sdk_edit_after edit)Kstop)).

Lemma actual_sdk_edit_source_call(ge:Clight.genv)edit environment temporaries memory actions attributes
    data_right control_right symbol:
  environment!_actions=Some(actions,gateway_actions_type)->
  environment!_attributes=Some(attributes,gateway_attributes_type)->
  environment!(gateway_spawn_identifier(sdk_edit_api edit))=None->
  Genv.find_symbol ge(gateway_spawn_identifier(sdk_edit_api edit))=Some symbol->
  Genv.find_funct_ptr ge symbol=Some(gateway_spawn_signature(sdk_edit_api edit))->
  store_edge ge(State f_host_exchange(sdk_edit_call edit)
    (Kseq(sdk_edit_bind edit)(Kseq(sdk_edit_after edit)Kstop))environment
    (sdk_edit_loaded_temps edit data_right control_right temporaries)memory)
    (Callstate(gateway_spawn_signature(sdk_edit_api edit))
      (sdk_edit_arguments edit actions attributes data_right control_right)
      (sdk_edit_cont edit environment(sdk_edit_loaded_temps edit data_right control_right temporaries))memory).
Proof.
  intros ACTIONS ATTRIBUTES UNSHADOWED SYMBOL FUNCTION;destruct edit.
  all:first[eapply gateway_sdk_source_call with(api:=gateway_attributes_group_api)|
    eapply gateway_sdk_source_call with(api:=gateway_attributes_flags_api)|
    eapply gateway_sdk_source_call with(api:=gateway_actions_dup_api)|
    eapply gateway_sdk_source_call with(api:=gateway_actions_closefrom_api)];
    [exact UNSHADOWED|exact SYMBOL|exact FUNCTION|].
  all:eapply cons_argument_values with(v:=Vptr _ Ptrofs.zero);
    [apply local_address_expression;first[exact ACTIONS|exact ATTRIBUTES]|reflexivity|].
  all:repeat first[apply no_argument_values|
    eapply cons_argument_values with(v:=Vint _);
      [apply old_expression_value;first[constructor|apply value_temp;apply PTree.gss]|reflexivity|]].
  all:apply PTree.gss.
Qed.

Theorem actual_sdk_edit_prefix {World Event}(backend:gateway_backend World Event)
    property(CLOSED:gateway_ambient_closed backend property)edit allocation_before allocated environment temporaries memory
    actions attributes data control data_left data_right control_left control_right:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  environment!_actions=Some(actions,gateway_actions_type)->
  environment!_attributes=Some(attributes,gateway_attributes_type)->
  environment!_pair=Some(data,tarray tint 2)->environment!_control=Some(control,tarray tint 2)->
  temporaries!_setup=Some(Vint Int.zero)->
  (forall before world,property before world->gateway_pair_cells before data Ptrofs.zero data_left data_right /\
    gateway_pair_cells before control Ptrofs.zero control_left control_right)->
  gateway_memory_prefix backend(Clight.globalenv prog)
    (Callstate(gateway_spawn_signature(sdk_edit_api edit))
      (sdk_edit_arguments edit actions attributes data_right control_right)
      (sdk_edit_cont edit environment(sdk_edit_loaded_temps edit data_right control_right temporaries))memory)
    property property(State f_host_exchange(sdk_edit_start edit)Kstop environment temporaries memory).
Proof.
  intros ALLOC ACTIONS ATTRIBUTES DATA CONTROL SETUP CELLS.
  eapply gateway_memory_same with(following:=State f_host_exchange(sdk_edit_statement edit)
    (Kseq(sdk_edit_after edit)Kstop)environment temporaries memory);
    [exact CLOSED|cbn;destruct edit;tauto|intros;destruct edit;apply unchanged_store_edge,edge_seq|].
  assert(BODY:gateway_memory_prefix backend(Clight.globalenv prog)
    (Callstate(gateway_spawn_signature(sdk_edit_api edit))
      (sdk_edit_arguments edit actions attributes data_right control_right)
      (sdk_edit_cont edit environment(sdk_edit_loaded_temps edit data_right control_right temporaries))memory)
    property property(State f_host_exchange(sdk_edit_body edit)(Kseq(sdk_edit_after edit)Kstop)environment temporaries memory)).
  { eapply gateway_memory_same with(following:=State f_host_exchange(sdk_edit_prefix edit)
      (Kseq(sdk_edit_bind edit)(Kseq(sdk_edit_after edit)Kstop))environment temporaries memory);
      [exact CLOSED|cbn;destruct edit;tauto|intros;destruct edit;apply unchanged_store_edge,edge_seq|].
    assert(CALL:gateway_memory_prefix backend(Clight.globalenv prog)
      (Callstate(gateway_spawn_signature(sdk_edit_api edit))
        (sdk_edit_arguments edit actions attributes data_right control_right)
        (sdk_edit_cont edit environment(sdk_edit_loaded_temps edit data_right control_right temporaries))memory)
      property property(State f_host_exchange(sdk_edit_call edit)
        (Kseq(sdk_edit_bind edit)(Kseq(sdk_edit_after edit)Kstop))environment
        (sdk_edit_loaded_temps edit data_right control_right temporaries)memory)).
    { eapply gateway_memory_same;
        [exact CLOSED|cbn;destruct edit;tauto| |apply gateway_memory_identity].
      intros before world READY;destruct(actual_gateway_spawn_binding(sdk_edit_api edit))as[symbol[SYMBOL FUNCTION]].
      eapply actual_sdk_edit_source_call;[exact ACTIONS|exact ATTRIBUTES| |exact SYMBOL|exact FUNCTION].
      eapply actual_exchange_setup_unshadowed;[exact ALLOC|destruct edit;cbn;intuition discriminate]. }
    destruct edit;try exact CALL.
    all:let edit:=lazymatch type of CALL with
      gateway_memory_prefix _ _ _ _ _ (State _ (sdk_edit_call ?current) _ _ _ _)=>current end in
      eapply gateway_memory_same with(following:=State f_host_exchange(sdk_edit_load edit)
        (Kseq(sdk_edit_call edit)(Kseq(sdk_edit_bind edit)(Kseq(sdk_edit_after edit)Kstop)))
        environment temporaries memory);
        [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
    all:let edit:=lazymatch type of CALL with
      gateway_memory_prefix _ _ _ _ _ (State _ (sdk_edit_call ?current) _ _ _ _)=>current end in
      eapply gateway_memory_same with(following:=State f_host_exchange Sskip
        (Kseq(sdk_edit_call edit)(Kseq(sdk_edit_bind edit)(Kseq(sdk_edit_after edit)Kstop)))environment
          (sdk_edit_loaded_temps edit data_right control_right temporaries)memory);
        [exact CLOSED|cbn;tauto| |].
    all:try solve[intros before world READY;apply certified_set_edge;
      eapply actual_exchange_endpoint_load with(left:=data_left)(right:=data_right);
        [exact DATA|exact(proj1(CELLS before world READY))|lia]].
    all:try solve[intros before world READY;apply certified_set_edge;
      eapply actual_exchange_endpoint_load with(left:=control_left)(right:=control_right);
        [exact CONTROL|exact(proj2(CELLS before world READY))|lia]].
    all:let code:=lazymatch type of CALL with gateway_memory_prefix _ _ _ _ _ ?source=>source end in
      eapply gateway_memory_same with(following:=code);
        [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|exact CALL]. }
  destruct edit;try exact BODY.
  all:let code:=lazymatch type of BODY with gateway_memory_prefix _ _ _ _ _ ?source=>source end in
    eapply gateway_memory_same with(following:=code);[exact CLOSED|cbn;tauto| |exact BODY].
  all:intros before world READY;apply certified_if_edge with(v:=Vint Int.one)(b:=true);
    [apply old_expression_value;eapply value_unary with(v:=Vint Int.zero);[apply value_temp;exact SETUP|reflexivity]|
      reflexivity].
Qed.
