(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual SDK initializer arguments and guards precede the selected
   spawn. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewaySpawnABI GatewaySDKCall GatewayExchangeSetup GatewayExchangeErrors
  GatewayFramedRuntime GatewayMemoryPrefixes GatewayLaunchPaths GatewayPrefix.
Import ListNotations.

Inductive gateway_sdk_initializer:=gateway_initialize_actions|gateway_initialize_attributes.
Definition sdk_initializer_api initializer:=match initializer with
  gateway_initialize_actions=>gateway_actions_init_api|gateway_initialize_attributes=>gateway_attributes_init_api end.
Definition sdk_initializer_identifier initializer:=match initializer with
  gateway_initialize_actions=>_actions|gateway_initialize_attributes=>_attributes end.
Definition sdk_initializer_type initializer:=match initializer with
  gateway_initialize_actions=>gateway_actions_type|gateway_initialize_attributes=>gateway_attributes_type end.
Definition sdk_initializer_destination initializer:=match initializer with
  gateway_initialize_actions=>_t'14|gateway_initialize_attributes=>_t'17 end.
Definition sdk_initializer_body initializer:=match initializer with
  gateway_initialize_actions=>exchange_actions_initialize|gateway_initialize_attributes=>exchange_attributes_initialize end.
Definition sdk_initializer_call initializer:=match sdk_initializer_body initializer with Ssequence call _=>call|_=>Sskip end.
Definition sdk_initializer_bind initializer:=match sdk_initializer_body initializer with Ssequence _ bind=>bind|_=>Sskip end.
Definition sdk_initializer_start initializer:=exchange_setup_after(match initializer with
  gateway_initialize_actions=>6|gateway_initialize_attributes=>8 end).
Definition sdk_initializer_after initializer:=exchange_setup_after(match initializer with
  gateway_initialize_actions=>7|gateway_initialize_attributes=>9 end).
Definition sdk_initializer_guard initializer:=match initializer with
  gateway_initialize_actions=>exchange_actions_guard|gateway_initialize_attributes=>exchange_attributes_guard end.
Definition sdk_initializer_rest initializer:=exchange_setup_after(match initializer with
  gateway_initialize_actions=>8|gateway_initialize_attributes=>10 end).
Definition sdk_initializer_cont initializer environment temporaries:=
  Kcall(Some(sdk_initializer_destination initializer))f_host_exchange environment temporaries
    (Kseq(sdk_initializer_bind initializer)(Kseq(sdk_initializer_after initializer)Kstop)).
Definition sdk_initializer_temps initializer status temporaries:=PTree.set _setup(Vint status)
  (PTree.set(sdk_initializer_destination initializer)(Vint status)temporaries).

Lemma actual_sdk_initializer_source_call(ge:Clight.genv)initializer environment temporaries memory object symbol:
  environment!(sdk_initializer_identifier initializer)=Some(object,sdk_initializer_type initializer)->
  environment!(gateway_spawn_identifier(sdk_initializer_api initializer))=None->
  Genv.find_symbol ge(gateway_spawn_identifier(sdk_initializer_api initializer))=Some symbol->
  Genv.find_funct_ptr ge symbol=Some(gateway_spawn_signature(sdk_initializer_api initializer))->
  store_edge ge(State f_host_exchange(sdk_initializer_call initializer)
    (Kseq(sdk_initializer_bind initializer)(Kseq(sdk_initializer_after initializer)Kstop))environment temporaries memory)
    (Callstate(gateway_spawn_signature(sdk_initializer_api initializer))[Vptr object Ptrofs.zero]
      (sdk_initializer_cont initializer environment temporaries)memory).
Proof.
  intros LOCATION UNSHADOWED SYMBOL FUNCTION;destruct initializer.
  - eapply gateway_sdk_source_call with(api:=gateway_actions_init_api);[exact UNSHADOWED|exact SYMBOL|exact FUNCTION|].
    eapply cons_argument_values with(v:=Vptr object Ptrofs.zero);
      [apply local_address_expression;exact LOCATION|reflexivity|apply no_argument_values].
  - eapply gateway_sdk_source_call with(api:=gateway_attributes_init_api);[exact UNSHADOWED|exact SYMBOL|exact FUNCTION|].
    eapply cons_argument_values with(v:=Vptr object Ptrofs.zero);
      [apply local_address_expression;exact LOCATION|reflexivity|apply no_argument_values].
Qed.

Theorem actual_sdk_initializer_prefix {World Event}(backend:gateway_backend World Event)
    property(CLOSED:gateway_ambient_closed backend property)initializer allocation_before allocated environment temporaries memory object:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  environment!(sdk_initializer_identifier initializer)=Some(object,sdk_initializer_type initializer)->
  gateway_memory_prefix backend(Clight.globalenv prog)
    (Callstate(gateway_spawn_signature(sdk_initializer_api initializer))[Vptr object Ptrofs.zero]
      (sdk_initializer_cont initializer environment temporaries)memory)property property
    (State f_host_exchange(sdk_initializer_start initializer)Kstop environment temporaries memory).
Proof.
  intros ALLOC LOCATION.
  eapply gateway_memory_same with(following:=State f_host_exchange(sdk_initializer_body initializer)
    (Kseq(sdk_initializer_after initializer)Kstop)environment temporaries memory);
    [exact CLOSED|cbn;destruct initializer;tauto|intros;destruct initializer;apply unchanged_store_edge,edge_seq|].
  eapply gateway_memory_same with(following:=State f_host_exchange(sdk_initializer_call initializer)
    (Kseq(sdk_initializer_bind initializer)(Kseq(sdk_initializer_after initializer)Kstop))environment temporaries memory);
    [exact CLOSED|cbn;destruct initializer;tauto|intros;destruct initializer;apply unchanged_store_edge,edge_seq|].
  eapply gateway_memory_same with(following:=Callstate(gateway_spawn_signature(sdk_initializer_api initializer))[Vptr object Ptrofs.zero]
    (sdk_initializer_cont initializer environment temporaries)memory);
    [exact CLOSED|cbn;destruct initializer;tauto| |].
  - intros before world READY;destruct(actual_gateway_spawn_binding(sdk_initializer_api initializer))as[symbol[SYMBOL FUNCTION]].
    eapply actual_sdk_initializer_source_call;[exact LOCATION| |exact SYMBOL|exact FUNCTION].
    eapply actual_exchange_setup_unshadowed;[exact ALLOC|destruct initializer;cbn;intuition discriminate].
  - apply gateway_memory_identity.
Qed.

Theorem actual_sdk_initializer_return_path {World Event}(backend:gateway_backend World Event)
    target property(CLOSED:gateway_ambient_closed backend property)initializer allocation_before allocated environment temporaries memory status:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  (status=Int.zero->gateway_launch_path backend target property
    (State f_host_exchange(sdk_initializer_rest initializer)Kstop environment(sdk_initializer_temps initializer status temporaries)memory))->
  gateway_launch_path backend target property(Returnstate(Vint status)(sdk_initializer_cont initializer environment temporaries)memory).
Proof.
  intros ALLOC SUCCESS.
  set(returned:=PTree.set(sdk_initializer_destination initializer)(Vint status)temporaries).
  set(marked:=sdk_initializer_temps initializer status temporaries).
  eapply gateway_launch_same with(following:=State f_host_exchange Sskip
    (Kseq(sdk_initializer_bind initializer)(Kseq(sdk_initializer_after initializer)Kstop))environment returned memory);
    [exact CLOSED|cbn;tauto|exact I|intros;apply unchanged_store_edge,edge_returnstate|].
  eapply gateway_launch_same with(following:=State f_host_exchange(sdk_initializer_bind initializer)
    (Kseq(sdk_initializer_after initializer)Kstop)environment returned memory);
    [exact CLOSED|cbn;tauto|exact I|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_launch_same with(following:=State f_host_exchange Sskip(Kseq(sdk_initializer_after initializer)Kstop)
    environment marked memory);
    [exact CLOSED|cbn;destruct initializer;tauto|exact I| |].
  { intros before world READY;destruct initializer;apply certified_set_edge,old_expression_value,value_temp;apply PTree.gss. }
  eapply gateway_launch_same with(following:=State f_host_exchange(sdk_initializer_after initializer)Kstop environment marked memory);
    [exact CLOSED|cbn;tauto|exact I|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_launch_same with(following:=State f_host_exchange(sdk_initializer_guard initializer)
    (Kseq(sdk_initializer_rest initializer)Kstop)environment marked memory);
    [exact CLOSED|cbn;destruct initializer;tauto|exact I|intros;destruct initializer;apply unchanged_store_edge,edge_seq|].
  destruct(Int.eq status Int.zero)eqn:ZERO.
  - apply Int.same_if_eq in ZERO;subst status.
    eapply gateway_launch_same with(following:=State f_host_exchange Sskip(Kseq(sdk_initializer_rest initializer)Kstop)
      environment marked memory);
      [exact CLOSED|cbn;destruct initializer;tauto|exact I| |].
    { intros before world READY;destruct initializer;
        (apply certified_if_edge with(v:=Vint Int.zero)(b:=false);
         [apply old_expression_value,value_temp;apply PTree.gss|reflexivity]). }
    eapply gateway_launch_same with(following:=State f_host_exchange(sdk_initializer_rest initializer)Kstop environment marked memory);
      [exact CLOSED|cbn;tauto|exact I|intros;apply unchanged_store_edge,edge_skip_seq|apply SUCCESS;reflexivity].
  - eapply gateway_launch_same with(following:=State f_host_exchange(exchange_guard_failure(sdk_initializer_guard initializer))
      (Kseq(sdk_initializer_rest initializer)Kstop)environment marked memory);
      [exact CLOSED|cbn;destruct initializer;tauto|exact I| |].
    { intros before world READY;destruct initializer.
      all:apply certified_if_edge with(v:=Vint status)(b:=true);
        [apply old_expression_value,value_temp;apply PTree.gss|].
      all:change(Some(negb(Int.eq status Int.zero))=Some true);rewrite ZERO;reflexivity. }
    eapply gateway_launch_failure with(allowed:=exchange_error_allowed).
    + exact(actual_exchange_error_bindings allocation_before environment allocated ALLOC).
    + apply((proj1(Forall_forall _ _))actual_exchange_errors_return).
      destruct initializer.
      * change(In(exchange_guard_failure exchange_actions_guard)exchange_early_errors).
        unfold exchange_early_errors;apply in_map;cbn;auto 8.
      * change(In(exchange_guard_failure exchange_attributes_guard)exchange_early_errors).
        unfold exchange_early_errors;apply in_map;cbn;auto 8.
    + reflexivity.
Qed.
