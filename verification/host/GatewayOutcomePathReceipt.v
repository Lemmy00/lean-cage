(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Successful construction forces the same actual output insertion to return zero. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayObjects GatewaySourcePaths GatewaySourceObjectReceipt GatewaySourceSDKReceipt
  GatewayOutcomePathSource GatewayOutcomeOutputSource GatewayContexts GatewayFramedRuntime.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_actual_outcome_path_insert {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)environment parameters copy copy_offset path path_offset before world events value after next
    set_symbol set_definition name release_symbol release_external release_types release_result release_convention:
  gateway_ambient_closed backend property->property before world->parameters!_copy=Some(Vptr copy copy_offset)->
  (forall memory current,property memory current->Mem.weak_valid_pointer memory path(Ptrofs.unsigned path_offset)=true)->
  environment!_PyDict_SetItemString=None->environment!___stringlit_40=None->environment!_Py_DecRef=None->
  Genv.find_symbol ge _PyDict_SetItemString=Some set_symbol->Genv.find_funct_ptr ge set_symbol=Some set_definition->
  Genv.find_symbol ge ___stringlit_40=Some name->
  type_of_fundef set_definition=Tfunction[tptr(Tstruct __object noattr);tptr tschar;tptr(Tstruct __object noattr)]tint cc_default->
  gateway_object_api_definition gateway_api_dict_set_string=Some set_definition->
  Genv.find_symbol ge _Py_DecRef=Some release_symbol->
  Genv.find_funct_ptr ge release_symbol=Some(External release_external release_types release_result release_convention)->
  type_of_fundef(External release_external release_types release_result release_convention)=Tfunction[tptr(Tstruct __object noattr)]tvoid cc_default->
  (forall memory current returned changed following observed,property memory current->
    gateway_object_operation backend gateway_api_dict_set_string[Vptr copy copy_offset;Vptr name Ptrofs.zero;Vptr path path_offset]
      memory current returned changed following observed->exists status,returned=Vint status)->
  gateway_steps backend ge(gateway_live(Returnstate(Vptr path path_offset)(gateway_outcome_path_cont environment parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  exists prefix suffix selected memory current changed following observed,
    events=prefix++gateway_primitive observed::suffix /\selected!_copy=Some(Vptr copy copy_offset) /\
    selected!_path=Some(Vptr path path_offset) /\property memory current /\
    gateway_object_operation backend gateway_api_dict_set_string[Vptr copy copy_offset;Vptr name Ptrofs.zero;Vptr path path_offset]
      memory current(Vint Int.zero)changed following observed /\
    gateway_steps backend ge
      (gateway_live(Returnstate(Vint Int.zero)(gateway_outcome_path_set_cont environment selected)changed)following)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros CLOSED INPUT COPY POINTER SET_LOCAL NAME_LOCAL RELEASE_LOCAL SET_SYMBOL SET_FUNCTION NAME SET_TYPE SET_API
    RELEASE_SYMBOL RELEASE_FUNCTION RELEASE_TYPE TYPED RUN NONNULL.
  destruct(gateway_outcome_path_set_source backend ge property environment parameters copy copy_offset path path_offset before set_symbol
    set_definition name CLOSED COPY POINTER SET_LOCAL NAME_LOCAL SET_SYMBOL SET_FUNCTION NAME SET_TYPE)
    as[selected[SET_SOURCE[SELECTED_COPY[SELECTED_PATH SELECTED_DATA]]]].
  destruct(gateway_source_object_receipt backend ge gateway_api_dict_set_string set_definition
    [Vptr copy copy_offset;Vptr name Ptrofs.zero;Vptr path path_offset](gateway_outcome_path_set_cont environment selected)
    property(Returnstate(Vptr path path_offset)(gateway_outcome_path_cont environment parameters)before)
    before world events value after next SET_API ltac:(exact I)ltac:(cbn;lia)CLOSED SET_SOURCE INPUT RUN)
    as(prefix &suffix &memory &current &returned &changed &following &observed &EVENTS &READY &PREFIX &OPERATION &REST).
  destruct(TYPED memory current returned changed following observed READY OPERATION)as[status STATUS];subst returned.
  assert(ZERO:status=Int.zero).
  { destruct(Int.eq_dec status Int.zero)as[SAME|DIFFERENT];[exact SAME|].
    assert(TRUE_CLOSED:gateway_ambient_closed backend(fun _ _=>True))by(unfold gateway_ambient_closed;intros;exact I).
    destruct(gateway_outcome_path_release_source backend ge(fun _ _=>True)environment selected path path_offset status changed
      release_symbol(External release_external release_types release_result release_convention)TRUE_CLOSED SELECTED_PATH
      RELEASE_LOCAL RELEASE_SYMBOL RELEASE_FUNCTION RELEASE_TYPE)
      as[release_parameters[RELEASE_SOURCE[RELEASE_COPY[RELEASE_PATH[RELEASE_FAILED RELEASE_DATA]]]]].
    destruct(gateway_source_sdk_receipt backend ge release_external release_types release_result release_convention[Vptr path path_offset]
      (gateway_outcome_path_release_cont environment release_parameters)(fun _ _=>True)
      (Returnstate(Vint status)(gateway_outcome_path_set_cont environment selected)changed)changed following suffix value after next
      ltac:(exact I)ltac:(cbn;lia)TRUE_CLOSED RELEASE_SOURCE I REST)
      as(pending &tail &call_memory &call_world &ignored &done_memory &done_world &release_event &TAIL &GOOD &TO_RELEASE &RELEASE &SUFFIX).
    exfalso;apply NONNULL;eapply gateway_outcome_path_failed;[exact RELEASE_FAILED|exact DIFFERENT|exact SUFFIX]. }
  subst status;exists prefix,suffix,selected,memory,current,changed,following,observed.
  split;[exact EVENTS|]. split;[rewrite SELECTED_COPY;exact COPY|]. split;[exact SELECTED_PATH|].
  split;[exact READY|]. split;assumption.
Qed.
