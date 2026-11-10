(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Outcome validation selects the real builtin type-test operation. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayFunctionEntry GatewayNoLocalEntry GatewayCalls
  GatewaySourcePaths GatewaySourceCuts GatewaySourceBoundCalls GatewaySourceSegmentAutomation GatewayFramedRuntime
  GatewaySourceObjectReceipt GatewayObjects GatewayUnaryExpressions GatewayReturns GatewayReturnIdentity GatewayRuntimeCuts GatewayReadonly.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_has_type_return_statement:=Sreturn(Some(Etempvar _t'2 tint)).
Definition gateway_has_type_instance_cont parameters:=
  Kcall(Some _t'2)f_host_has_type empty_env parameters(Kseq gateway_has_type_return_statement Kstop).

Lemma gateway_has_type_entry_parameters ge value class optional before environment parameters allocated:
  function_entry2 ge f_host_has_type[value;class;Vint optional]before environment parameters allocated->
  environment=empty_env /\allocated=before /\parameters!_value=Some value /\parameters!_type=Some class /\
    parameters!_optional=Some(Vint optional).
Proof.
  intro ENTRY;destruct(gateway_no_local_entry ge f_host_has_type _ _ _ _ _ eq_refl ENTRY)as[ENV MEMORY].
  split;[exact ENV|]. split;[exact MEMORY|]. inversion ENTRY;subst.
  match goal with BIND:bind_parameter_temps _ _ _=Some _|-_=>
    change(Some(PTree.set _optional(Vint optional)(PTree.set _type class(PTree.set _value value
      (create_undef_temps(fn_temps f_host_has_type)))))=Some parameters)in BIND;
    inversion BIND;subst parameters end.
  repeat split;repeat rewrite PTree.gso by discriminate;apply PTree.gss.
Qed.

Theorem gateway_has_type_required_source {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)parameters object offset class class_offset before symbol definition:
  gateway_ambient_closed backend property->parameters!_value=Some(Vptr object offset)->
  parameters!_type=Some(Vptr class class_offset)->parameters!_optional=Some(Vint Int.zero)->
  (forall memory world,property memory world->Mem.weak_valid_pointer memory object(Ptrofs.unsigned offset)=true)->
  Genv.find_symbol ge _PyObject_IsInstance=Some symbol->Genv.find_funct_ptr ge symbol=Some definition->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr);tptr(Tstruct __object noattr)]tint cc_default->
  exists selected,
    gateway_source_path backend ge definition[Vptr object offset;Vptr class class_offset]
      (gateway_has_type_instance_cont selected)property
      (State f_host_has_type(fn_body f_host_has_type)Kstop empty_env parameters before)property /\
    selected!_value=parameters!_value /\selected!_type=parameters!_type.
Proof.
  intros CLOSED VALUE CLASS OPTIONAL POINTER SYMBOL FUNCTION TYPE;eexists;split.
  - gateway_bound_source_call CLOSED
      ltac:(fun _=>first[
        eapply gateway_unary_expression_value with(value:=Vptr object offset)(result:=Vint Int.zero);
          [apply old_expression_value,value_temp;exact VALUE|
           match goal with GOOD:property ?memory ?world|-_=>
             change(option_map(fun flag=>Val.of_bool(negb flag))
               (if Mem.weak_valid_pointer memory object(Ptrofs.unsigned offset)then Some true else None)=Some(Vint Int.zero));
             rewrite(POINTER memory world GOOD);reflexivity end]])
      ltac:(fun _=>first[exact OPTIONAL|reflexivity]).
    eapply gateway_source_same with(target:=Callstate definition[Vptr object offset;Vptr class class_offset]
      (gateway_has_type_instance_cont _)before).
    + exact CLOSED.
    + cbn;tauto.
    + intros;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
      * reflexivity.
      * apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
      * apply cons_argument_values with(v:=Vptr object offset).
        -- apply old_expression_value,value_temp;repeat rewrite PTree.gso by discriminate;exact VALUE.
        -- reflexivity.
        -- apply cons_argument_values with(v:=Vptr class class_offset).
           ++ eapply cast_expression_value;[apply old_expression_value,value_temp;
                repeat rewrite PTree.gso by discriminate;exact CLASS|reflexivity].
           ++ reflexivity.
           ++ apply no_argument_values.
      * change(Genv.find_funct_ptr ge symbol=Some definition);exact FUNCTION.
      * exact TYPE.
    + apply gateway_source_reached;auto.
  - split;repeat rewrite PTree.gso by discriminate;reflexivity.
Qed.

Theorem gateway_has_type_instance_return {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)parameters status before world events value after next:
  gateway_ambient_closed backend property->property before world->
  gateway_steps backend ge(gateway_live(Returnstate(Vint status)(gateway_has_type_instance_cont parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  value=Vint status /\property after next.
Proof.
  intros CLOSED INPUT RUN.
  destruct(gateway_uniform_edge_side_cut backend ge property CLOSED
    (Returnstate(Vint status)(gateway_has_type_instance_cont parameters)before)
    (State f_host_has_type Sskip(Kseq gateway_has_type_return_statement Kstop)empty_env(PTree.set _t'2(Vint status)parameters)before)
    before world events value after next ltac:(cbn;tauto)
    ltac:(intros;apply unchanged_store_edge,edge_returnstate)INPUT RUN)
    as(prefix &rest &called &owner &EVENTS &AMBIENT &PREFIX &READY &REST).
  destruct(gateway_uniform_edge_side_cut backend ge property CLOSED
    (State f_host_has_type Sskip(Kseq gateway_has_type_return_statement Kstop)empty_env(PTree.set _t'2(Vint status)parameters)called)
    (State f_host_has_type gateway_has_type_return_statement Kstop empty_env(PTree.set _t'2(Vint status)parameters)called)
    called owner rest value after next ltac:(cbn;tauto)
    ltac:(intros;apply unchanged_store_edge,edge_skip_seq)READY REST)
    as(pending &suffix &memory &current &REST_EVENTS &PENDING &TO_RETURN &AT_RETURN &RETURN).
  split.
  - eapply(gateway_return_expression_identity backend ge f_host_has_type(Etempvar _t'2 tint)Kstop empty_env
      (PTree.set _t'2(Vint status)parameters)memory current(Vint status)suffix value after next);
      [reflexivity| | |exact RETURN].
    + intros;apply old_expression_value,value_temp,PTree.gss.
    + intros cast_memory converted CAST;cbn in CAST;inversion CAST;reflexivity.
  - eapply(gateway_readonly_run_side backend ge property CLOSED
      (State f_host_has_type gateway_has_type_return_statement Kstop empty_env(PTree.set _t'2(Vint status)parameters)memory)
      current suffix value after next);[|exact AT_RETURN|exact RETURN].
    repeat split;reflexivity.
Qed.

Theorem gateway_actual_required_type_check {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)(post:int->mem->World->Prop)
    object offset class class_offset before world events value after next symbol definition:
  gateway_ambient_closed backend property->(forall status,gateway_ambient_closed backend(post status))->
  property before world->
  (forall memory current,property memory current->Mem.weak_valid_pointer memory object(Ptrofs.unsigned offset)=true)->
  Genv.find_symbol ge _PyObject_IsInstance=Some symbol->Genv.find_funct_ptr ge symbol=Some definition->
  gateway_object_api_definition gateway_api_is_instance=Some definition->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr);tptr(Tstruct __object noattr)]tint cc_default->
  (forall memory current result changed following observed,property memory current->
    gateway_object_operation backend gateway_api_is_instance[Vptr object offset;Vptr class class_offset]
      memory current result changed following observed->exists status,result=Vint status /\post status changed following)->
  gateway_steps backend ge(gateway_live(Callstate(Internal f_host_has_type)
    [Vptr object offset;Vptr class class_offset;Vint Int.zero]Kstop before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists prefix suffix called called_world changed changed_world status observed parameters,
    events=prefix++gateway_primitive observed::suffix /\value=Vint status /\post status after next /\
    property called called_world /\
    gateway_steps backend ge(gateway_live(Callstate(Internal f_host_has_type)
      [Vptr object offset;Vptr class class_offset;Vint Int.zero]Kstop before)world)prefix
      (gateway_live(Callstate definition[Vptr object offset;Vptr class class_offset]
        (gateway_has_type_instance_cont parameters)called)called_world) /\
    gateway_object_operation backend gateway_api_is_instance[Vptr object offset;Vptr class class_offset]
      called called_world(Vint status)changed changed_world observed /\
    gateway_steps backend ge
      (gateway_live(Returnstate(Vint status)(gateway_has_type_instance_cont parameters)changed)changed_world)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros CLOSED POST_CLOSED INPUT POINTER SYMBOL FUNCTION DEFINITION TYPE OBSERVER RUN.
  destruct(actual_gateway_function_entry_ambient backend ge f_host_has_type
    [Vptr object offset;Vptr class class_offset;Vint Int.zero]Kstop before world events value Kstop after next RUN)
    as(pending &rest &entry_memory &entry_world &environment &temporaries &allocated &EVENTS &AMBIENT &PREFIX &ENTRY &REST).
  pose proof(gateway_has_type_entry_parameters ge _ _ _ _ _ _ _ ENTRY)
    as[ENVIRONMENT[MEMORY[VALUE[CLASS OPTIONAL]]]];subst environment allocated.
  assert(READY:property entry_memory entry_world).
  { exact(gateway_ambient_run_ready backend ge property CLOSED
      (Callstate(Internal f_host_has_type)[Vptr object offset;Vptr class class_offset;Vint Int.zero]Kstop before)
      before world pending entry_memory entry_world INPUT AMBIENT PREFIX). }
  destruct(gateway_has_type_required_source backend ge property temporaries object offset class class_offset entry_memory
    symbol definition CLOSED VALUE CLASS OPTIONAL POINTER SYMBOL FUNCTION TYPE)as(parameters &PATH &VALUE_SAVED &CLASS_SAVED).
  destruct(gateway_source_object_receipt backend ge gateway_api_is_instance definition[Vptr object offset;Vptr class class_offset]
    (gateway_has_type_instance_cont parameters)property _ entry_memory entry_world rest value after next
    DEFINITION ltac:(cbn;exact I)ltac:(cbn;lia)CLOSED PATH READY REST)
    as(prefix &suffix &called &called_world &returned &changed &changed_world &observed &TAIL &CALLED &TO_CALL &OPERATION &SUFFIX).
  destruct(OBSERVER called called_world returned changed changed_world observed CALLED OPERATION)
    as(status &RETURNED &POST);subst returned.
  destruct(gateway_has_type_instance_return backend ge(post status)parameters status changed changed_world suffix value after next
    (POST_CLOSED status)POST SUFFIX)as[SAME FINAL].
  exists(pending++gateway_source E0::prefix),suffix,called,called_world,changed,changed_world,status,observed,parameters.
  split;[rewrite EVENTS,TAIL,<-app_assoc;reflexivity|]. split;[exact SAME|]. split;[exact FINAL|]. split;[exact CALLED|]. split.
  - eapply gateway_steps_append;[exact PREFIX|].
    econstructor;[apply gateway_internal;[exact I|apply step_internal_function;exact ENTRY]|exact TO_CALL].
  - split;assumption.
Qed.
