(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A getter roots the actually selected data before any SDK callback. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayOutcome GatewayOutcomeConstruction
  GatewaySourceBoundCalls GatewaySourceSegmentAutomation GatewaySourcePaths GatewaySourceCuts GatewayFramedRuntime
  GatewayUnaryExpressions GatewayFailurePaths GatewayValueReturns GatewayNoLocalEntry GatewayFunctionEntry GatewayCalls.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_observation_after_root:=gateway_outcome_right_suffix 3(fn_body f_host_outcome_observation).
Definition gateway_observation_root_cont parameters:=
  Kcall None f_host_outcome_observation empty_env parameters(Kseq gateway_observation_after_root Kstop).

Lemma gateway_observation_entry_parameters ge self unused before environment parameters allocated:
  function_entry2 ge f_host_outcome_observation[self;unused]before environment parameters allocated->
  parameters!_self=Some self /\parameters!_unused=Some unused.
Proof.
  intro ENTRY;inversion ENTRY;subst.
  match goal with BIND:bind_parameter_temps _ _ _=Some _|-_=>
    change(Some(PTree.set _unused unused(PTree.set _self self
      (create_undef_temps(fn_temps f_host_outcome_observation))))=Some parameters)in BIND;
    inversion BIND;subst parameters end.
  split;[rewrite PTree.gso by discriminate;apply PTree.gss|apply PTree.gss].
Qed.

Definition gateway_observation_key_tail:=gateway_outcome_right_suffix 1 gateway_observation_after_root.
Definition gateway_observation_key_cont parameters:=
  Kcall(Some _t'1)f_host_outcome_observation empty_env parameters
    (Kseq(Sset _key(Etempvar _t'1(tptr(Tstruct __object noattr))))(Kseq gateway_observation_key_tail Kstop)).
Definition gateway_observation_lookup_tail:=gateway_outcome_right_suffix 2 gateway_observation_key_tail.
Definition gateway_observation_lookup_cont parameters:=
  Kcall(Some _t'2)f_host_outcome_observation empty_env parameters
    (Kseq(Sset _value(Etempvar _t'2(tptr(Tstruct __object noattr))))(Kseq gateway_observation_lookup_tail Kstop)).
Definition gateway_observation_after_value_root:=gateway_outcome_right_suffix 1 gateway_observation_lookup_tail.
Definition gateway_observation_value_root_cont parameters:=
  Kcall None f_host_outcome_observation empty_env parameters(Kseq gateway_observation_after_value_root Kstop).
Definition gateway_observation_after_key_release:=gateway_outcome_right_suffix 2 gateway_observation_lookup_tail.
Definition gateway_observation_key_release_cont parameters:=
  Kcall None f_host_outcome_observation empty_env parameters(Kseq gateway_observation_after_key_release Kstop).
Definition gateway_observation_return_statement:=Sreturn(Some(Etempvar _value(tptr(Tstruct __object noattr)))).
Definition gateway_observation_release_cont parameters:=
  Kcall None f_host_outcome_observation empty_env parameters(Kseq gateway_observation_return_statement Kstop).

Theorem gateway_observation_key_source_path {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)parameters ignored before symbol definition json:
  gateway_ambient_closed backend property->
  Genv.find_symbol ge _PyUnicode_FromString=Some symbol->Genv.find_funct_ptr ge symbol=Some definition->
  Genv.find_symbol ge ___stringlit_51=Some json->
  type_of_fundef definition=Tfunction[tptr tschar](tptr(Tstruct __object noattr))cc_default->
  gateway_source_path backend ge definition[Vptr json Ptrofs.zero](gateway_observation_key_cont parameters)property
    (Returnstate ignored(gateway_observation_root_cont parameters)before)property.
Proof.
  intros CLOSED SYMBOL FUNCTION JSON TYPE.
  gateway_bound_source_call CLOSED ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
  eapply gateway_source_same with(target:=Callstate definition[Vptr json Ptrofs.zero]
    (gateway_observation_key_cont parameters)before).
  - exact CLOSED.
  - cbn;tauto.
  - intros;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
    + reflexivity.
    + apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
    + apply cons_argument_values with(v:=Vptr json Ptrofs.zero).
      * apply old_expression_value;eapply value_function;[reflexivity|exact JSON|reflexivity].
      * reflexivity.
      * apply no_argument_values.
    + change(Genv.find_funct_ptr ge symbol=Some definition);exact FUNCTION.
    + exact TYPE.
  - apply gateway_source_reached;auto.
Qed.

Theorem gateway_observation_lookup_source_path {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)parameters data data_offset key key_offset before symbol definition:
  gateway_ambient_closed backend property->parameters!_selected_data=Some(Vptr data data_offset)->
  (forall memory world,property memory world->Mem.weak_valid_pointer memory key(Ptrofs.unsigned key_offset)=true)->
  Genv.find_symbol ge _PyDict_GetItemWithError=Some symbol->Genv.find_funct_ptr ge symbol=Some definition->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr);tptr(Tstruct __object noattr)]
    (tptr(Tstruct __object noattr))cc_default->
  exists selected,
    gateway_source_path backend ge definition[Vptr data data_offset;Vptr key key_offset]
      (gateway_observation_lookup_cont selected)property
      (Returnstate(Vptr key key_offset)(gateway_observation_key_cont parameters)before)property /\
    selected!_key=Some(Vptr key key_offset) /\selected!_selected_data=parameters!_selected_data.
Proof.
  intros CLOSED DATA POINTER SYMBOL FUNCTION TYPE;eexists;split.
  - gateway_bound_source_call CLOSED
      ltac:(fun _=>eapply gateway_unary_expression_value with(value:=Vptr key key_offset)(result:=Vint Int.zero);
        [gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|
         match goal with GOOD:property ?memory ?world|-_=>
           change(option_map(fun flag=>Val.of_bool(negb flag))
             (if Mem.weak_valid_pointer memory key(Ptrofs.unsigned key_offset)then Some true else None)=Some(Vint Int.zero));
           rewrite(POINTER memory world GOOD);reflexivity end])ltac:(fun _=>reflexivity).
    eapply gateway_source_same with(target:=Callstate definition[Vptr data data_offset;Vptr key key_offset]
      (gateway_observation_lookup_cont _)before).
    + exact CLOSED.
    + cbn;tauto.
    + intros;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
      * reflexivity.
      * apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
      * apply cons_argument_values with(v:=Vptr data data_offset).
        -- gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
        -- reflexivity.
        -- apply cons_argument_values with(v:=Vptr key key_offset).
          ++ gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
          ++ reflexivity.
          ++ apply no_argument_values.
      * change(Genv.find_funct_ptr ge symbol=Some definition);exact FUNCTION.
      * exact TYPE.
    + apply gateway_source_reached;auto.
  - unfold set_opttemp;split;[apply PTree.gss|]. repeat rewrite PTree.gso by discriminate;reflexivity.
Qed.

Theorem gateway_observation_present_root_source_path {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)parameters value value_offset before symbol definition:
  gateway_ambient_closed backend property->
  (forall memory world,property memory world->Mem.weak_valid_pointer memory value(Ptrofs.unsigned value_offset)=true)->
  Genv.find_symbol ge _Py_IncRef=Some symbol->Genv.find_funct_ptr ge symbol=Some definition->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr)]tvoid cc_default->
  exists selected,
    gateway_source_path backend ge definition[Vptr value value_offset](gateway_observation_value_root_cont selected)property
      (Returnstate(Vptr value value_offset)(gateway_observation_lookup_cont parameters)before)property /\
    selected!_value=Some(Vptr value value_offset) /\selected!_selected_data=parameters!_selected_data /\
    selected!_key=parameters!_key.
Proof.
  intros CLOSED POINTER SYMBOL FUNCTION TYPE;eexists;split.
  - gateway_bound_source_call CLOSED
      ltac:(fun _=>gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity))
      ltac:(fun _=>first[
        match goal with GOOD:property ?memory ?world|-bool_val _ _ _=Some ?branch=>
          unify branch true;change((if Mem.weak_valid_pointer memory value(Ptrofs.unsigned value_offset)then Some true else None)=Some true);
          rewrite(POINTER memory world GOOD);reflexivity end|reflexivity]).
    eapply gateway_source_same with(target:=Callstate definition[Vptr value value_offset]
      (gateway_observation_value_root_cont _)before).
    + exact CLOSED.
    + cbn;tauto.
    + intros;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
      * reflexivity.
      * apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
      * apply cons_argument_values with(v:=Vptr value value_offset).
        -- gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
        -- reflexivity.
        -- apply no_argument_values.
      * change(Genv.find_funct_ptr ge symbol=Some definition);exact FUNCTION.
      * exact TYPE.
    + apply gateway_source_reached;auto.
  - unfold set_opttemp;repeat split;repeat rewrite PTree.gso by discriminate;first[apply PTree.gss|reflexivity].
Qed.

Theorem gateway_observation_key_release_source_path {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)parameters key key_offset ignored before symbol definition:
  gateway_ambient_closed backend property->parameters!_key=Some(Vptr key key_offset)->
  Genv.find_symbol ge _Py_DecRef=Some symbol->Genv.find_funct_ptr ge symbol=Some definition->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr)]tvoid cc_default->
  gateway_source_path backend ge definition[Vptr key key_offset](gateway_observation_key_release_cont parameters)property
    (Returnstate ignored(gateway_observation_value_root_cont parameters)before)property.
Proof.
  intros CLOSED KEY SYMBOL FUNCTION TYPE.
  gateway_bound_source_call CLOSED ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
  eapply gateway_source_same with(target:=Callstate definition[Vptr key key_offset]
    (gateway_observation_key_release_cont parameters)before).
  - exact CLOSED.
  - cbn;tauto.
  - intros;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
    + reflexivity.
    + apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
    + apply cons_argument_values with(v:=Vptr key key_offset).
      * gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
      * reflexivity.
      * apply no_argument_values.
    + change(Genv.find_funct_ptr ge symbol=Some definition);exact FUNCTION.
    + exact TYPE.
  - apply gateway_source_reached;auto.
Qed.

Theorem gateway_observation_release_source_path {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)parameters data data_offset value value_offset ignored before symbol definition:
  gateway_ambient_closed backend property->parameters!_selected_data=Some(Vptr data data_offset)->
  parameters!_value=Some(Vptr value value_offset)->
  (forall memory world,property memory world->Mem.weak_valid_pointer memory value(Ptrofs.unsigned value_offset)=true)->
  Genv.find_symbol ge _Py_DecRef=Some symbol->Genv.find_funct_ptr ge symbol=Some definition->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr)]tvoid cc_default->
  exists selected,
    gateway_source_path backend ge definition[Vptr data data_offset](gateway_observation_release_cont selected)property
      (Returnstate ignored(gateway_observation_key_release_cont parameters)before)property /\
    selected!_value=parameters!_value /\selected!_selected_data=parameters!_selected_data.
Proof.
  intros CLOSED DATA VALUE POINTER SYMBOL FUNCTION TYPE;eexists;split.
  - gateway_bound_source_call CLOSED
      ltac:(fun _=>eapply gateway_unary_expression_value with(value:=Vptr value value_offset)(result:=Vint Int.zero);
        [gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|
         match goal with GOOD:property ?memory ?world|-_=>
           change(option_map(fun flag=>Val.of_bool(negb flag))
             (if Mem.weak_valid_pointer memory value(Ptrofs.unsigned value_offset)then Some true else None)=Some(Vint Int.zero));
           rewrite(POINTER memory world GOOD);reflexivity end])ltac:(fun _=>reflexivity).
    eapply gateway_source_same with(target:=Callstate definition[Vptr data data_offset]
      (gateway_observation_release_cont _)before).
    + exact CLOSED.
    + cbn;tauto.
    + intros;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
      * reflexivity.
      * apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
      * apply cons_argument_values with(v:=Vptr data data_offset).
        -- gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
        -- reflexivity.
        -- apply no_argument_values.
      * change(Genv.find_funct_ptr ge symbol=Some definition);exact FUNCTION.
      * exact TYPE.
    + apply gateway_source_reached;auto.
  - unfold set_opttemp;repeat split;repeat rewrite PTree.gso by discriminate;reflexivity.
Qed.

Theorem gateway_observation_root_source_path {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)parameters object offset data data_offset before symbol definition:
  gateway_ambient_closed backend property->gateway_outcome_member_layout ge->
  parameters!_self=Some(Vptr object offset)->
  (forall memory world,property memory world->
    Mem.loadv Mptr memory(gateway_outcome_slot object offset)=Some(Vptr data data_offset))->
  (forall memory world,property memory world->Mem.weak_valid_pointer memory data(Ptrofs.unsigned data_offset)=true)->
  Genv.find_symbol ge _Py_IncRef=Some symbol->Genv.find_funct_ptr ge symbol=Some definition->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr)]tvoid cc_default->
  exists selected,
    gateway_source_path backend ge definition[Vptr data data_offset](gateway_observation_root_cont selected)
      property(State f_host_outcome_observation(fn_body f_host_outcome_observation)Kstop empty_env parameters before)property /\
    selected!_selected_data=Some(Vptr data data_offset) /\selected!_self=parameters!_self.
Proof.
  intros CLOSED LAYOUT SELF LOAD POINTER SYMBOL FUNCTION TYPE;eexists;split.
  - gateway_bound_source_call CLOSED
      ltac:(fun _=>first[
        eapply gateway_actual_outcome_member_read;[repeat rewrite PTree.gso by discriminate;exact SELF|exact LAYOUT|eapply LOAD;eassumption]|
        eapply gateway_unary_expression_value with(value:=Vptr data data_offset)(result:=Vint Int.zero);
          [gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|
           match goal with GOOD:property ?memory ?world|-_=>
             change(option_map(fun flag=>Val.of_bool(negb flag))
               (if Mem.weak_valid_pointer memory data(Ptrofs.unsigned data_offset)then Some true else None)=Some(Vint Int.zero));
             rewrite(POINTER memory world GOOD);reflexivity end]])ltac:(fun _=>reflexivity).
    eapply gateway_source_same with(target:=Callstate definition[Vptr data data_offset]
      (gateway_observation_root_cont _)before).
    + exact CLOSED.
    + cbn;tauto.
    + intros;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
      * reflexivity.
      * apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
      * apply cons_argument_values with(v:=Vptr data data_offset).
        -- gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
        -- reflexivity.
        -- apply no_argument_values.
      * change(Genv.find_funct_ptr ge symbol=Some definition);exact FUNCTION.
      * exact TYPE.
    + apply gateway_source_reached;auto.
  - split;[apply PTree.gss|]. repeat rewrite PTree.gso by discriminate;reflexivity.
Qed.

Theorem gateway_actual_observation_selects_data {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)object offset unused data data_offset before world events value after next symbol definition:
  gateway_ambient_closed backend property->gateway_outcome_member_layout ge->
  (forall memory current,property memory current->
    Mem.loadv Mptr memory(gateway_outcome_slot object offset)=Some(Vptr data data_offset))->
  (forall memory current,property memory current->Mem.weak_valid_pointer memory data(Ptrofs.unsigned data_offset)=true)->
  Genv.find_symbol ge _Py_IncRef=Some symbol->Genv.find_funct_ptr ge symbol=Some definition->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr)]tvoid cc_default->
  property before world->
  gateway_steps backend ge
    (gateway_live(Callstate(Internal f_host_outcome_observation)[Vptr object offset;unused]Kstop before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists prefix suffix memory current parameters,
    events=prefix++suffix /\
    gateway_steps backend ge
      (gateway_live(Callstate(Internal f_host_outcome_observation)[Vptr object offset;unused]Kstop before)world)prefix
      (gateway_live(Callstate definition[Vptr data data_offset](gateway_observation_root_cont parameters)memory)current) /\
    property memory current /\parameters!_selected_data=Some(Vptr data data_offset) /\
    gateway_steps backend ge
      (gateway_live(Callstate definition[Vptr data data_offset](gateway_observation_root_cont parameters)memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros CLOSED LAYOUT LOAD POINTER SYMBOL FUNCTION TYPE INPUT RUN.
  destruct(actual_gateway_function_entry_ambient backend ge f_host_outcome_observation[Vptr object offset;unused]Kstop
    before world events value Kstop after next RUN)
    as(pending &body_events &entered &owner &environment &parameters &allocated &EVENTS &AMBIENT &PREFIX &ENTRY &BODY).
  destruct(gateway_observation_entry_parameters _ _ _ _ _ _ _ ENTRY)as[SELF UNUSED].
  destruct(gateway_no_local_entry ge f_host_outcome_observation[Vptr object offset;unused]
    entered environment parameters allocated eq_refl ENTRY)as[ENV SAME];subst environment allocated.
  assert(READY:property entered owner).
  { exact(gateway_ambient_run_ready backend ge property CLOSED
      (Callstate(Internal f_host_outcome_observation)[Vptr object offset;unused]Kstop before)
      before world pending entered owner INPUT AMBIENT PREFIX). }
  destruct(gateway_observation_root_source_path backend ge property parameters object offset data data_offset entered symbol definition
    CLOSED LAYOUT SELF LOAD POINTER SYMBOL FUNCTION TYPE)as(selected &PATH &SELECTED &SAVED).
  destruct(gateway_source_path_cut backend ge definition[Vptr data data_offset](gateway_observation_root_cont selected)
    property _ property PATH entered owner body_events value after next READY BODY)
    as(prelude &suffix &memory &current &TAIL &QUIET &PRELUDE &GOOD &REST).
  exists(pending++gateway_source E0::prelude),suffix,memory,current,selected.
  split;[rewrite EVENTS,TAIL,<-app_assoc;reflexivity|]. split.
  - eapply gateway_steps_append;[exact PREFIX|].
    econstructor;[apply gateway_internal;[exact I|apply step_internal_function;exact ENTRY]|exact PRELUDE].
  - split;[exact GOOD|]. split;assumption.
Qed.

Theorem gateway_observation_null_data_source {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)parameters object offset before:
  gateway_ambient_closed backend property->gateway_outcome_member_layout ge->
  parameters!_self=Some(Vptr object offset)->
  (forall memory world,property memory world->Mem.loadv Mptr memory(gateway_outcome_slot object offset)=Some Vnullptr)->
  gateway_failure_when backend ge property
    (State f_host_outcome_observation(fn_body f_host_outcome_observation)Kstop empty_env parameters before).
Proof.
  intros CLOSED LAYOUT SELF LOAD.
  assert(POINTER_RETURN:gateway_pointer_return f_host_outcome_observation)by(repeat eexists).
  gateway_bound_source_failure CLOSED
    ltac:(fun _=>first[
      eapply gateway_actual_outcome_member_read;[repeat rewrite PTree.gso by discriminate;exact SELF|exact LAYOUT|eapply LOAD;eassumption]|
      eapply gateway_unary_expression_value with(value:=Vnullptr)(result:=Vint Int.one);
        [gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|reflexivity]])
    ltac:(fun _=>reflexivity)POINTER_RETURN.
Qed.

Theorem gateway_actual_observation_null_data_returns_null {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)object offset unused before world events value after next:
  gateway_ambient_closed backend property->gateway_outcome_member_layout ge->
  (forall memory current,property memory current->Mem.loadv Mptr memory(gateway_outcome_slot object offset)=Some Vnullptr)->
  property before world->
  gateway_steps backend ge
    (gateway_live(Callstate(Internal f_host_outcome_observation)[Vptr object offset;unused]Kstop before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value=Vnullptr.
Proof.
  intros CLOSED LAYOUT LOAD INPUT RUN.
  destruct(actual_gateway_function_entry_ambient backend ge f_host_outcome_observation[Vptr object offset;unused]Kstop
    before world events value Kstop after next RUN)
    as(pending &body_events &entered &owner &environment &parameters &allocated &EVENTS &AMBIENT &PREFIX &ENTRY &BODY).
  destruct(gateway_observation_entry_parameters _ _ _ _ _ _ _ ENTRY)as[SELF UNUSED].
  destruct(gateway_no_local_entry ge f_host_outcome_observation[Vptr object offset;unused]
    entered environment parameters allocated eq_refl ENTRY)as[ENV SAME];subst environment allocated.
  assert(READY:property entered owner).
  { exact(gateway_ambient_run_ready backend ge property CLOSED
      (Callstate(Internal f_host_outcome_observation)[Vptr object offset;unused]Kstop before)
      before world pending entered owner INPUT AMBIENT PREFIX). }
  exact(gateway_observation_null_data_source backend ge property parameters object offset entered CLOSED LAYOUT SELF LOAD
    entered owner body_events value after next READY BODY).
Qed.

Theorem gateway_observation_released_return_identity {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    parameters selected ignored before world events value after next:
  parameters!_value=Some selected->gateway_object_pointer_value selected->
  gateway_steps backend ge
    (gateway_live(Returnstate ignored(gateway_observation_release_cont parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value=selected.
Proof.
  intros SELECTED POINTER RUN.
  assert(PATH:GatewayReturns.gateway_constant_path ge selected
    (Returnstate ignored(gateway_observation_release_cont parameters)before)).
  { eapply GatewayReturns.gateway_constant_next with(next:=State f_host_outcome_observation Sskip
      (Kseq gateway_observation_return_statement Kstop)empty_env parameters before).
    - cbn;tauto.
    - intros;apply unchanged_store_edge,edge_returnstate.
    - eapply GatewayReturns.gateway_constant_next with(next:=State f_host_outcome_observation gateway_observation_return_statement
        Kstop empty_env parameters before).
      + cbn;tauto.
      + intros;apply unchanged_store_edge,edge_skip_seq.
      + eapply GatewayReturns.gateway_constant_at_return with(value:=selected).
        * reflexivity.
        * intros;apply old_expression_value,value_temp;exact SELECTED.
        * intros;destruct POINTER as[NULL|[block[offset SAME]]];subst selected;reflexivity. }
  eapply GatewayReturns.gateway_constant_path_actual;[exact PATH|exact RUN].
Qed.
