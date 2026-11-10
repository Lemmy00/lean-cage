(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Each real field getter checks its closure and roots selected data. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayOutcome GatewayOutcomeConstruction
  GatewaySourceBoundCalls GatewaySourceSegmentAutomation GatewaySourcePaths GatewaySourceCuts GatewayFramedRuntime
  GatewayUnaryExpressions GatewayFailurePaths GatewayValueReturns GatewayNoLocalEntry GatewayFunctionEntry GatewayCalls.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_field_after_root:=gateway_outcome_right_suffix 4(fn_body f_host_outcome_get).
Definition gateway_field_root_cont parameters:=
  Kcall None f_host_outcome_get empty_env parameters(Kseq gateway_field_after_root Kstop).

Lemma gateway_field_entry_parameters ge self closure before environment parameters allocated:
  function_entry2 ge f_host_outcome_get[self;Vlong closure]before environment parameters allocated->
  parameters!_self=Some self /\parameters!_closure=Some(Vlong closure).
Proof.
  intro ENTRY;inversion ENTRY;subst.
  match goal with BIND:bind_parameter_temps _ _ _=Some _|-_=>
    change(Some(PTree.set _closure(Vlong closure)(PTree.set _self self
      (create_undef_temps(fn_temps f_host_outcome_get))))=Some parameters)in BIND;
    inversion BIND;subst parameters end.
  split;[rewrite PTree.gso by discriminate;apply PTree.gss|apply PTree.gss].
Qed.

Lemma gateway_field_index_compare(ge:Clight.genv)memory index:
  Int64.unsigned index<14->
  sem_binary_operation ge Oge(Vlong index)tulong(Vint(Int.repr 14))tint memory=Some(Vint Int.zero).
Proof.
  intro BOUND.
  change(Some(Val.of_bool(negb(Int64.ltu index(Int64.repr 14))))=Some(Vint Int.zero)).
  assert(LESS:Int64.ltu index(Int64.repr 14)=true).
  { unfold Int64.ltu;change((if zlt(Int64.unsigned index)14 then true else false)=true).
    destruct zlt;[reflexivity|lia]. }
  rewrite LESS;reflexivity.
Qed.


Theorem gateway_field_root_source_path {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)parameters index object offset data data_offset before symbol definition:
  gateway_ambient_closed backend property->gateway_outcome_member_layout ge->
  parameters!_self=Some(Vptr object offset)->parameters!_closure=Some(Vlong index)->Int64.unsigned index<14->
  (forall memory world,property memory world->
    Mem.loadv Mptr memory(gateway_outcome_slot object offset)=Some(Vptr data data_offset))->
  (forall memory world,property memory world->Mem.weak_valid_pointer memory data(Ptrofs.unsigned data_offset)=true)->
  Genv.find_symbol ge _Py_IncRef=Some symbol->Genv.find_funct_ptr ge symbol=Some definition->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr)]tvoid cc_default->
  exists selected,
    gateway_source_path backend ge definition[Vptr data data_offset](gateway_field_root_cont selected)
      property(State f_host_outcome_get(fn_body f_host_outcome_get)Kstop empty_env parameters before)property /\
    selected!_selected_data=Some(Vptr data data_offset) /\selected!_index=Some(Vlong index) /\
    selected!_self=parameters!_self.
Proof.
  intros CLOSED LAYOUT SELF CLOSURE BOUND LOAD POINTER SYMBOL FUNCTION TYPE;eexists;split.
  - gateway_bound_source_call CLOSED
      ltac:(fun _=>first[
        eapply gateway_actual_outcome_member_read;[repeat rewrite PTree.gso by discriminate;exact SELF|exact LAYOUT|eapply LOAD;eassumption]|
        eapply gateway_unary_expression_value with(value:=Vptr data data_offset)(result:=Vint Int.zero);
          [gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|
           match goal with GOOD:property ?memory ?world|-_=>
             change(option_map(fun flag=>Val.of_bool(negb flag))
               (if Mem.weak_valid_pointer memory data(Ptrofs.unsigned data_offset)then Some true else None)=Some(Vint Int.zero));
             rewrite(POINTER memory world GOOD);reflexivity end]])
      ltac:(fun _=>first[apply gateway_field_index_compare;exact BOUND|reflexivity]).
    eapply gateway_source_same with(target:=Callstate definition[Vptr data data_offset](gateway_field_root_cont _)before).
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
  - split;[apply PTree.gss|]. split.
    + repeat rewrite PTree.gso by discriminate;apply PTree.gss.
    + repeat rewrite PTree.gso by discriminate;reflexivity.
Qed.

Definition gateway_field_lookup_tail:=gateway_outcome_right_suffix 1 gateway_field_after_root.
Definition gateway_field_lookup_cont parameters:=
  Kcall(Some _t'2)f_host_outcome_get empty_env parameters
    (Kseq(Sset _value(Etempvar _t'2(tptr(Tstruct __object noattr))))(Kseq gateway_field_lookup_tail Kstop)).
Definition gateway_field_name_offset index:=
  Ptrofs.add Ptrofs.zero(Ptrofs.mul(Ptrofs.repr 8)(Ptrofs.of_int64 index)).

Lemma gateway_field_name_read(ge:Clight.genv)parameters memory table index name:
  parameters!_index=Some(Vlong index)->Genv.find_symbol ge _host_outcome_fields=Some table->
  Mem.loadv Mptr memory(Vptr table(gateway_field_name_offset index))=Some(Vptr name Ptrofs.zero)->
  expression_value ge empty_env parameters memory
    (Ederef(Ebinop Oadd(Evar _host_outcome_fields(tarray(tptr tschar)14))
      (Etempvar _index tulong)(tptr(tptr tschar)))(tptr tschar))(Vptr name Ptrofs.zero).
Proof.
  intros INDEX TABLE LOAD;eapply location_read_value.
  - apply pointer_location_value.
    eapply binary_expression_value with(v:=Vptr table Ptrofs.zero)(w:=Vlong index).
    + apply old_expression_value;eapply value_function;[reflexivity|exact TABLE|reflexivity].
    + apply old_expression_value,value_temp;exact INDEX.
    + reflexivity.
  - eapply deref_loc_value;[reflexivity|exact LOAD].
Qed.

Theorem gateway_field_lookup_source_path {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)parameters data data_offset index before symbol definition table name:
  gateway_ambient_closed backend property->parameters!_selected_data=Some(Vptr data data_offset)->
  parameters!_index=Some(Vlong index)->Genv.find_symbol ge _host_outcome_fields=Some table->
  (forall memory world,property memory world->
    Mem.loadv Mptr memory(Vptr table(gateway_field_name_offset index))=Some(Vptr name Ptrofs.zero))->
  Genv.find_symbol ge _PyDict_GetItemString=Some symbol->Genv.find_funct_ptr ge symbol=Some definition->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr);tptr tschar](tptr(Tstruct __object noattr))cc_default->
  forall ignored,exists selected,
    gateway_source_path backend ge definition[Vptr data data_offset;Vptr name Ptrofs.zero]
      (gateway_field_lookup_cont selected)property(Returnstate ignored(gateway_field_root_cont parameters)before)property /\
    selected!_selected_data=parameters!_selected_data /\selected!_index=parameters!_index /\
    selected!_t'4=Some(Vptr name Ptrofs.zero).
Proof.
  intros CLOSED DATA INDEX TABLE LOAD SYMBOL FUNCTION TYPE ignored;eexists;split.
  - gateway_bound_source_call CLOSED
      ltac:(fun _=>eapply gateway_field_name_read;[exact INDEX|exact TABLE|eapply LOAD;eassumption])ltac:(fun _=>reflexivity).
    eapply gateway_source_same with(target:=Callstate definition[Vptr data data_offset;Vptr name Ptrofs.zero]
      (gateway_field_lookup_cont _)before).
    + exact CLOSED.
    + cbn;tauto.
    + intros;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
      * reflexivity.
      * apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
      * apply cons_argument_values with(v:=Vptr data data_offset).
        -- gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
        -- reflexivity.
        -- apply cons_argument_values with(v:=Vptr name Ptrofs.zero).
          ++ gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
          ++ reflexivity.
          ++ apply no_argument_values.
      * change(Genv.find_funct_ptr ge symbol=Some definition);exact FUNCTION.
      * exact TYPE.
    + apply gateway_source_reached;auto.
  - repeat split;repeat rewrite PTree.gso by discriminate;first[reflexivity|apply PTree.gss].
Qed.
