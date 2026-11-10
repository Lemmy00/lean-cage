(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The Path callback receives the one object loaded by the real tuple helper. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayNoLocalEntry GatewayFunctionEntry GatewaySourcePaths GatewaySourceSegments
  GatewaySourceBoundCalls GatewaySourceCuts GatewaySourceSegmentAutomation GatewayFramedRuntime GatewayUnaryExpressions GatewayFailurePaths
  GatewayReturnIdentity GatewayPure GatewayReturns GatewayValueReturns GatewayPresentationRuntime.
Import ListNotations.
Open Scope Z_scope.

Fixpoint gateway_presentation_suffix(n:nat)(body:statement):statement:=
  match n,body with S rest,Ssequence _ second=>gateway_presentation_suffix rest second|_,_=>body end.
Definition gateway_presentation_after_new:=gateway_presentation_suffix 2(fn_body f_host_call_objects).
Definition gateway_presentation_loop_init:=match gateway_presentation_suffix 3(fn_body f_host_call_objects)with
  Ssequence first _=>first|_=>Sskip end.
Definition gateway_presentation_loop:=match gateway_presentation_loop_init with Ssequence _ loop=>loop|_=>Sskip end.
Definition gateway_presentation_loop_body:=match gateway_presentation_loop with Sloop body _=>body|_=>Sskip end.
Definition gateway_presentation_loop_increment:=match gateway_presentation_loop with Sloop _ increment=>increment|_=>Sskip end.
Definition gateway_presentation_after_loop:=gateway_presentation_suffix 4(fn_body f_host_call_objects).
Definition gateway_presentation_loop_cont:=Kloop1 gateway_presentation_loop_body gateway_presentation_loop_increment
  (Kseq gateway_presentation_after_loop Kstop).
Definition gateway_presentation_after_incref:=match gateway_presentation_loop_body with
  Ssequence _ (Ssequence _ rest)=>rest|_=>Sskip end.
Definition gateway_presentation_set_guard:=match gateway_presentation_after_incref with Ssequence _ guard=>guard|_=>Sskip end.
Definition gateway_presentation_after_call:=gateway_presentation_suffix 5(fn_body f_host_call_objects).
Definition gateway_presentation_return:=Sreturn(Some(Etempvar _result(tptr(Tstruct __object noattr)))).
Definition gateway_presentation_new_cont parameters:=Kcall(Some _t'1)f_host_call_objects empty_env parameters
  (Kseq(Sset _arguments(Etempvar _t'1(tptr(Tstruct __object noattr))))(Kseq gateway_presentation_after_new Kstop)).
Definition gateway_presentation_incref_cont parameters:=Kcall None f_host_call_objects empty_env parameters
  (Kseq gateway_presentation_after_incref gateway_presentation_loop_cont).
Definition gateway_presentation_set_cont parameters:=Kcall(Some _t'2)f_host_call_objects empty_env parameters
  (Kseq gateway_presentation_set_guard gateway_presentation_loop_cont).
Definition gateway_presentation_call_cont parameters:=Kcall(Some _t'3)f_host_call_objects empty_env parameters
  (Kseq(Sset _result(Etempvar _t'3(tptr(Tstruct __object noattr))))(Kseq gateway_presentation_after_call Kstop)).
Definition gateway_presentation_release_cont parameters:=Kcall None f_host_call_objects empty_env parameters
  (Kseq gateway_presentation_return Kstop).

Ltac gateway_presentation_source_call closed loads reduce:=
  lazymatch goal with
  | |-gateway_source_path _ _ _ _ _ _ (Returnstate ?value ?saved ?memory)_=>
    let call:=eval hnf in saved in lazymatch call with
    |Kcall ?destination ?function ?environment ?parameters ?continuation=>
      eapply gateway_source_same with(target:=State function Sskip continuation environment(set_opttemp destination value parameters)memory);
        [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_returnstate|gateway_presentation_source_call closed loads reduce]
    end
  | |-gateway_source_path _ _ _ _ _ _ (State ?function ?body ?continuation ?environment ?parameters ?memory)_=>
    let statement:=eval hnf in body in lazymatch statement with
    |(if ?flag then ?yes else ?no)=>let selected:=eval vm_compute in flag in lazymatch selected with
      |true=>change body with yes;gateway_presentation_source_call closed loads reduce
      |false=>change body with no;gateway_presentation_source_call closed loads reduce end
    |Ssequence ?first ?rest=>eapply gateway_source_same with(target:=State function first(Kseq rest continuation)environment parameters memory);
      [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|gateway_presentation_source_call closed loads reduce]
    |Sloop ?first ?increment=>eapply gateway_source_same with(target:=State function first(Kloop1 first increment continuation)environment parameters memory);
      [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_loop|gateway_presentation_source_call closed loads reduce]
    |Sskip=>let next:=eval hnf in continuation in lazymatch next with
      |Kseq ?following ?rest=>eapply gateway_source_same with(target:=State function following rest environment parameters memory);
        [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|gateway_presentation_source_call closed loads reduce]
      |Kloop1 ?first ?increment ?rest=>eapply gateway_source_same with(target:=State function increment(Kloop2 first increment rest)environment parameters memory);
        [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_loop1|gateway_presentation_source_call closed loads reduce]
      |Kloop2 ?first ?increment ?rest=>eapply gateway_source_same with(target:=State function(Sloop first increment)rest environment parameters memory);
        [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_loop2|gateway_presentation_source_call closed loads reduce]
      end
    |Sbreak=>let next:=eval hnf in continuation in lazymatch next with
      |Kseq _ ?rest=>eapply gateway_source_same with(target:=State function Sbreak rest environment parameters memory);
        [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_break_seq|gateway_presentation_source_call closed loads reduce]
      |Kloop1 _ _ ?rest=>eapply gateway_source_same with(target:=State function Sskip rest environment parameters memory);
        [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_break_loop1|gateway_presentation_source_call closed loads reduce]
      end
    |Sset ?identifier ?expression=>let result:=open_constr:(_ : Values.val)in
      eapply gateway_source_same with(target:=State function Sskip continuation environment(PTree.set identifier result parameters)memory);
        [exact closed|cbn;tauto|intros;apply certified_set_edge;gateway_segment_expression loads reduce|gateway_presentation_source_call closed loads reduce]
    |Sifthenelse ?expression ?yes ?no=>let flag:=open_constr:(_ : bool)in
      eapply gateway_source_same with(target:=State function(if flag then yes else no)continuation environment parameters memory);
        [exact closed|cbn;tauto|intros;eapply certified_if_edge;[gateway_segment_expression loads reduce|reduce()]|
         gateway_presentation_source_call closed loads reduce]
    |Scall _ _ _=>idtac end end.

Theorem gateway_presentation_new_source {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)parameters before symbol definition:
  gateway_ambient_closed backend property->parameters!_count=Some(Vint Int.one)->
  Genv.find_symbol ge _PyTuple_New=Some symbol->Genv.find_funct_ptr ge symbol=Some definition->
  type_of_fundef definition=Tfunction[tlong](tptr(Tstruct __object noattr))cc_default->
  gateway_source_path backend ge definition[Vlong Int64.one](gateway_presentation_new_cont parameters)property
    (State f_host_call_objects(fn_body f_host_call_objects)Kstop empty_env parameters before)property.
Proof.
  intros CLOSED COUNT SYMBOL FUNCTION TYPE.
  gateway_presentation_source_call CLOSED ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
  eapply gateway_source_same with(target:=Callstate definition[Vlong Int64.one](gateway_presentation_new_cont parameters)before).
  - exact CLOSED.
  - cbn;tauto.
  - intros;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
    + reflexivity.
    + apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
    + apply cons_argument_values with(v:=Vint Int.one);
        [apply old_expression_value,value_temp;exact COUNT|reflexivity|apply no_argument_values].
    + change(Genv.find_funct_ptr ge symbol=Some definition);exact FUNCTION.
    + exact TYPE.
  - apply gateway_source_reached;auto.
Qed.

Lemma gateway_presentation_zero_element ge parameters memory array offset object:
  parameters!_values=Some(Vptr array offset)->parameters!_index=Some(Vint Int.zero)->
  Ptrofs.unsigned offset+8<=Ptrofs.modulus->
  Mem.load Mptr memory array(Ptrofs.unsigned offset)=Some object->
  expression_value ge empty_env parameters memory
    (Ederef(Ebinop Oadd(Etempvar _values(tptr(tptr(Tstruct __object noattr))))
      (Etempvar _index tuint)(tptr(tptr(Tstruct __object noattr))))(tptr(Tstruct __object noattr)))object.
Proof.
  intros ARRAY INDEX NOWRAP LOAD;eapply location_read_value with(b:=array)(ofs:=offset).
  - apply pointer_location_value,old_expression_value;eapply value_binary.
    + apply value_temp;exact ARRAY.
    + apply value_temp;exact INDEX.
    + change(Some(Vptr array(Ptrofs.add offset Ptrofs.zero))=Some(Vptr array offset));rewrite Ptrofs.add_zero;reflexivity.
  - eapply deref_loc_value;[reflexivity|]. unfold Mem.loadv;rewrite zle_true by exact NOWRAP;exact LOAD.
Qed.

Theorem gateway_presentation_incref_source {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)parameters array offset tuple tuple_offset child child_offset before symbol definition:
  gateway_ambient_closed backend property->parameters!_count=Some(Vint Int.one)->
  parameters!_values=Some(Vptr array offset)->Ptrofs.unsigned offset+8<=Ptrofs.modulus->
  (forall memory current,property memory current->Mem.weak_valid_pointer memory tuple(Ptrofs.unsigned tuple_offset)=true)->
  (forall memory current,property memory current->Mem.load Mptr memory array(Ptrofs.unsigned offset)=Some(Vptr child child_offset))->
  Genv.find_symbol ge _Py_IncRef=Some symbol->Genv.find_funct_ptr ge symbol=Some definition->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr)]tvoid cc_default->
  exists selected,
    gateway_source_path backend ge definition[Vptr child child_offset](gateway_presentation_incref_cont selected)property
      (Returnstate(Vptr tuple tuple_offset)(gateway_presentation_new_cont parameters)before)property /\
    selected!_arguments=Some(Vptr tuple tuple_offset) /\selected!_values=parameters!_values /\
    selected!_count=parameters!_count /\selected!_index=Some(Vint Int.zero) /\selected!_callable=parameters!_callable.
Proof.
  intros CLOSED COUNT ARRAY NOWRAP POINTER LOAD SYMBOL FUNCTION TYPE;eexists;split.
  - gateway_presentation_source_call CLOSED
      ltac:(fun _=>first[
        eapply gateway_unary_expression_value with(value:=Vptr tuple tuple_offset)(result:=Vint Int.zero);
          [gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|
           match goal with GOOD:property ?memory ?current|-_=>
             change(option_map(fun flag=>Val.of_bool(negb flag))
               (if Mem.weak_valid_pointer memory tuple(Ptrofs.unsigned tuple_offset)then Some true else None)=Some(Vint Int.zero));
             rewrite(POINTER memory current GOOD);reflexivity end]|
        eapply gateway_presentation_zero_element;
          [unfold set_opttemp;repeat rewrite PTree.gso by discriminate;exact ARRAY|
           unfold set_opttemp;repeat rewrite PTree.gso by discriminate;apply PTree.gss|exact NOWRAP|
           match goal with GOOD:property ?memory ?current|-_=>exact(LOAD memory current GOOD)end]])
      ltac:(fun _=>reflexivity).
    eapply gateway_source_same with(target:=Callstate definition[Vptr child child_offset]
      (gateway_presentation_incref_cont _)before).
    + exact CLOSED.
    + cbn;tauto.
    + intros;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
      * reflexivity.
      * apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
      * apply cons_argument_values with(v:=Vptr child child_offset);
          [gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|reflexivity|apply no_argument_values].
      * change(Genv.find_funct_ptr ge symbol=Some definition);exact FUNCTION.
      * exact TYPE.
    + apply gateway_source_reached;auto.
  - unfold set_opttemp;repeat split;repeat rewrite PTree.gso by discriminate;first[apply PTree.gss|reflexivity].
Qed.

Theorem gateway_presentation_set_source {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)parameters array offset tuple tuple_offset child child_offset ignored before symbol definition:
  gateway_ambient_closed backend property->parameters!_index=Some(Vint Int.zero)->
  parameters!_values=Some(Vptr array offset)->parameters!_arguments=Some(Vptr tuple tuple_offset)->
  Ptrofs.unsigned offset+8<=Ptrofs.modulus->
  (forall memory current,property memory current->Mem.load Mptr memory array(Ptrofs.unsigned offset)=Some(Vptr child child_offset))->
  Genv.find_symbol ge _PyTuple_SetItem=Some symbol->Genv.find_funct_ptr ge symbol=Some definition->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr);tlong;tptr(Tstruct __object noattr)]tint cc_default->
  exists selected,
    gateway_source_path backend ge definition[Vptr tuple tuple_offset;Vlong Int64.zero;Vptr child child_offset]
      (gateway_presentation_set_cont selected)property
      (Returnstate ignored(gateway_presentation_incref_cont parameters)before)property /\
    selected!_arguments=parameters!_arguments /\selected!_values=parameters!_values /\
    selected!_count=parameters!_count /\selected!_index=parameters!_index /\selected!_callable=parameters!_callable.
Proof.
  intros CLOSED INDEX ARRAY TUPLE NOWRAP LOAD SYMBOL FUNCTION TYPE;eexists;split.
  - gateway_presentation_source_call CLOSED
      ltac:(fun _=>eapply gateway_presentation_zero_element;
        [unfold set_opttemp;repeat rewrite PTree.gso by discriminate;exact ARRAY|
         unfold set_opttemp;repeat rewrite PTree.gso by discriminate;exact INDEX|exact NOWRAP|
         match goal with GOOD:property ?memory ?current|-_=>exact(LOAD memory current GOOD)end])
      ltac:(fun _=>reflexivity).
    eapply gateway_source_same with(target:=Callstate definition[Vptr tuple tuple_offset;Vlong Int64.zero;Vptr child child_offset]
      (gateway_presentation_set_cont _)before).
    + exact CLOSED.
    + cbn;tauto.
    + intros;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
      * reflexivity.
      * apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
      * apply cons_argument_values with(v:=Vptr tuple tuple_offset).
        -- gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
        -- reflexivity.
        -- apply cons_argument_values with(v:=Vint Int.zero).
           ++ gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
           ++ reflexivity.
           ++ apply cons_argument_values with(v:=Vptr child child_offset);
                [gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|reflexivity|apply no_argument_values].
      * change(Genv.find_funct_ptr ge symbol=Some definition);exact FUNCTION.
      * exact TYPE.
    + apply gateway_source_reached;auto.
  - unfold set_opttemp;repeat split;repeat rewrite PTree.gso by discriminate;reflexivity.
Qed.


Theorem gateway_presentation_call_source {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)parameters tuple tuple_offset callable callable_offset before symbol definition:
  gateway_ambient_closed backend property->parameters!_index=Some(Vint Int.zero)->
  parameters!_count=Some(Vint Int.one)->parameters!_arguments=Some(Vptr tuple tuple_offset)->
  parameters!_callable=Some(Vptr callable callable_offset)->
  Genv.find_symbol ge _PyObject_CallObject=Some symbol->Genv.find_funct_ptr ge symbol=Some definition->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr);tptr(Tstruct __object noattr)]
    (tptr(Tstruct __object noattr))cc_default->
  exists selected,
    gateway_source_path backend ge definition[Vptr callable callable_offset;Vptr tuple tuple_offset]
      (gateway_presentation_call_cont selected)property
      (Returnstate(Vint Int.zero)(gateway_presentation_set_cont parameters)before)property /\
    selected!_arguments=parameters!_arguments /\selected!_values=parameters!_values /\
    selected!_count=parameters!_count /\selected!_index=Some(Vint Int.one) /\selected!_callable=parameters!_callable.
Proof.
  intros CLOSED INDEX COUNT TUPLE CALLABLE SYMBOL FUNCTION TYPE;eexists;split.
  - gateway_presentation_source_call CLOSED ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
    eapply gateway_source_same with(target:=Callstate definition[Vptr callable callable_offset;Vptr tuple tuple_offset]
      (gateway_presentation_call_cont _)before).
    + exact CLOSED.
    + cbn;tauto.
    + intros;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
      * reflexivity.
      * apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
      * apply cons_argument_values with(v:=Vptr callable callable_offset).
        -- gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
        -- reflexivity.
        -- apply cons_argument_values with(v:=Vptr tuple tuple_offset);
             [gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|reflexivity|apply no_argument_values].
      * change(Genv.find_funct_ptr ge symbol=Some definition);exact FUNCTION.
      * exact TYPE.
    + apply gateway_source_reached;auto.
  - unfold set_opttemp;repeat split;repeat rewrite PTree.gso by discriminate;first[apply PTree.gss|reflexivity].
Qed.

Theorem gateway_presentation_release_source {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)parameters tuple tuple_offset returned before symbol definition:
  gateway_ambient_closed backend property->parameters!_arguments=Some(Vptr tuple tuple_offset)->
  Genv.find_symbol ge _Py_DecRef=Some symbol->Genv.find_funct_ptr ge symbol=Some definition->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr)]tvoid cc_default->
  exists selected,
    gateway_source_path backend ge definition[Vptr tuple tuple_offset]
      (gateway_presentation_release_cont selected)property
      (Returnstate returned(gateway_presentation_call_cont parameters)before)property /\
    selected!_arguments=parameters!_arguments /\selected!_result=Some returned /\selected!_callable=parameters!_callable.
Proof.
  intros CLOSED TUPLE SYMBOL FUNCTION TYPE;eexists;split.
  - gateway_presentation_source_call CLOSED ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
    eapply gateway_source_same with(target:=Callstate definition[Vptr tuple tuple_offset]
      (gateway_presentation_release_cont _)before).
    + exact CLOSED.
    + cbn;tauto.
    + intros;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
      * reflexivity.
      * apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
      * apply cons_argument_values with(v:=Vptr tuple tuple_offset);
          [gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|reflexivity|apply no_argument_values].
      * change(Genv.find_funct_ptr ge symbol=Some definition);exact FUNCTION.
      * exact TYPE.
    + apply gateway_source_reached;auto.
  - unfold set_opttemp;repeat split;repeat rewrite PTree.gso by discriminate;first[apply PTree.gss|reflexivity].
Qed.

Theorem gateway_presentation_return_source ge parameters ignored returned before:
  parameters!_result=Some returned->gateway_object_pointer_value returned->
  gateway_constant_path ge returned(Returnstate ignored(gateway_presentation_release_cont parameters)before).
Proof.
  intros RESULT POINTER.
  eapply gateway_constant_next with(next:=State f_host_call_objects Sskip(Kseq gateway_presentation_return Kstop)
    empty_env parameters before).
  - cbn;tauto.
  - intros;apply unchanged_store_edge,edge_returnstate.
  - eapply gateway_constant_next with(next:=State f_host_call_objects gateway_presentation_return Kstop empty_env parameters before).
    + cbn;tauto.
    + intros;apply unchanged_store_edge,edge_skip_seq.
    + eapply gateway_constant_at_return with(value:=returned).
      * reflexivity.
      * intros;apply old_expression_value,value_temp;exact RESULT.
      * intros;destruct POINTER as[NULL|[object[offset PTR]]];subst returned;reflexivity.
Qed.

Theorem gateway_presentation_new_failed {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    parameters before world events value after next:
  gateway_steps backend ge(gateway_live(Returnstate Vnullptr(gateway_presentation_new_cont parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value=Vnullptr.
Proof.
  intro RUN;assert(CLOSED:gateway_ambient_closed backend(fun _ _=>True))by(unfold gateway_ambient_closed;intros;exact I).
  assert(POINTER_RETURN:gateway_pointer_return f_host_call_objects)by(repeat eexists).
  assert(PATH:gateway_failure_when backend ge(fun _ _=>True)
    (Returnstate Vnullptr(gateway_presentation_new_cont parameters)before)).
  { gateway_bound_source_failure CLOSED
      ltac:(fun _=>eapply gateway_unary_expression_value with(value:=Vnullptr)(result:=Vint Int.one);
        [gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|reflexivity])
      ltac:(fun _=>reflexivity)POINTER_RETURN. }
  exact(PATH before world events value after next I RUN).
Qed.


Lemma gateway_presentation_return_pure ge parameters ignored returned before:
  parameters!_result=Some returned->gateway_object_pointer_value returned->
  gateway_pure_path ge(Returnstate ignored(gateway_presentation_release_cont parameters)before)returned.
Proof.
  intros RESULT POINTER.
  eapply gateway_pure_next with(next:=State f_host_call_objects Sskip(Kseq gateway_presentation_return Kstop)
    empty_env parameters before).
  - cbn;tauto.
  - intros;apply unchanged_store_edge,edge_returnstate.
  - eapply gateway_pure_next with(next:=State f_host_call_objects gateway_presentation_return Kstop empty_env parameters before).
    + cbn;tauto.
    + intros;apply unchanged_store_edge,edge_skip_seq.
    + eapply gateway_pure_next with(next:=Returnstate returned Kstop before).
      * cbn;tauto.
      * intros;apply unchanged_store_edge;eapply edge_return.
        -- apply value_temp;exact RESULT.
        -- destruct POINTER as[NULL|[object[offset PTR]]];subst returned;reflexivity.
      * constructor.
Qed.
