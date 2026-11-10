(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Float construction and its text release use the actual
   number-helper continuations, retaining allocation failures and arbitrary callbacks. *)
From Stdlib Require Import List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayNumberConstruction GatewayJsonNumberSource
  GatewaySourcePaths GatewaySourceBoundCalls GatewaySourceSegmentAutomation GatewayUnaryExpressions GatewayFailurePaths
  GatewayFramedRuntime GatewayRuntimeCuts GatewayReturnIdentity GatewayReturns GatewayTempNull GatewaySourceCuts GatewayObjects
  GatewayObjectAddresses GatewayValueReturns.
Import ListNotations.

Definition gateway_number_float_group:=json_number_first(json_number_rest gateway_number_after_decode).
Definition gateway_number_float_assign:=json_number_rest gateway_number_float_group.
Definition gateway_number_after_float:=json_number_rest(json_number_rest gateway_number_after_decode).
Definition gateway_number_float_cont parameters:=Kcall(Some _t'14)f_host_json_number empty_env parameters
  (Kseq gateway_number_float_assign(Kseq gateway_number_after_float(Kseq json_number_integer_construction Kstop))).
Definition gateway_number_text_release:=json_number_first gateway_number_after_float.
Definition gateway_number_float_return:=json_number_rest gateway_number_after_float.
Definition gateway_number_text_release_cont parameters:=Kcall None f_host_json_number empty_env parameters
  (Kseq gateway_number_float_return(Kseq json_number_integer_construction Kstop)).

Lemma gateway_number_float_pointer_return:gateway_pointer_return f_host_json_number.
Proof. repeat eexists;reflexivity. Qed.

Theorem gateway_number_null_text_denied {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    parameters memory:
  gateway_failure_result backend ge(Returnstate Vnullptr(gateway_number_decode_cont parameters)memory).
Proof.
  assert(CLOSED:gateway_ambient_closed backend(fun _ _=>True))by(unfold gateway_ambient_closed;intros;exact I).
  assert(FAILURE:gateway_failure_when backend ge(fun _ _=>True)
    (Returnstate Vnullptr(gateway_number_decode_cont parameters)memory)).
  { gateway_bound_source_failure CLOSED
      ltac:(fun _=>eapply gateway_unary_expression_value with(value:=Vnullptr)(result:=Vint Int.one);
        [gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|reflexivity])
      ltac:(fun _=>reflexivity)gateway_number_float_pointer_return. }
  intros before world events value after next RUN;exact(FAILURE before world events value after next I RUN).
Qed.

Theorem gateway_number_float_source_path {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)parameters text text_offset memory symbol definition:
  gateway_ambient_closed backend property->
  (forall memory world,property memory world->Mem.weak_valid_pointer memory text(Ptrofs.unsigned text_offset)=true)->
  Genv.find_symbol ge _PyFloat_FromString=Some symbol->Genv.find_funct_ptr ge symbol=Some definition->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr)](tptr(Tstruct __object noattr))cc_default->
  exists called_parameters,
    gateway_source_path backend ge definition[Vptr text text_offset](gateway_number_float_cont called_parameters)property
      (Returnstate(Vptr text text_offset)(gateway_number_decode_cont parameters)memory)property /\
    called_parameters!_text=Some(Vptr text text_offset) /\
    (forall identifier,identifier<>_text->identifier<>_t'13->called_parameters!identifier=parameters!identifier).
Proof.
  intros CLOSED POINTER SYMBOL FUNCTION TYPE;eexists;split.
  - gateway_bound_source_call CLOSED
      ltac:(fun _=>eapply gateway_unary_expression_value with(value:=Vptr text text_offset)(result:=Vint Int.zero);
        [gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|
         match goal with GOOD:property ?current ?world|-_=>
           change(option_map(fun flag=>Val.of_bool(negb flag))
             (if Mem.weak_valid_pointer current text(Ptrofs.unsigned text_offset)then Some true else None)=Some(Vint Int.zero));
           rewrite(POINTER current world GOOD);reflexivity end])ltac:(fun _=>reflexivity).
    eapply gateway_source_same with(target:=Callstate definition[Vptr text text_offset](gateway_number_float_cont _)memory).
    + exact CLOSED.
    + cbn;tauto.
    + intros;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
      * reflexivity.
      * apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
      * apply cons_argument_values with(v:=Vptr text text_offset).
        -- gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
        -- reflexivity.
        -- apply no_argument_values.
      * exact FUNCTION.
      * exact TYPE.
    + apply gateway_source_reached;auto.
  - split;[apply PTree.gss|]. intros identifier A B;unfold set_opttemp;repeat rewrite PTree.gso by congruence;reflexivity.
Qed.

Theorem gateway_number_text_release_source_path {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)parameters text returned memory symbol definition:
  gateway_ambient_closed backend property->parameters!_text=Some text->
  gateway_object_pointer_value text->
  Genv.find_symbol ge _Py_DecRef=Some symbol->Genv.find_funct_ptr ge symbol=Some definition->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr)]tvoid cc_default->
  exists called_parameters,
    gateway_source_path backend ge definition[text](gateway_number_text_release_cont called_parameters)property
      (Returnstate returned(gateway_number_float_cont parameters)memory)property /\
    called_parameters!_value=Some returned /\
    (forall identifier,identifier<>_value->identifier<>_t'14->called_parameters!identifier=parameters!identifier).
Proof.
  intros CLOSED TEXT POINTER SYMBOL FUNCTION TYPE;eexists;split.
  - gateway_bound_source_call CLOSED ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
    eapply gateway_source_same with(target:=Callstate definition[text](gateway_number_text_release_cont _)memory).
    + exact CLOSED.
    + cbn;tauto.
    + intros;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
      * reflexivity.
      * apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
      * apply cons_argument_values with(v:=text).
        -- apply old_expression_value,value_temp;unfold set_opttemp;
             repeat rewrite PTree.gso by discriminate;exact TEXT.
        -- destruct POINTER as[NULL|[object[offset SAME]]];subst text;reflexivity.
        -- apply no_argument_values.
      * exact FUNCTION.
      * exact TYPE.
    + apply gateway_source_reached;auto.
  - split;[apply PTree.gss|]. intros identifier A B;unfold set_opttemp;repeat rewrite PTree.gso by congruence;reflexivity.
Qed.

Theorem gateway_number_float_return_identity {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    parameters selected ignored before world events value after next:
  parameters!_value=Some selected->
  gateway_steps backend ge(gateway_live(Returnstate ignored(gateway_number_text_release_cont parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value=selected.
Proof.
  intros SELECTED RUN.
  assert(CLOSED:gateway_ambient_closed backend(fun _ _=>True))by(unfold gateway_ambient_closed;intros;exact I).
  destruct(gateway_uniform_edge_side_cut backend ge _ CLOSED
    (Returnstate ignored(gateway_number_text_release_cont parameters)before)
    (State f_host_json_number Sskip(Kseq gateway_number_float_return(Kseq json_number_integer_construction Kstop))empty_env parameters before)
    before world events value after next ltac:(cbn;tauto)ltac:(intros;apply unchanged_store_edge,edge_returnstate)I RUN)
    as(prefix &rest &middle &current &EVENTS &QUIET &PREFIX &READY &REST).
  destruct(gateway_uniform_edge_side_cut backend ge _ CLOSED
    (State f_host_json_number Sskip(Kseq gateway_number_float_return(Kseq json_number_integer_construction Kstop))empty_env parameters middle)
    (State f_host_json_number gateway_number_float_return(Kseq json_number_integer_construction Kstop)empty_env parameters middle)
    middle current rest value after next ltac:(cbn;tauto)ltac:(intros;apply unchanged_store_edge,edge_skip_seq)I REST)
    as(pending &suffix &return_memory &return_world &REST_EVENTS &WAITING &TO_RETURN &RETURN_READY &FROM_RETURN).
  eapply(gateway_return_expression_identity backend ge f_host_json_number(Etempvar _value(tptr(Tstruct __object noattr)))
    (Kseq json_number_integer_construction Kstop)empty_env parameters return_memory return_world selected suffix value after next);
    [reflexivity| | |exact FROM_RETURN].
  - intros;apply old_expression_value,value_temp;exact SELECTED.
  - intros memory converted CAST;eapply gateway_pointer_cast_identity;
      [eexists;reflexivity|eexists;reflexivity|exact CAST].
Qed.
