(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The original private copy is stored before its checked output lookup. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayOutcomeConstruction GatewaySourceCuts GatewaySourcePaths
  GatewaySourceBoundCalls GatewaySourceSegmentAutomation GatewayUnaryExpressions GatewayFailurePaths GatewayFramedRuntime GatewaySourceSegments.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_outcome_after_copy:=gateway_outcome_right_suffix 9(fn_body f_host_outcome_from).
Definition gateway_outcome_copy_cont environment parameters:=
  Kcall(Some _t'20)f_host_outcome_from environment parameters
    (Kseq(Sset _copy(Etempvar _t'20(tptr(Tstruct __object noattr))))(Kseq gateway_outcome_after_copy Kstop)).
Definition gateway_outcome_copied_parameters (parameters:temp_env) (pointer:Values.val):=
  PTree.set _copy pointer(PTree.set _t'20 pointer parameters).
Definition gateway_outcome_output_assignment:=
  Sassign(Evar _output(tptr(Tstruct __object noattr)))(Etempvar _t'21(tptr(Tstruct __object noattr))).
Definition gateway_outcome_after_output_lookup:=gateway_outcome_right_suffix 11(fn_body f_host_outcome_from).
Definition gateway_outcome_output_lookup_cont environment parameters:=
  Kcall(Some _t'21)f_host_outcome_from environment parameters
    (Kseq gateway_outcome_output_assignment(Kseq gateway_outcome_after_output_lookup Kstop)).

Theorem gateway_actual_outcome_copy_failure {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    environment parameters before world events value after next:
  gateway_steps backend ge(gateway_live(Returnstate Vnullptr(gateway_outcome_copy_cont environment parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value=Vnullptr.
Proof.
  intro RUN.
  assert(CLOSED:gateway_ambient_closed backend(fun _ _=>True))by(unfold gateway_ambient_closed;intros;exact I).
  assert(POINTER_RETURN:gateway_pointer_return f_host_outcome_from)by(repeat eexists).
  assert(PATH:gateway_failure_when backend ge(fun _ _=>True)
    (Returnstate Vnullptr(gateway_outcome_copy_cont environment parameters)before)).
  { gateway_bound_source_failure CLOSED
      ltac:(fun _=>eapply gateway_unary_expression_value with(value:=Vnullptr)(result:=Vint Int.one);
        [gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|reflexivity])
      ltac:(fun _=>reflexivity)POINTER_RETURN. }
  exact(PATH before world events value after next I RUN).
Qed.

Theorem gateway_outcome_copy_store_segment {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)environment parameters copy before:
  gateway_ambient_closed backend property->
  gateway_source_segment backend ge property(Returnstate copy(gateway_outcome_copy_cont environment parameters)before)
    (State f_host_outcome_from Sskip(Kseq gateway_outcome_after_copy Kstop)environment
      (gateway_outcome_copied_parameters parameters copy)before)property.
Proof.
  intro CLOSED;gateway_segment_dynamic CLOSED ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
Qed.

Theorem gateway_outcome_copy_output_source {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)environment parameters copy offset before function definition name:
  gateway_ambient_closed backend property->
  (forall memory current,property memory current->Mem.weak_valid_pointer memory copy(Ptrofs.unsigned offset)=true)->
  environment!_PyDict_GetItemString=None->environment!___stringlit_40=None->
  Genv.find_symbol ge _PyDict_GetItemString=Some function->Genv.find_funct_ptr ge function=Some definition->
  Genv.find_symbol ge ___stringlit_40=Some name->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr);tptr tschar](tptr(Tstruct __object noattr))cc_default->
  exists selected,
    gateway_source_path backend ge definition[Vptr copy offset;Vptr name Ptrofs.zero]
      (gateway_outcome_output_lookup_cont environment selected)property
      (Returnstate(Vptr copy offset)(gateway_outcome_copy_cont environment parameters)before)property /\
    selected!_copy=Some(Vptr copy offset) /\selected!_data=parameters!_data.
Proof.
  intros CLOSED POINTER LOCAL NAME_LOCAL SYMBOL FUNCTION NAME TYPE;eexists;split.
  - gateway_bound_source_call CLOSED
      ltac:(fun _=>eapply gateway_unary_expression_value with(value:=Vptr copy offset)(result:=Vint Int.zero);
        [gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|
         match goal with GOOD:property ?memory ?current|-_=>
           change(option_map(fun flag=>Val.of_bool(negb flag))
             (if Mem.weak_valid_pointer memory copy(Ptrofs.unsigned offset)then Some true else None)=Some(Vint Int.zero));
           rewrite(POINTER memory current GOOD);reflexivity end])ltac:(fun _=>reflexivity).
    eapply gateway_source_same with(target:=Callstate definition[Vptr copy offset;Vptr name Ptrofs.zero]
      (gateway_outcome_output_lookup_cont environment _)before).
    + exact CLOSED.
    + cbn;tauto.
    + intros;eapply certified_call_edge with(vf:=Vptr function Ptrofs.zero).
      * reflexivity.
      * apply old_expression_value;eapply value_function;[exact LOCAL|exact SYMBOL|reflexivity].
      * apply cons_argument_values with(v:=Vptr copy offset).
        -- gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
        -- reflexivity.
        -- apply cons_argument_values with(v:=Vptr name Ptrofs.zero).
           ++ apply old_expression_value;eapply value_function;[exact NAME_LOCAL|exact NAME|reflexivity].
           ++ reflexivity.
           ++ apply no_argument_values.
      * change(Genv.find_funct_ptr ge function=Some definition);exact FUNCTION.
      * exact TYPE.
    + apply gateway_source_reached;auto.
  - unfold set_opttemp;split;[apply PTree.gss|repeat rewrite PTree.gso by discriminate;reflexivity].
Qed.
