(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual Path and insertion failures return NULL before Outcome allocation. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayOutcomeConstruction GatewayOutcomeOutputSource GatewayObjectAddresses
  GatewaySourceSegments GatewaySourcePaths GatewaySourceCuts GatewaySourceBoundCalls GatewaySourceSegmentAutomation GatewayFramedRuntime
  GatewayUnaryExpressions GatewayFailurePaths GatewayContexts GatewayValueReturns.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_outcome_path_insertion:=match gateway_outcome_path_after_call with Ssequence _ rest=>rest|_=>Sskip end.
Definition gateway_outcome_path_after_set:=match gateway_outcome_path_insertion with Ssequence _ rest=>rest|_=>Sskip end.
Definition gateway_outcome_path_failed_guard:=match gateway_outcome_path_after_set with Ssequence _ rest=>rest|_=>Sskip end.
Definition gateway_outcome_path_set_cont environment parameters:=Kcall(Some _t'23)f_host_outcome_from environment parameters
  (Kseq(Sset _failed(Etempvar _t'23 tint))(Kseq gateway_outcome_path_after_set(Kseq gateway_outcome_allocation_tail Kstop))).
Definition gateway_outcome_path_release_cont environment parameters:=Kcall None f_host_outcome_from environment parameters
  (Kseq gateway_outcome_path_failed_guard(Kseq gateway_outcome_allocation_tail Kstop)).

Theorem gateway_actual_outcome_path_null {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    environment parameters before world events value after next:
  gateway_steps backend ge(gateway_live(Returnstate Vnullptr(gateway_outcome_path_cont environment parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value=Vnullptr.
Proof.
  intro RUN;assert(CLOSED:gateway_ambient_closed backend(fun _ _=>True))by(unfold gateway_ambient_closed;intros;exact I).
  assert(POINTER:gateway_pointer_return f_host_outcome_from)by(repeat eexists).
  assert(PATH:gateway_failure_when backend ge(fun _ _=>True)
    (Returnstate Vnullptr(gateway_outcome_path_cont environment parameters)before)).
  { gateway_bound_source_failure CLOSED
      ltac:(fun _=>eapply gateway_unary_expression_value with(value:=Vnullptr)(result:=Vint Int.one);
        [gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|reflexivity])ltac:(fun _=>reflexivity)POINTER. }
  exact(PATH before world events value after next I RUN).
Qed.

Theorem gateway_outcome_path_set_source {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)environment parameters copy copy_offset path path_offset before function definition name:
  gateway_ambient_closed backend property->parameters!_copy=Some(Vptr copy copy_offset)->
  (forall memory current,property memory current->Mem.weak_valid_pointer memory path(Ptrofs.unsigned path_offset)=true)->
  environment!_PyDict_SetItemString=None->environment!___stringlit_40=None->
  Genv.find_symbol ge _PyDict_SetItemString=Some function->Genv.find_funct_ptr ge function=Some definition->
  Genv.find_symbol ge ___stringlit_40=Some name->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr);tptr tschar;tptr(Tstruct __object noattr)]tint cc_default->
  exists selected,
    gateway_source_path backend ge definition[Vptr copy copy_offset;Vptr name Ptrofs.zero;Vptr path path_offset]
      (gateway_outcome_path_set_cont environment selected)property
      (Returnstate(Vptr path path_offset)(gateway_outcome_path_cont environment parameters)before)property /\
    selected!_copy=parameters!_copy /\selected!_path=Some(Vptr path path_offset) /\selected!_data=parameters!_data.
Proof.
  intros CLOSED COPY POINTER LOCAL NAME_LOCAL SYMBOL FUNCTION NAME TYPE;eexists;split.
  - gateway_bound_source_call CLOSED
      ltac:(fun _=>eapply gateway_unary_expression_value with(value:=Vptr path path_offset)(result:=Vint Int.zero);
        [gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|
         match goal with GOOD:property ?memory ?current|-_=>
           change(option_map(fun flag=>Val.of_bool(negb flag))
             (if Mem.weak_valid_pointer memory path(Ptrofs.unsigned path_offset)then Some true else None)=Some(Vint Int.zero));
           rewrite(POINTER memory current GOOD);reflexivity end])ltac:(fun _=>reflexivity).
    eapply gateway_source_same with(target:=Callstate definition[Vptr copy copy_offset;Vptr name Ptrofs.zero;Vptr path path_offset]
      (gateway_outcome_path_set_cont environment _)before).
    + exact CLOSED.
    + cbn;tauto.
    + intros;eapply certified_call_edge with(vf:=Vptr function Ptrofs.zero).
      * reflexivity.
      * apply old_expression_value;eapply value_function;[exact LOCAL|exact SYMBOL|reflexivity].
      * apply cons_argument_values with(v:=Vptr copy copy_offset).
        -- gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
        -- reflexivity.
        -- apply cons_argument_values with(v:=Vptr name Ptrofs.zero).
           ++ apply old_expression_value;eapply value_function;[exact NAME_LOCAL|exact NAME|reflexivity].
           ++ reflexivity.
           ++ apply cons_argument_values with(v:=Vptr path path_offset);
                [gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|reflexivity|apply no_argument_values].
      * change(Genv.find_funct_ptr ge function=Some definition);exact FUNCTION.
      * exact TYPE.
    + apply gateway_source_reached;auto.
  - unfold set_opttemp;repeat split;repeat rewrite PTree.gso by discriminate;first[reflexivity|apply PTree.gss].
Qed.

Theorem gateway_outcome_path_release_source {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)environment parameters path path_offset status before function definition:
  gateway_ambient_closed backend property->parameters!_path=Some(Vptr path path_offset)->
  environment!_Py_DecRef=None->Genv.find_symbol ge _Py_DecRef=Some function->Genv.find_funct_ptr ge function=Some definition->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr)]tvoid cc_default->
  exists selected,
    gateway_source_path backend ge definition[Vptr path path_offset](gateway_outcome_path_release_cont environment selected)property
      (Returnstate(Vint status)(gateway_outcome_path_set_cont environment parameters)before)property /\
    selected!_copy=parameters!_copy /\selected!_path=parameters!_path /\selected!_failed=Some(Vint status) /\selected!_data=parameters!_data.
Proof.
  intros CLOSED PATH LOCAL SYMBOL FUNCTION TYPE;eexists;split.
  - gateway_bound_source_call CLOSED ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
    eapply gateway_source_same with(target:=Callstate definition[Vptr path path_offset]
      (gateway_outcome_path_release_cont environment _)before).
    + exact CLOSED.
    + cbn;tauto.
    + intros;eapply certified_call_edge with(vf:=Vptr function Ptrofs.zero).
      * reflexivity.
      * apply old_expression_value;eapply value_function;[exact LOCAL|exact SYMBOL|reflexivity].
      * apply cons_argument_values with(v:=Vptr path path_offset);
          [gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|reflexivity|apply no_argument_values].
      * change(Genv.find_funct_ptr ge function=Some definition);exact FUNCTION.
      * exact TYPE.
    + apply gateway_source_reached;auto.
  - unfold set_opttemp;repeat split;repeat rewrite PTree.gso by discriminate;first[reflexivity|apply PTree.gss].
Qed.

Theorem gateway_outcome_path_failed {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    environment parameters status ignored before world events value after next:
  parameters!_failed=Some(Vint status)->status<>Int.zero->
  gateway_steps backend ge(gateway_live(Returnstate ignored(gateway_outcome_path_release_cont environment parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value=Vnullptr.
Proof.
  intros FAILED NONZERO RUN;assert(CLOSED:gateway_ambient_closed backend(fun _ _=>True))by(unfold gateway_ambient_closed;intros;exact I).
  assert(POINTER:gateway_pointer_return f_host_outcome_from)by(repeat eexists).
  assert(PATH:gateway_failure_when backend ge(fun _ _=>True)
    (Returnstate ignored(gateway_outcome_path_release_cont environment parameters)before)).
  { gateway_bound_source_failure CLOSED ltac:(fun _=>fail)
      ltac:(fun _=>lazymatch goal with
        | |- _ = @Some bool ?branch=>unify branch true;
          change(Some(negb(Int.eq status Int.zero))=Some true);
          rewrite Int.eq_false by exact NONZERO;reflexivity
        | |- _=>reflexivity end)POINTER. }
  exact(PATH before world events value after next I RUN).
Qed.

Theorem gateway_outcome_path_installed_segment {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)environment parameters ignored before:
  gateway_ambient_closed backend property->parameters!_failed=Some(Vint Int.zero)->
  gateway_source_segment backend ge property
    (Returnstate ignored(gateway_outcome_path_release_cont environment parameters)before)
    (State f_host_outcome_from gateway_outcome_allocation_tail Kstop environment parameters before)property.
Proof.
  intros CLOSED ZERO;gateway_segment_dynamic CLOSED ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
Qed.
