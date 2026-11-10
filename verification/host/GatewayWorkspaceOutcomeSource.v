(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The original Workspace returns the constructed instance after its real data release. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayCallPath GatewayReferenceSourceExecution GatewaySourcePaths GatewaySourceSegments
  GatewaySourceBoundCalls GatewaySourceSegmentAutomation GatewayFramedRuntime GatewayPure GatewayReturnIdentity.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_workspace_outcome_return:=Sreturn(Some(Etempvar _outcome(tptr(Tstruct __object noattr)))).
Definition gateway_workspace_data_release:=Scall None
  (Evar _Py_DecRef(Tfunction[tptr(Tstruct __object noattr)]tvoid cc_default))
  [Etempvar _data(tptr(Tstruct __object noattr))].
Definition gateway_workspace_after_outcome:=Ssequence gateway_workspace_data_release gateway_workspace_outcome_return.
Definition gateway_workspace_outcome_cont environment parameters:=Kcall(Some _t'31)f_host_workspace_execute environment parameters
  (Kseq(Sset _outcome(Etempvar _t'31(tptr(Tstruct __object noattr))))(Kseq gateway_workspace_after_outcome Kstop)).
Definition gateway_workspace_data_release_cont environment parameters:=Kcall None f_host_workspace_execute environment parameters
  (Kseq gateway_workspace_outcome_return Kstop).
Definition gateway_workspace_outcome_parameters(parameters:temp_env)(value:Values.val):=PTree.set _outcome value(PTree.set _t'31 value parameters).

Fixpoint gateway_workspace_outcome_suffix body:option statement:=
  match body with
  |Ssequence(Ssequence(Scall _ (Evar callee _)_)_)rest=>
    if Pos.eqb callee _host_outcome_from then Some body else gateway_workspace_outcome_suffix rest
  |Ssequence _ rest=>gateway_workspace_outcome_suffix rest
  |_=>None end.

Theorem gateway_actual_workspace_outcome_tail:
  gateway_workspace_outcome_suffix(fn_body f_host_workspace_execute)=Some(Ssequence
    (Ssequence(Scall(Some _t'31)
      (Evar _host_outcome_from(Tfunction[tptr(Tstruct __object noattr)](tptr(Tstruct __object noattr))cc_default))
      [Etempvar _data(tptr(Tstruct __object noattr))])
      (Sset _outcome(Etempvar _t'31(tptr(Tstruct __object noattr)))))gateway_workspace_after_outcome).
Proof. reflexivity. Qed.

Theorem gateway_workspace_outcome_release_source {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)environment parameters data data_offset outcome before symbol:
  gateway_ambient_closed backend property->parameters!_data=Some(Vptr data data_offset)->
  environment!_Py_DecRef=None->Genv.find_symbol ge _Py_DecRef=Some symbol->
  Genv.find_funct_ptr ge symbol=Some gateway_reference_decref_definition->
  gateway_source_path backend ge gateway_reference_decref_definition[Vptr data data_offset]
    (gateway_workspace_data_release_cont environment(gateway_workspace_outcome_parameters parameters outcome))property
    (Returnstate outcome(gateway_workspace_outcome_cont environment parameters)before)property.
Proof.
  intros CLOSED DATA LOCAL SYMBOL FUNCTION.
  gateway_bound_source_call CLOSED ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
  eapply gateway_source_same with(target:=Callstate gateway_reference_decref_definition[Vptr data data_offset]
    (gateway_workspace_data_release_cont environment(gateway_workspace_outcome_parameters parameters outcome))before).
  - exact CLOSED.
  - cbn;tauto.
  - intros;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
    + reflexivity.
    + apply old_expression_value;eapply value_function;[exact LOCAL|exact SYMBOL|reflexivity].
    + apply cons_argument_values with(v:=Vptr data data_offset).
      * gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
      * reflexivity.
      * apply no_argument_values.
    + change(Genv.find_funct_ptr ge symbol=Some gateway_reference_decref_definition);exact FUNCTION.
    + reflexivity.
  - apply gateway_source_reached;auto.
Qed.

Theorem gateway_actual_workspace_outcome_release_identity {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    environment parameters outcome ignored before world events value after next:
  parameters!_outcome=Some outcome->(outcome=Vnullptr \/exists object offset,outcome=Vptr object offset)->
  gateway_steps backend ge
    (gateway_live(Returnstate ignored(gateway_workspace_data_release_cont environment parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value=outcome.
Proof.
  intros OUTCOME POINTER RUN.
  assert(CLOSED:gateway_ambient_closed backend(fun _ _=>True))by(unfold gateway_ambient_closed;intros;exact I).
  destruct(gateway_source_segment_cut backend ge _
    (Returnstate ignored(gateway_workspace_data_release_cont environment parameters)before)
    (State f_host_workspace_execute gateway_workspace_outcome_return Kstop environment parameters before)(fun _ _=>True)
    ltac:(gateway_segment_dynamic CLOSED ltac:(fun _=>fail)ltac:(fun _=>reflexivity))before world events value after next I RUN)
    as(prefix &suffix &memory &current &EVENTS &QUIET &PREFIX &GOOD &SUFFIX).
  eapply(gateway_return_expression_identity backend ge f_host_workspace_execute
    (Etempvar _outcome(tptr(Tstruct __object noattr)))Kstop environment parameters memory current outcome suffix value after next);
    [reflexivity| | |exact SUFFIX].
  - intros;apply old_expression_value,value_temp;exact OUTCOME.
  - intros changed returned CAST;destruct POINTER as[NULL|[object[offset SAME]]];subst outcome;
      cbn in CAST;inversion CAST;reflexivity.
Qed.

Theorem gateway_workspace_outcome_return_source_cut {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    environment parameters object before world events value after next:
  parameters!_outcome=Some(Vptr object Ptrofs.zero)->
  gateway_steps backend ge
    (gateway_live(State f_host_workspace_execute gateway_workspace_outcome_return Kstop environment parameters before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists prefix suffix memory current freed,
    events=prefix++gateway_source E0::suffix /\Forall(fun event=>event=gateway_ambient)prefix /\
    gateway_steps backend ge
      (gateway_live(State f_host_workspace_execute gateway_workspace_outcome_return Kstop environment parameters before)world)prefix
      (gateway_live(State f_host_workspace_execute gateway_workspace_outcome_return Kstop environment parameters memory)current) /\
    gateway_step backend ge
      (gateway_live(State f_host_workspace_execute gateway_workspace_outcome_return Kstop environment parameters memory)current)
      (gateway_source E0)(gateway_live(Returnstate(Vptr object Ptrofs.zero)Kstop freed)current) /\
    gateway_steps backend ge(gateway_live(Returnstate(Vptr object Ptrofs.zero)Kstop freed)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intro OUTCOME;revert before world;induction events as[|event rest IH];intros before world RUN;[inversion RUN|].
  inversion RUN as[|first observed middle remaining final STEP REST];subst.
  assert(INTERNAL:~gateway_at_primitive(State f_host_workspace_execute gateway_workspace_outcome_return Kstop environment parameters before))
    by(cbn;tauto).
  destruct(gateway_nonprimitive_step backend ge _ _ _ _ INTERNAL STEP)
    as[[trace[target[EVENT[REAL TARGET]]]]|[[changed[current[EVENT[AMBIENT TARGET]]]]|[EVENT TARGET]]];subst.
  - assert(EXPRESSION:expression_value ge environment parameters before(Etempvar _outcome(tptr(Tstruct __object noattr)))(Vptr object Ptrofs.zero)).
    { apply old_expression_value,value_temp;exact OUTCOME. }
    inversion REAL;subst;try match goal with BAD:_=_\/_=_|-_=>destruct BAD;discriminate end.
    match goal with EVAL:eval_expr _ _ _ _ (Etempvar _outcome _) ?pointer|-_=>
      pose proof(proj2 EXPRESSION _ EVAL)as SAME;subst pointer end.
    match goal with CAST:sem_cast _ _ _ _=Some _|-_=>cbn in CAST;inversion CAST;subst end.
    exists[],rest,before,world,m';split;[reflexivity|]. split;[constructor|]. split;[constructor|]. split;[|exact REST].
    apply gateway_internal;[exact I|exact REAL].
  - destruct(IH changed current REST)as(prefix &suffix &memory &owner &freed &EVENTS &PENDING &PREFIX &EDGE &SUFFIX).
    exists(gateway_ambient::prefix),suffix,memory,owner,freed;split;[cbn;congruence|]. split;[constructor;[reflexivity|exact PENDING]|].
    split;[econstructor;[apply gateway_interleaved;exact AMBIENT|exact PREFIX]|]. split;assumption.
  - destruct(gateway_dead_steps _ _ _ _ _ _ REST)as[_ IMPOSSIBLE];discriminate.
Qed.
