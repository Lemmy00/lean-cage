(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Every nonzero append status takes the actual cleanup/null-return branch. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayValueEntry GatewayValueGuards
  GatewayContainerLoopSource GatewayContainerArraySource GatewaySourceDynamic GatewaySourcePaths GatewaySourceCuts
  GatewayFailurePaths GatewayFramedRuntime.
Import ListNotations.

Definition gateway_container_append_guard:=match gateway_container_after_append with Ssequence _ rest=>rest|_=>Sskip end.
Definition gateway_container_array_release_cont slots parameters:=Kcall None f_host_value(gateway_value_environment slots)parameters
  (Kseq gateway_container_append_guard(Kloop1 gateway_container_loop_body gateway_container_loop_increment gateway_container_loop_cont)).

Lemma gateway_container_append_release_path {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    slots parameters status child child_offset memory symbol definition:
  parameters!_first=Some(Vptr child child_offset) ->
  Genv.find_symbol ge _Py_DecRef=Some symbol ->Genv.find_funct_ptr ge symbol=Some definition ->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr)]tvoid cc_default ->
  exists called_parameters,gateway_source_path backend ge definition[Vptr child child_offset]
    (gateway_container_array_release_cont slots called_parameters)(fun _ _=>True)
    (Returnstate(Vint status)(gateway_container_append_cont slots parameters)memory)(fun _ _=>True) /\
    called_parameters!_result=Some(Vint status).
Proof.
  intros CHILD SYMBOL FUNCTION TYPE.
  assert(CLOSED:gateway_ambient_closed backend(fun _ _=>True))by(unfold gateway_ambient_closed;intros;exact I).
  eexists;split.
  - gateway_source_dynamic_call CLOSED ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
    eapply gateway_source_same with(target:=Callstate definition[Vptr child child_offset]
      (gateway_container_array_release_cont slots _)memory).
    + exact CLOSED.
    + cbn;tauto.
    + intros;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
      * reflexivity.
      * apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
      * apply cons_argument_values with(v:=Vptr child child_offset).
        -- gateway_source_dynamic_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
        -- reflexivity.
        -- apply no_argument_values.
      * change(Genv.find_funct_ptr ge symbol=Some definition);exact FUNCTION.
      * exact TYPE.
    + apply gateway_source_reached;auto.
  - unfold set_opttemp;apply PTree.gss.
Qed.

Theorem gateway_actual_nonzero_append_failure {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    slots parameters status child child_offset before world events value after next symbol definition:
  status<>Int.zero ->parameters!_first=Some(Vptr child child_offset) ->
  Genv.find_symbol ge _Py_DecRef=Some symbol ->Genv.find_funct_ptr ge symbol=Some definition ->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr)]tvoid cc_default ->
  gateway_steps backend ge(gateway_live(Returnstate(Vint status)(gateway_container_append_cont slots parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value=Vnullptr.
Proof.
  intros NONZERO CHILD SYMBOL FUNCTION TYPE RUN.
  destruct(gateway_container_append_release_path backend ge slots parameters status child child_offset before symbol definition CHILD SYMBOL FUNCTION TYPE)
    as(called_parameters &PATH &CALLED_STATUS).
  destruct(gateway_source_path_cut backend ge _ _ _ _ _ _ PATH before world events value after next I RUN)
    as(prefix &rest &release_before &release_world &EVENTS &QUIET &PREFIX &READY &FROM_RELEASE).
  destruct(gateway_return_cut backend ge definition[Vptr child child_offset](gateway_container_array_release_cont slots called_parameters)
    release_before release_world rest(Returnstate value Kstop after)next ltac:(cbn;exact I)ltac:(cbn;lia)FROM_RELEASE)
    as(releasing &suffix &released &release_after &release_next &REST_EVENTS &RELEASE_RUN &REST).
  assert(CLOSED:gateway_ambient_closed backend(fun _ _=>True))by(unfold gateway_ambient_closed;intros;exact I).
  assert(FAILED:gateway_failure_when backend ge(fun _ _=>True)
    (Returnstate released(gateway_container_array_release_cont slots called_parameters)release_after)).
  { eapply gateway_failure_when_same with(target:=State f_host_value Sskip
      (Kseq gateway_container_append_guard(Kloop1 gateway_container_loop_body gateway_container_loop_increment gateway_container_loop_cont))
      (gateway_value_environment slots)called_parameters release_after);
      [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_returnstate|].
    eapply gateway_failure_when_same with(target:=State f_host_value gateway_container_append_guard
      (Kloop1 gateway_container_loop_body gateway_container_loop_increment gateway_container_loop_cont)
      (gateway_value_environment slots)called_parameters release_after);
      [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
    eapply gateway_failure_when_same with(target:=State f_host_value
      (match gateway_container_append_guard with Sifthenelse _ failed _=>failed|_=>Sskip end)
      (Kloop1 gateway_container_loop_body gateway_container_loop_increment gateway_container_loop_cont)
      (gateway_value_environment slots)called_parameters release_after).
    - exact CLOSED.
    - cbn;tauto.
    - intros;eapply certified_if_edge with(b:=true).
      + apply old_expression_value,value_temp;exact CALLED_STATUS.
      + change(Some(negb(Int.eq status Int.zero))=Some true);rewrite Int.eq_false by exact NONZERO;reflexivity.
    - apply gateway_failure_when_selected,gateway_failure_selected;
        [exact gateway_value_pointer_return|vm_compute;auto|reflexivity]. }
  exact(FAILED release_after release_next suffix value after next I REST).
Qed.

Theorem gateway_successful_append_status_zero {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    slots parameters status child child_offset before world events value after next symbol definition:
  parameters!_first=Some(Vptr child child_offset) ->
  Genv.find_symbol ge _Py_DecRef=Some symbol ->Genv.find_funct_ptr ge symbol=Some definition ->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr)]tvoid cc_default ->
  gateway_steps backend ge(gateway_live(Returnstate(Vint status)(gateway_container_append_cont slots parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value<>Vnullptr ->status=Int.zero.
Proof.
  intros CHILD SYMBOL FUNCTION TYPE RUN NONNULL;destruct(Int.eq_dec status Int.zero);[assumption|].
  exfalso;apply NONNULL;eapply gateway_actual_nonzero_append_failure;eassumption.
Qed.
