(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The original Outcome call supplies its real validation locals and first type check. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayCalls GatewayFunctionEntry GatewayStackAllocation
  GatewayThreadRuntime GatewayLocalRuntime GatewayStreamInterface GatewayFramedRuntime GatewayContexts
  GatewayOutcomeConstruction GatewaySourcePaths GatewaySourceCuts GatewaySourceBoundCalls GatewaySourceSegmentAutomation GatewayObjectAddresses GatewayValueReturns.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_outcome_parameters data:=PTree.set _data data(create_undef_temps(fn_temps f_host_outcome_from)).

Lemma gateway_outcome_entry_canonical ge data before environment parameters allocated:
  function_entry2 ge f_host_outcome_from[data]before environment parameters allocated->
  parameters=gateway_outcome_parameters data /\
    alloc_variables ge empty_env before(fn_vars f_host_outcome_from)environment allocated.
Proof.
  intro ENTRY;inversion ENTRY;subst.
  match goal with BIND:bind_parameter_temps _ _ _=Some _|-_=>
    change(Some(gateway_outcome_parameters data)=Some parameters)in BIND;inversion BIND;subst parameters end.
  split;[reflexivity|assumption].
Qed.

Lemma gateway_outcome_variables_unique:list_norepet(map fst(fn_vars f_host_outcome_from)).
Proof. repeat(apply list_norepet_cons;[cbn;intuition discriminate|]);apply list_norepet_nil. Qed.

Definition gateway_outcome_stack_buffers ge before environment after:Prop:=
  (forall identifier ty,In(identifier,ty)(fn_vars f_host_outcome_from)->
    exists object,environment!identifier=Some(object,ty) /\~Mem.valid_block before object /\
      Mem.range_perm after object 0(sizeof ge ty)Cur Freeable) /\
  gateway_stack_environment after environment /\Mem.unchanged_on(fun _ _=>True)before after /\
  (forall identifier,~In identifier(map fst(fn_vars f_host_outcome_from))->environment!identifier=None).

Lemma gateway_actual_outcome_allocations ge before environment after:
  alloc_variables ge empty_env before(fn_vars f_host_outcome_from)environment after->
  gateway_outcome_stack_buffers ge before environment after.
Proof.
  intro ALLOC;split.
  - intros identifier ty MEMBER;eapply gateway_alloc_variables_member;
      [exact ALLOC|exact gateway_outcome_variables_unique|exact MEMBER].
  - split;[eapply gateway_alloc_variables_stack;[exact ALLOC|apply gateway_empty_stack_environment]|].
    split;[eapply gateway_alloc_variables_frame;exact ALLOC|].
    intros identifier ABSENT;rewrite(gateway_alloc_variables_lookup ge _ _ _ _ _ identifier ALLOC ABSENT);apply PTree.gempty.
Qed.

Theorem gateway_actual_outcome_entry {World Event}(backend:gateway_backend World Event)
    io native stable discipline thread_errno(runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    ge data before world events value after next:
  discipline None before world->
  gateway_steps backend ge(gateway_live(Callstate(Internal f_host_outcome_from)[data]Kstop before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists prefix suffix called current environment allocated,
    events=prefix++gateway_source E0::suffix /\Forall(fun event=>event=gateway_ambient)prefix /\
    gateway_steps backend ge(gateway_live(Callstate(Internal f_host_outcome_from)[data]Kstop before)world)prefix
      (gateway_live(Callstate(Internal f_host_outcome_from)[data]Kstop called)current) /\
    function_entry2 ge f_host_outcome_from[data]called environment(gateway_outcome_parameters data)allocated /\
    gateway_outcome_stack_buffers ge called environment allocated /\discipline None allocated current /\
    gateway_native_environment native current allocated environment /\
    gateway_steps backend ge
      (gateway_live(State f_host_outcome_from(fn_body f_host_outcome_from)Kstop environment(gateway_outcome_parameters data)allocated)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros SIDE RUN.
  destruct(actual_gateway_function_entry_ambient backend ge f_host_outcome_from[data]Kstop before world events value Kstop after next RUN)
    as(prefix &suffix &called &current &environment &parameters &allocated &EVENTS &AMBIENT &PREFIX &ENTRY &REST).
  assert(CALLED:discipline None called current).
  { eapply gateway_ambient_run_ready with(source:=Callstate(Internal f_host_outcome_from)[data]Kstop before);
      [|exact SIDE|exact AMBIENT|exact PREFIX].
    intros initial owner changed target READY INTERFERENCE.
    exact(proj1(gateway_thread_ambient _ _ _ _ _ _ runtime None _ _ _ _ READY INTERFERENCE)). }
  destruct(gateway_outcome_entry_canonical ge data called environment parameters allocated ENTRY)as[PARAMETERS ALLOC];subst parameters.
  destruct(gateway_native_alloc_variables backend io native stable discipline thread_errno runtime ge None empty_env called
    (fn_vars f_host_outcome_from)environment allocated current ALLOC CALLED(gateway_native_environment_empty native current called))
    as[ALLOCATED NATIVE].
  exists prefix,suffix,called,current,environment,allocated.
  split;[exact EVENTS|]. split;[exact AMBIENT|]. split;[exact PREFIX|]. split;[exact ENTRY|].
  split;[apply gateway_actual_outcome_allocations;exact ALLOC|]. split;[exact ALLOCATED|]. split;assumption.
Qed.

Definition gateway_outcome_first_validation_tail:=gateway_outcome_right_suffix 1(fn_body f_host_outcome_from).
Definition gateway_outcome_first_type_cont environment parameters:=
  Kcall(Some _t'1)f_host_outcome_from environment parameters
    (Kseq(Sset _valid(Etempvar _t'1 tint))(Kseq gateway_outcome_first_validation_tail Kstop)).

Theorem gateway_outcome_first_type_source {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)environment parameters data before function dictionary:
  gateway_ambient_closed backend property->parameters!_data=Some data->gateway_object_pointer_value data->
  environment!_host_has_type=None->environment!_PyDict_Type=None->
  Genv.find_symbol ge _host_has_type=Some function->Genv.find_funct_ptr ge function=Some(Internal f_host_has_type)->
  Genv.find_symbol ge _PyDict_Type=Some dictionary->
  gateway_source_path backend ge(Internal f_host_has_type)[data;Vptr dictionary Ptrofs.zero;Vint Int.zero]
    (gateway_outcome_first_type_cont environment parameters)property
    (State f_host_outcome_from(fn_body f_host_outcome_from)Kstop environment parameters before)property.
Proof.
  intros CLOSED DATA POINTER LOCAL TYPE_LOCAL SYMBOL FUNCTION DICTIONARY.
  gateway_bound_source_call CLOSED ltac:(fun _=>fail)ltac:(fun _=>reflexivity).
  eapply gateway_source_same with(target:=Callstate(Internal f_host_has_type)
    [data;Vptr dictionary Ptrofs.zero;Vint Int.zero](gateway_outcome_first_type_cont environment parameters)before).
  - exact CLOSED.
  - cbn;tauto.
  - intros;eapply certified_call_edge with(vf:=Vptr function Ptrofs.zero).
    + reflexivity.
    + apply old_expression_value;eapply value_function;[exact LOCAL|exact SYMBOL|reflexivity].
    + apply cons_argument_values with(v:=data).
      * apply old_expression_value,value_temp;exact DATA.
      * destruct POINTER as[NULL|[object[offset SAME]]];subst data;reflexivity.
      * apply cons_argument_values with(v:=Vptr dictionary Ptrofs.zero).
        -- apply gateway_global_address_expression;assumption.
        -- reflexivity.
        -- apply cons_argument_values with(v:=Vint Int.zero);
             [apply old_expression_value;constructor|reflexivity|apply no_argument_values].
    + cbn;exact FUNCTION.
    + reflexivity.
  - apply gateway_source_reached;auto.
Qed.

Theorem gateway_actual_outcome_first_type {World Event}(backend:gateway_backend World Event)
    io native stable discipline thread_errno(runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    (ge:Clight.genv)data before world events value after next function dictionary:
  discipline None before world->gateway_object_pointer_value data->
  Genv.find_symbol ge _host_has_type=Some function->Genv.find_funct_ptr ge function=Some(Internal f_host_has_type)->
  Genv.find_symbol ge _PyDict_Type=Some dictionary->
  gateway_steps backend ge(gateway_live(Callstate(Internal f_host_outcome_from)[data]Kstop before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists prefix suffix called current environment parameters,
    events=prefix++suffix /\discipline None called current /\gateway_native_environment native current called environment /\
    parameters!_data=Some data /\
    gateway_steps backend ge(gateway_live(Callstate(Internal f_host_outcome_from)[data]Kstop before)world)prefix
      (gateway_live(Callstate(Internal f_host_has_type)[data;Vptr dictionary Ptrofs.zero;Vint Int.zero]
        (gateway_outcome_first_type_cont environment parameters)called)current) /\
    gateway_steps backend ge
      (gateway_live(Callstate(Internal f_host_has_type)[data;Vptr dictionary Ptrofs.zero;Vint Int.zero]
        (gateway_outcome_first_type_cont environment parameters)called)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros SIDE POINTER SYMBOL FUNCTION DICTIONARY RUN.
  destruct(gateway_actual_outcome_entry backend io native stable discipline thread_errno runtime ge data before world events value after next SIDE RUN)
    as(pending &rest &entry_memory &entry_world &environment &allocated &EVENTS &AMBIENT &PREFIX &ENTRY &BUFFERS &READY &NATIVE &REST).
  set(property:=fun memory world=>discipline None memory world /\gateway_native_environment native world memory environment).
  assert(CLOSED:gateway_ambient_closed backend property).
  { exact(gateway_local_runtime_discipline backend io native stable discipline thread_errno runtime None environment). }
  assert(LOCAL:environment!_host_has_type=None).
  { apply(proj2(proj2(proj2 BUFFERS)));cbn;intuition discriminate. }
  assert(TYPE_LOCAL:environment!_PyDict_Type=None).
  { apply(proj2(proj2(proj2 BUFFERS)));cbn;intuition discriminate. }
  pose proof(gateway_outcome_first_type_source backend ge property environment(gateway_outcome_parameters data)data allocated function dictionary
    CLOSED ltac:(apply PTree.gss)POINTER LOCAL TYPE_LOCAL SYMBOL FUNCTION DICTIONARY)as PATH.
  destruct(gateway_source_path_cut backend ge _ _ _ property _ property PATH allocated entry_world rest value after next
    (conj READY NATIVE)REST)as(prelude &suffix &called &current &REST_EVENTS &QUIET &TO_CALL &[CALLED PRIVATE]&SUFFIX).
  exists(pending++gateway_source E0::prelude),suffix,called,current,environment,(gateway_outcome_parameters data).
  split;[rewrite EVENTS,REST_EVENTS,<-app_assoc;reflexivity|]. split;[exact CALLED|]. split;[exact PRIVATE|].
  split;[apply PTree.gss|]. split.
  - eapply gateway_steps_append;[exact PREFIX|].
    econstructor;[apply gateway_internal;[exact I|apply step_internal_function;exact ENTRY]|exact TO_CALL].
  - exact SUFFIX.
Qed.
