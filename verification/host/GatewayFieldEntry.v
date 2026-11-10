(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: An actual helper return must cross its exact first bytes-API call. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayFrames GatewayCallPath
  GatewayPython GatewayAllocation GatewayPrefix GatewayFunctionEntry.
Import ListNotations.

Lemma actual_field_entry_is_canonical ge before arguments (continuation:cont) environment temporaries allocated :
  function_entry2 ge f_host_field_bytes(field_values arguments)before environment temporaries allocated ->
  exists locals,environment=field_environment locals /\temporaries=field_parameters arguments /\
    field_allocations before locals allocated /\
    Mem.unchanged_on(fun _ _=>True)before allocated /\
    ~Mem.valid_block before(field_local_data locals) /\
    ~Mem.valid_block before(field_local_size locals) /\
    field_local_data locals<>field_local_size locals /\
    Mem.range_perm allocated(field_local_data locals)0 8 Cur Freeable /\
    Mem.range_perm allocated(field_local_size locals)0 8 Cur Freeable.
Proof.
  intro ENTRY.
  destruct(actual_field_entry_allocates ge before arguments continuation)
    as[locals[canonical[[_[_ UNIQUE]][ALLOC[FRAME[FRESH_DATA[FRESH_SIZE[DISTINCT[DATA SIZE]]]]]]]]].
  assert(REAL:step2 ge
    (Callstate(Internal f_host_field_bytes)(field_values arguments)continuation before)E0
    (State f_host_field_bytes(fn_body f_host_field_bytes)continuation environment temporaries allocated)).
  { apply step_internal_function;exact ENTRY. }
  destruct(UNIQUE _ _ REAL)as[_ SAME];inversion SAME;subst.
  exists locals;split;[reflexivity|]. split;[reflexivity|].
  exact(conj ALLOC(conj FRAME(conj FRESH_DATA(conj FRESH_SIZE(conj DISTINCT(conj DATA SIZE)))))).
Qed.

Lemma field_body_first_callback (ge:Clight.genv) protected property locals arguments memory continuation symbol object offset :
  gateway_region_closed protected property ->
  field_object arguments=Vptr object offset ->
  Genv.find_symbol ge _PyBytes_AsStringAndSize=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some python_bytes_definition ->
  gateway_call_path ge protected python_bytes_definition
    [field_object arguments;Vptr(field_local_data locals)Ptrofs.zero;
      Vptr(field_local_size locals)Ptrofs.zero](field_api_cont locals arguments continuation)
    property property
    (State f_host_field_bytes(fn_body f_host_field_bytes)continuation
      (field_environment locals)(field_parameters arguments)memory).
Proof.
  intros CLOSED OBJECT SYMBOL FUNCTION;rewrite field_first_api_structure.
  eapply gateway_call_same with(next:=State f_host_field_bytes(Ssequence field_api_call field_api_test)
    (Kseq field_after_api continuation)(field_environment locals)(field_parameters arguments)memory).
  - exact CLOSED.
  - cbn;tauto.
  - intros another GOOD;apply unchanged_store_edge,edge_seq.
  - eapply gateway_call_same with(next:=State f_host_field_bytes field_api_call
      (Kseq field_api_test(Kseq field_after_api continuation))
      (field_environment locals)(field_parameters arguments)memory).
    + exact CLOSED.
    + cbn;tauto.
    + intros another GOOD;apply unchanged_store_edge,edge_seq.
    + eapply gateway_call_same with(next:=Callstate python_bytes_definition
        [field_object arguments;Vptr(field_local_data locals)Ptrofs.zero;
          Vptr(field_local_size locals)Ptrofs.zero](field_api_cont locals arguments continuation)memory).
      * exact CLOSED.
      * cbn;tauto.
      * intros another GOOD;eapply actual_field_first_api_call;eassumption.
      * constructor;[exact CLOSED|auto].
Qed.

Theorem actual_field_body_must_call_bytes {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    protected active(law:gateway_private_contract backend protected active)property
    locals arguments memory world events returned after final_world symbol object offset :
  gateway_region_closed protected property ->active world ->property memory ->
  field_object arguments=Vptr object offset ->
  Genv.find_symbol ge _PyBytes_AsStringAndSize=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some python_bytes_definition ->
  gateway_steps backend ge
    (gateway_live(State f_host_field_bytes(fn_body f_host_field_bytes)Kstop
      (field_environment locals)(field_parameters arguments)memory)world)events
    (gateway_live(Returnstate returned Kstop after)final_world) ->
  exists prefix suffix called_memory called_world,
    events=prefix++suffix /\
    gateway_steps backend ge
      (gateway_live(State f_host_field_bytes(fn_body f_host_field_bytes)Kstop
        (field_environment locals)(field_parameters arguments)memory)world)prefix
      (gateway_live(Callstate python_bytes_definition
        [field_object arguments;Vptr(field_local_data locals)Ptrofs.zero;
          Vptr(field_local_size locals)Ptrofs.zero](field_api_cont locals arguments Kstop)called_memory)called_world) /\
    property called_memory /\active called_world /\
    gateway_steps backend ge
      (gateway_live(Callstate python_bytes_definition
        [field_object arguments;Vptr(field_local_data locals)Ptrofs.zero;
          Vptr(field_local_size locals)Ptrofs.zero](field_api_cont locals arguments Kstop)called_memory)called_world)
      suffix(gateway_live(Returnstate returned Kstop after)final_world).
Proof.
  intros CLOSED ACTIVE PROPERTY OBJECT SYMBOL FUNCTION RUN.
  eapply gateway_call_path_cut;try eassumption.
  eapply field_body_first_callback;eassumption.
Qed.

Lemma field_body_control_first_callback (ge:Clight.genv)locals arguments memory continuation symbol object offset :
  field_object arguments=Vptr object offset ->
  Genv.find_symbol ge _PyBytes_AsStringAndSize=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some python_bytes_definition ->
  gateway_control_call_path ge python_bytes_definition
    [field_object arguments;Vptr(field_local_data locals)Ptrofs.zero;
      Vptr(field_local_size locals)Ptrofs.zero](field_api_cont locals arguments continuation)
    (State f_host_field_bytes(fn_body f_host_field_bytes)continuation
      (field_environment locals)(field_parameters arguments)memory).
Proof.
  intros OBJECT SYMBOL FUNCTION;rewrite field_first_api_structure.
  eapply gateway_control_call_next with(next:=State f_host_field_bytes(Ssequence field_api_call field_api_test)
    (Kseq field_after_api continuation)(field_environment locals)(field_parameters arguments)memory).
  - cbn;tauto.
  - intro another;exists another;apply unchanged_store_edge,edge_seq.
  - eapply gateway_control_call_next with(next:=State f_host_field_bytes field_api_call
      (Kseq field_api_test(Kseq field_after_api continuation))
      (field_environment locals)(field_parameters arguments)memory).
    + cbn;tauto.
    + intro another;exists another;apply unchanged_store_edge,edge_seq.
    + eapply gateway_control_call_next with(next:=Callstate python_bytes_definition
        [field_object arguments;Vptr(field_local_data locals)Ptrofs.zero;
          Vptr(field_local_size locals)Ptrofs.zero](field_api_cont locals arguments continuation)memory).
      * cbn;tauto.
      * intro another;exists another;eapply actual_field_first_api_call;eassumption.
      * constructor.
Qed.

Theorem actual_field_call_must_call_bytes {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    arguments before world events returned after final_world symbol object offset :
  field_object arguments=Vptr object offset ->
  Genv.find_symbol ge _PyBytes_AsStringAndSize=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some python_bytes_definition ->
  gateway_steps backend ge
    (gateway_live(Callstate(Internal f_host_field_bytes)(field_values arguments)Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)final_world) ->
  exists prefix suffix locals memory called_world allocation_before allocated,
    events=prefix++suffix /\field_allocations allocation_before locals allocated /\
    ~Mem.valid_block allocation_before(field_local_data locals) /\
    ~Mem.valid_block allocation_before(field_local_size locals) /\
    field_local_data locals<>field_local_size locals /\
    gateway_steps backend ge
      (gateway_live(Callstate(Internal f_host_field_bytes)(field_values arguments)Kstop before)world)prefix
      (gateway_live(Callstate python_bytes_definition
        [field_object arguments;Vptr(field_local_data locals)Ptrofs.zero;
          Vptr(field_local_size locals)Ptrofs.zero](field_api_cont locals arguments Kstop)memory)called_world) /\
    gateway_steps backend ge
      (gateway_live(Callstate python_bytes_definition
        [field_object arguments;Vptr(field_local_data locals)Ptrofs.zero;
          Vptr(field_local_size locals)Ptrofs.zero](field_api_cont locals arguments Kstop)memory)called_world)
      suffix(gateway_live(Returnstate returned Kstop after)final_world).
Proof.
  intros OBJECT SYMBOL FUNCTION RUN.
  destruct(actual_gateway_function_entry backend ge f_host_field_bytes(field_values arguments)Kstop
    before world events returned Kstop after final_world RUN)
    as[entry_prefix[body_events[allocation_before[allocation_world[environment[temporaries
      [allocated[EVENTS[PREFIX[ENTRY BODY]]]]]]]]]].
  destruct(actual_field_entry_is_canonical ge allocation_before arguments Kstop environment temporaries allocated ENTRY)
    as[locals[ENV[TEMPS[ALLOC[FRAME[FRESH_DATA[FRESH_SIZE[DISTINCT[DATA SIZE]]]]]]]]];subst environment temporaries.
  destruct(gateway_control_call_cut backend ge python_bytes_definition
    [field_object arguments;Vptr(field_local_data locals)Ptrofs.zero;
      Vptr(field_local_size locals)Ptrofs.zero](field_api_cont locals arguments Kstop)
    (State f_host_field_bytes(fn_body f_host_field_bytes)Kstop
      (field_environment locals)(field_parameters arguments)allocated)allocation_world body_events returned after final_world
    (field_body_control_first_callback ge locals arguments allocated Kstop symbol object offset
      OBJECT SYMBOL FUNCTION)BODY)
    as[body_prefix[suffix[memory[called_world[BODY_EVENTS[CALL REST]]]]]].
  exists(entry_prefix++gateway_source E0::body_prefix),suffix,locals,memory,called_world,allocation_before,allocated.
  split;[rewrite EVENTS,BODY_EVENTS;rewrite<-app_assoc;reflexivity|].
  split;[exact ALLOC|]. split;[exact FRESH_DATA|]. split;[exact FRESH_SIZE|]. split;[exact DISTINCT|].
  split;[|exact REST].
  eapply gateway_steps_append;[exact PREFIX|].
  econstructor;[apply gateway_internal;[exact I|apply step_internal_function;exact ENTRY]|exact CALL].
Qed.
