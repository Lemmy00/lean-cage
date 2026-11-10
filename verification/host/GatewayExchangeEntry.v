(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The exchange owns its actual spawn and framing stack buffers. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayFunctionEntry GatewayCalls
  GatewayOperations GatewayThreadRuntime GatewayLocalRuntime GatewayStackAllocation GatewayStreamInterface.
Import ListNotations.
Open Scope Z_scope.

Definition exchange_parameters fields command fault cancellation cli:=
  PTree.set _cli(Vint cli)(PTree.set _cancellation cancellation
    (PTree.set _fault(Vint fault)(PTree.set _command(Vint command)
      (PTree.set _fields fields(create_undef_temps(fn_temps f_host_exchange)))))).

Lemma actual_exchange_entry_canonical ge fields command fault cancellation cli before environment temporaries allocated:
  function_entry2 ge f_host_exchange[fields;Vint command;Vint fault;cancellation;Vint cli]before
    environment temporaries allocated->
  temporaries=exchange_parameters fields command fault cancellation cli /\
  alloc_variables ge empty_env before(fn_vars f_host_exchange)environment allocated.
Proof.
  intro ENTRY;inversion ENTRY;subst.
  match goal with BIND:bind_parameter_temps _ _ _=Some temporaries|-_=>
    change(Some(exchange_parameters fields command fault cancellation cli)=Some temporaries)in BIND;
    inversion BIND;subst end.
  split;[reflexivity|assumption].
Qed.

Lemma actual_exchange_variables_unique:list_norepet(map fst(fn_vars f_host_exchange)).
Proof. repeat(apply list_norepet_cons;[cbn;intuition discriminate|]);apply list_norepet_nil. Qed.

Definition exchange_stack_buffers ge before environment after:Prop:=
  (forall identifier ty,In(identifier,ty)(fn_vars f_host_exchange)->
    exists object,environment!identifier=Some(object,ty) /\~Mem.valid_block before object /\
      Mem.range_perm after object 0(sizeof ge ty)Cur Freeable) /\
  gateway_stack_environment after environment /\Mem.unchanged_on(fun _ _=>True)before after.

Lemma actual_exchange_allocations ge before environment after:
  alloc_variables ge empty_env before(fn_vars f_host_exchange)environment after->
  exchange_stack_buffers ge before environment after.
Proof.
  intro ALLOC;split.
  - intros identifier ty MEMBER;eapply gateway_alloc_variables_member;
      [exact ALLOC|exact actual_exchange_variables_unique|exact MEMBER].
  - split.
    + eapply gateway_alloc_variables_stack;[exact ALLOC|apply gateway_empty_stack_environment].
    + eapply gateway_alloc_variables_frame;exact ALLOC.
Qed.

Theorem actual_exchange_entry_owns_packet ge before environment after:
  exchange_stack_buffers ge before environment after->
  exists header stream,
    environment!_header=Some(header,tarray tuchar 112) /\
    environment!_stream=Some(stream,Tstruct _host_stream noattr) /\header<>stream /\
    ~Mem.valid_block before header /\~Mem.valid_block before stream /\
    Mem.range_perm after header 0 112 Cur Freeable /\
    Mem.range_perm after stream 0(sizeof ge(Tstruct _host_stream noattr))Cur Freeable.
Proof.
  intros[BUFFERS[[LIVE DISTINCT]FRAME]].
  destruct(BUFFERS _header(tarray tuchar 112)ltac:(cbn;auto 12))as[header[HEADER[FRESH_HEADER HEADER_PERMISSIONS]]].
  destruct(BUFFERS _stream(Tstruct _host_stream noattr)ltac:(cbn;auto 12))as[stream[STREAM[FRESH_STREAM STREAM_PERMISSIONS]]].
  exists header,stream;split;[exact HEADER|]. split;[exact STREAM|]. split.
  - eapply DISTINCT;[exact HEADER|exact STREAM|discriminate].
  - split;[exact FRESH_HEADER|]. split;[exact FRESH_STREAM|]. split;[|exact STREAM_PERMISSIONS].
    change(sizeof ge(tarray tuchar 112))with 112 in HEADER_PERMISSIONS;exact HEADER_PERMISSIONS.
Qed.

Section ExchangeSourceEntry.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
  (native_private:World->block->Prop)(stable_readonly:World->block->Z->Prop)
  (discipline:option val->mem->World->Prop)(thread_errno:World->int).
Context(runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).

Theorem actual_exchange_source_allocates ge fields command fault cancellation cli before world events returned after next:
  discipline None before world->
  gateway_steps backend ge
    (gateway_live(Callstate(Internal f_host_exchange)
      [fields;Vint command;Vint fault;cancellation;Vint cli]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next)->
  exists prefix suffix called current environment allocated,
    events=prefix++gateway_source Events.E0::suffix /\Forall(fun event=>event=gateway_ambient)prefix /\
    gateway_steps backend ge
      (gateway_live(Callstate(Internal f_host_exchange)
        [fields;Vint command;Vint fault;cancellation;Vint cli]Kstop before)world)prefix
      (gateway_live(Callstate(Internal f_host_exchange)
        [fields;Vint command;Vint fault;cancellation;Vint cli]Kstop called)current) /\
    exchange_stack_buffers ge called environment allocated /\discipline None allocated current /\
    gateway_native_environment native_private current allocated environment /\
    gateway_steps backend ge
      (gateway_live(State f_host_exchange(fn_body f_host_exchange)Kstop environment
        (exchange_parameters fields command fault cancellation cli)allocated)current)suffix
      (gateway_live(Returnstate returned Kstop after)next).
Proof.
  intros SIDE RUN.
  destruct(actual_gateway_function_entry_ambient backend ge f_host_exchange
    [fields;Vint command;Vint fault;cancellation;Vint cli]Kstop before world events returned Kstop after next RUN)
    as(prefix & suffix & called & current & environment & temporaries & allocated &
      EVENTS & AMBIENT & PREFIX & ENTRY & REST).
  assert(CALLED:discipline None called current).
  { eapply gateway_ambient_run_ready with(source:=Callstate(Internal f_host_exchange)
      [fields;Vint command;Vint fault;cancellation;Vint cli]Kstop before).
    - intros original source changed target READY INTERFERENCE.
      exact(proj1(gateway_thread_ambient _ _ _ _ _ _ runtime None _ _ _ _ READY INTERFERENCE)).
    - exact SIDE.
    - exact AMBIENT.
    - exact PREFIX. }
  destruct(actual_exchange_entry_canonical ge fields command fault cancellation cli called environment temporaries allocated ENTRY)
    as[TEMPS ALLOC];subst temporaries.
  destruct(gateway_native_alloc_variables backend io native_private stable_readonly discipline thread_errno runtime ge None
    empty_env called(fn_vars f_host_exchange)environment allocated current ALLOC CALLED
    (gateway_native_environment_empty native_private current called))as[ALLOCATED NATIVE].
  exists prefix,suffix,called,current,environment,allocated.
  split;[exact EVENTS|]. split;[exact AMBIENT|]. split;[exact PREFIX|].
  split;[apply actual_exchange_allocations;exact ALLOC|]. split;[exact ALLOCATED|]. split;assumption.
Qed.

End ExchangeSourceEntry.
