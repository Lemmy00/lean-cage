(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: The actual read entry supplies its guard under coupled runtime ownership. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs
  Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayRuntimeCuts GatewayInstructions GatewayOperations
  GatewayReadonly GatewayReadGuard GatewayReadEntry GatewayStreamInterface GatewayStreamLayout GatewayStreamAccess GatewayCalls.
From HostGateway Require Import GatewayContexts GatewayReadTransfer GatewayReturnTypes.
Import ListNotations.
Open Scope Z_scope.

Theorem actual_read_source_reaches_guard {World Event}(backend:gateway_backend World Event)ge
    stream_block stream_offset data amount initial before world events returned after next
    (ready:mem->World->Prop)(discipline:gateway_runtime_discipline backend ready)
    (sufficient:forall memory current,ready memory current->gateway_stream_memory memory stream_block stream_offset initial) :
  stream_member_layout ge _remaining 24 ->ready before world ->
  gateway_steps backend ge
    (gateway_live(Callstate(Internal f_host_read)[Vptr stream_block stream_offset;data;Vlong(Int64.repr amount)]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next) ->
  exists prefix suffix memory current,
    events=prefix++suffix /\Forall gateway_quiet_event prefix /\
    gateway_steps backend ge
      (gateway_live(Callstate(Internal f_host_read)[Vptr stream_block stream_offset;data;Vlong(Int64.repr amount)]Kstop before)world)prefix
      (gateway_live(State f_host_read read_test(Kseq read_tail Kstop)empty_env
        (read_guard_values(Vptr stream_block stream_offset)data amount(stream_remaining initial))memory)current) /\
    ready memory current /\
    gateway_steps backend ge
      (gateway_live(State f_host_read read_test(Kseq read_tail Kstop)empty_env
        (read_guard_values(Vptr stream_block stream_offset)data amount(stream_remaining initial))memory)current)suffix
      (gateway_live(Returnstate returned Kstop after)next).
Proof.
  intros LAYOUT READY RUN.
  destruct(gateway_actual_function_entry_side backend ge ready discipline f_host_read
    [Vptr stream_block stream_offset;data;Vlong(Int64.repr amount)]Kstop before world events returned Kstop after next READY RUN)
    as[prefix0[suffix0[entry_memory[entry_world[environment[temporaries[allocated
      [EVENTS0[QUIET0[PREFIX0[READY0[ENTRY REST0]]]]]]]]]]]].
  destruct(actual_read_entry_canonical ge(Vptr stream_block stream_offset)data amount entry_memory
    environment temporaries allocated ENTRY)as[ENV[TEMPS MEMORY]];subst environment temporaries allocated.
  destruct(gateway_uniform_edge_side_cut backend ge ready discipline
    (State f_host_read(fn_body f_host_read)Kstop empty_env(read_parameters(Vptr stream_block stream_offset)data amount)entry_memory)
    (State f_host_read read_guard(Kseq read_tail Kstop)empty_env(read_parameters(Vptr stream_block stream_offset)data amount)entry_memory)
    entry_memory entry_world suffix0 returned after next ltac:(cbn;tauto)
    ltac:(intro memory;apply unchanged_store_edge,edge_seq)READY0 REST0)
    as[prefix1[suffix1[memory1[world1[EVENTS1[AMBIENT1[PREFIX1[READY1 REST1]]]]]]]].
  cbn[GatewayMachine.gateway_replace_memory]in PREFIX1,REST1.
  destruct(gateway_uniform_edge_side_cut backend ge ready discipline
    (State f_host_read read_guard(Kseq read_tail Kstop)empty_env(read_parameters(Vptr stream_block stream_offset)data amount)memory1)
    (State f_host_read read_load(Kseq read_test(Kseq read_tail Kstop))empty_env
      (read_parameters(Vptr stream_block stream_offset)data amount)memory1)
    memory1 world1 suffix1 returned after next ltac:(cbn;tauto)
    ltac:(intro memory;apply unchanged_store_edge,edge_seq)READY1 REST1)
    as[prefix2[suffix2[memory2[world2[EVENTS2[AMBIENT2[PREFIX2[READY2 REST2]]]]]]]].
  cbn[GatewayMachine.gateway_replace_memory]in PREFIX2,REST2.
  destruct(gateway_set_result_cut backend ge f_host_read _t'3(stream_member _remaining tulong)
    (Kseq read_test(Kseq read_tail Kstop))empty_env(read_parameters(Vptr stream_block stream_offset)data amount)
    memory2 world2 suffix2 returned after next REST2)
    as[prefix3[suffix3[memory3[world3[value[EVENTS3[AMBIENT3[PREFIX3[VALUE REST3]]]]]]]]].
  assert(READY3:ready memory3 world3).
  { eapply gateway_ambient_run_ready with(backend:=backend)(ge:=ge)(ready:=ready)
      (source:=State f_host_read read_load(Kseq read_test(Kseq read_tail Kstop))empty_env
        (read_parameters(Vptr stream_block stream_offset)data amount)memory2)
      (before:=memory2)(world:=world2)(events:=prefix3)(after:=memory3)(next:=world3);
      [exact discipline|exact READY2|exact AMBIENT3|exact PREFIX3]. }
  assert(LOADED:expression_value ge empty_env(read_parameters(Vptr stream_block stream_offset)data amount)memory3
    (stream_member _remaining tulong)(Vlong(stream_remaining initial))).
  { eapply actual_stream_member_read with(block:=stream_block)(offset:=stream_offset)(delta:=24)(chunk:=Mint64).
    - reflexivity.
    - exact LAYOUT.
    - reflexivity.
    - exact(proj1(proj2(proj2(proj2(proj2(proj2(sufficient memory3 world3 READY3))))))). }
  destruct LOADED as[CANON UNIQUE];pose proof(UNIQUE _ VALUE)as SAME;subst value.
  change(gateway_steps backend ge
    (gateway_live(State f_host_read Sskip(Kseq read_test(Kseq read_tail Kstop))empty_env
      (read_guard_values(Vptr stream_block stream_offset)data amount(stream_remaining initial))memory3)world3)suffix3
    (gateway_live(Returnstate returned Kstop after)next))in REST3.
  destruct(gateway_uniform_edge_side_cut backend ge ready discipline
    (State f_host_read Sskip(Kseq read_test(Kseq read_tail Kstop))empty_env
      (read_guard_values(Vptr stream_block stream_offset)data amount(stream_remaining initial))memory3)
    (State f_host_read read_test(Kseq read_tail Kstop)empty_env
      (read_guard_values(Vptr stream_block stream_offset)data amount(stream_remaining initial))memory3)
    memory3 world3 suffix3 returned after next ltac:(cbn;tauto)
    ltac:(intro memory;apply unchanged_store_edge,edge_skip_seq)READY3 REST3)
    as[prefix4[suffix4[memory4[world4[EVENTS4[AMBIENT4[PREFIX4[READY4 REST4]]]]]]]].
  cbn[GatewayMachine.gateway_replace_memory]in PREFIX4,REST4.
  exists(prefix0++gateway_source E0::prefix1++gateway_source E0::prefix2++gateway_source E0::prefix3++
    gateway_source E0::prefix4++[gateway_source E0]),suffix4,memory4,world4.
  split.
  - rewrite EVENTS0,EVENTS1,EVENTS2,EVENTS3,EVENTS4.
    repeat(rewrite <-app_assoc;cbn[app]);reflexivity.
  - assert(QUIET1:Forall gateway_quiet_event prefix1).
    { eapply Forall_impl;[|exact AMBIENT1];intros event SAME;right;exact SAME. }
    assert(QUIET2:Forall gateway_quiet_event prefix2).
    { eapply Forall_impl;[|exact AMBIENT2];intros event SAME;right;exact SAME. }
    assert(QUIET3:Forall gateway_quiet_event prefix3).
    { eapply Forall_impl;[|exact AMBIENT3];intros event SAME;right;exact SAME. }
    assert(QUIET4:Forall gateway_quiet_event prefix4).
    { eapply Forall_impl;[|exact AMBIENT4];intros event SAME;right;exact SAME. }
    split.
    + apply Forall_app;split;[exact QUIET0|]. constructor;[left;reflexivity|].
      apply Forall_app;split;[exact QUIET1|]. constructor;[left;reflexivity|].
      apply Forall_app;split;[exact QUIET2|]. constructor;[left;reflexivity|].
      apply Forall_app;split;[exact QUIET3|]. constructor;[left;reflexivity|].
      apply Forall_app;split;[exact QUIET4|]. constructor;[left;reflexivity|constructor].
    + split.
      * eapply gateway_steps_append;[exact PREFIX0|].
        econstructor;[apply gateway_internal;[exact I|eapply step_internal_function;exact ENTRY]|].
        eapply gateway_steps_append;[exact PREFIX1|].
        econstructor;[apply gateway_internal;[exact I|constructor]|].
        eapply gateway_steps_append;[exact PREFIX2|].
        econstructor;[apply gateway_internal;[exact I|constructor]|].
        eapply gateway_steps_append;[exact PREFIX3|].
        econstructor;[apply gateway_internal;[exact I|apply step_set;exact VALUE]|].
        eapply gateway_steps_append;[exact PREFIX4|].
        econstructor;[apply gateway_internal;[exact I|constructor]|constructor].
      * split;[exact READY4|exact REST4].
Qed.

Theorem actual_successful_read_source_transfer_execution {World Event}(backend:gateway_backend World Event)ge
    stream_block stream_offset data_block data_offset amount initial before world events after next
    (ready:mem->World->Prop)(discipline:gateway_runtime_discipline backend ready)
    (sufficient:forall memory current,ready memory current->gateway_stream_memory memory stream_block stream_offset initial)
    symbol :
  stream_member_layout ge _remaining 24 ->ready before world ->0<=amount<=Int64.max_unsigned ->
  Genv.find_symbol ge _host_transfer=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some(Internal f_host_transfer) ->
  gateway_steps backend ge
    (gateway_live(Callstate(Internal f_host_read)
      [Vptr stream_block stream_offset;Vptr data_block data_offset;Vlong(Int64.repr amount)]Kstop before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next) ->
  amount<=Int64.unsigned(stream_remaining initial) /\
  exists prefix transfer_events caller_events called called_world transferred transferred_world,
    events=prefix++transfer_events++caller_events /\Forall gateway_quiet_event prefix /\
    gateway_steps backend ge
      (gateway_live(Callstate(Internal f_host_read)
        [Vptr stream_block stream_offset;Vptr data_block data_offset;Vlong(Int64.repr amount)]Kstop before)world)prefix
      (gateway_live(Callstate(Internal f_host_transfer)
        [Vptr stream_block stream_offset;Vptr data_block data_offset;Vlong(Int64.repr amount);Vint Int.zero]
        (read_transfer_cont(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount
          (stream_remaining initial))called)called_world) /\
    ready called called_world /\
    gateway_steps backend ge
      (gateway_live(Callstate(Internal f_host_transfer)
        [Vptr stream_block stream_offset;Vptr data_block data_offset;Vlong(Int64.repr amount);Vint Int.zero]
        Kstop called)called_world)transfer_events
      (gateway_live(Returnstate(Vint Int.zero)Kstop transferred)transferred_world) /\
    gateway_steps backend ge
      (gateway_live(Returnstate(Vint Int.zero)
        (read_transfer_cont(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount
          (stream_remaining initial))transferred)transferred_world)caller_events
      (gateway_live(Returnstate(Vint Int.zero)Kstop after)next).
Proof.
  intros LAYOUT READY AMOUNT SYMBOL FUNCTION RUN.
  destruct(actual_read_source_reaches_guard backend ge stream_block stream_offset(Vptr data_block data_offset)
    amount initial before world events(Vint Int.zero)after next ready discipline sufficient LAYOUT READY RUN)
    as[guard_prefix[guard_suffix[memory[current[GUARD_EVENTS[GUARD_QUIET[GUARD_PREFIX[GUARD_READY GUARD_REST]]]]]]]].
  assert(FITS:amount<=Int64.unsigned(stream_remaining initial)).
  { destruct(Z_le_gt_dec amount(Int64.unsigned(stream_remaining initial)));[assumption|].
    pose proof(actual_read_excess_test_returns_failure backend ge(Vptr stream_block stream_offset)
      (Vptr data_block data_offset)amount(stream_remaining initial)memory current guard_suffix
      (Vint Int.zero)after next AMOUNT ltac:(lia)GUARD_REST)as BAD;discriminate BAD. }
  split;[exact FITS|].
  destruct(gateway_retained_call_ready_cut backend ge ready discipline(Internal f_host_transfer)
    [Vptr stream_block stream_offset;Vptr data_block data_offset;Vlong(Int64.repr amount);Vint Int.zero]
    (read_transfer_cont(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount(stream_remaining initial))
    (State f_host_read read_test(Kseq read_tail Kstop)empty_env
      (read_guard_values(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount(stream_remaining initial))memory)
    current guard_suffix(Vint Int.zero)after next
    (actual_read_guard_transfer_path ge stream_block stream_offset data_block data_offset amount
      (stream_remaining initial)memory symbol AMOUNT FITS SYMBOL FUNCTION)GUARD_READY GUARD_REST)
    as[call_prefix[call_suffix[called[called_world[CALL_EVENTS[CALL_QUIET[CALL_PREFIX[CALL_READY CALL_REST]]]]]]]].
  destruct(gateway_return_cut backend ge(Internal f_host_transfer)
    [Vptr stream_block stream_offset;Vptr data_block data_offset;Vlong(Int64.repr amount);Vint Int.zero]
    (read_transfer_cont(Vptr stream_block stream_offset)(Vptr data_block data_offset)amount(stream_remaining initial))
    called called_world call_suffix(Returnstate(Vint Int.zero)Kstop after)next ltac:(reflexivity)
    ltac:(cbn[read_transfer_cont gateway_continuation gateway_cont_weight];lia)CALL_REST)
    as[transfer_events[caller_events[returned[transferred[transferred_world[RETURN_EVENTS[TRANSFER CALLER]]]]]]].
  pose proof(gateway_actual_int_return backend ge f_host_transfer _ _ _ _ _ _ _
    actual_host_transfer_return_profile TRANSFER)as TYPE.
  pose proof(actual_successful_read_transfer_return backend ge(Vptr stream_block stream_offset)
    (Vptr data_block data_offset)amount(stream_remaining initial)transferred transferred_world caller_events
    returned after next TYPE CALLER)as ZERO;subst returned.
  exists(guard_prefix++call_prefix),transfer_events,caller_events,called,called_world,transferred,transferred_world.
  split.
  - rewrite GUARD_EVENTS,CALL_EVENTS,RETURN_EVENTS.
    repeat(rewrite <-app_assoc;cbn[app]);reflexivity.
  - split;[apply Forall_app;auto|].
    split;[eapply gateway_steps_append;[exact GUARD_PREFIX|exact CALL_PREFIX]|].
    split;[exact CALL_READY|]. split;assumption.
Qed.
