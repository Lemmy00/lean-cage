(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Reaching this exchange's later helper forces its actual spawn status zero. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewaySpawnABI GatewaySpawnCall GatewayExchangeErrors
  GatewayExchangeSetup GatewayStartedFailure GatewaySymbolicBarrier GatewayReturnBarrier GatewayReturnFrontier
  GatewayMemoryPrefixes GatewayFramedRuntime GatewayContexts.
Import ListNotations.

Definition exchange_spawn_return_temps status temporaries:=PTree.set _started(Vint status)
  (PTree.set _t'26(Vint status)(PTree.set _t'27(Vint status)temporaries)).

Lemma actual_spawn_return_status_prefix {World Event}(backend:gateway_backend World Event)
    property(CLOSED:gateway_ambient_closed backend property)environment temporaries memory status:
  gateway_memory_prefix backend(Clight.globalenv prog)
    (State f_host_exchange spawn_after_decision Kstop environment(exchange_spawn_return_temps status temporaries)memory)property property
    (State f_host_exchange Sskip(Kseq spawn_selected_cast(Kseq spawn_bind_started(Kseq spawn_after_decision Kstop)))
      environment(PTree.set _t'27(Vint status)temporaries)memory).
Proof.
  eapply gateway_memory_same with(following:=State f_host_exchange spawn_selected_cast
    (Kseq spawn_bind_started(Kseq spawn_after_decision Kstop))environment(PTree.set _t'27(Vint status)temporaries)memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_memory_same with(following:=State f_host_exchange Sskip
    (Kseq spawn_bind_started(Kseq spawn_after_decision Kstop))environment
    (PTree.set _t'26(Vint status)(PTree.set _t'27(Vint status)temporaries))memory);
    [exact CLOSED|cbn;tauto| |].
  - intros before world READY;apply certified_set_edge,old_expression_value.
    eapply value_cast with(v:=Vint status);[apply value_temp;apply PTree.gss|reflexivity].
  - eapply gateway_memory_same with(following:=State f_host_exchange spawn_bind_started(Kseq spawn_after_decision Kstop)environment
      (PTree.set _t'26(Vint status)(PTree.set _t'27(Vint status)temporaries))memory);
      [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
    eapply gateway_memory_same with(following:=State f_host_exchange Sskip(Kseq spawn_after_decision Kstop)environment
      (exchange_spawn_return_temps status temporaries)memory);
      [exact CLOSED|cbn;tauto|intros;apply certified_set_edge,old_expression_value,value_temp;apply PTree.gss|].
    eapply gateway_memory_same with(following:=State f_host_exchange spawn_after_decision Kstop environment
      (exchange_spawn_return_temps status temporaries)memory);
      [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|apply gateway_memory_identity].
Qed.

Lemma actual_exchange_error_internal_bindings allocation_before environment allocated helper:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  gateway_barrier_bindings(Clight.globalenv prog)environment exchange_error_allowed(Internal helper).
Proof.
  intros ALLOC identifier ALLOWED;split.
  - eapply actual_exchange_setup_unshadowed;[exact ALLOC|apply actual_exchange_error_not_local;exact ALLOWED].
  - unfold exchange_error_allowed in ALLOWED;rewrite existsb_exists in ALLOWED.
    destruct ALLOWED as[entry[MEMBER EQUAL]];apply Pos.eqb_eq in EQUAL;subst identifier.
    pose proof((proj1(Forall_forall _ _))actual_exchange_error_declarations entry MEMBER)as[symbol[SYMBOL FUNCTION]].
    pose proof((proj1(Forall_forall _ _))actual_exchange_error_external entry MEMBER)as[[external[types[result[convention EXTERNAL]]]]OTHER].
    exists symbol,(snd entry);split;[exact SYMBOL|]. split;[exact FUNCTION|]. split;[repeat eexists;exact EXTERNAL|].
    intro SAME;pose proof(eq_trans(eq_sym EXTERNAL)SAME)as IMPOSSIBLE;discriminate IMPOSSIBLE.
Qed.

Theorem actual_spawn_before_internal_success {World Event}(backend:gateway_backend World Event)
    allocation_before allocated environment temporaries before world status events helper arguments continuation after next:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Returnstate(Vint status)(gateway_spawn_call_cont environment temporaries Kstop)before)world)events
    (gateway_live(Callstate(Internal helper)arguments continuation after)next)->status=Int.zero.
Proof.
  intros ALLOC RUN;destruct(Int.eq status Int.zero)eqn:ZERO;[apply Int.same_if_eq;exact ZERO|].
  exfalso.
  assert(CLOSED:gateway_ambient_closed backend(fun _ _=>True))by(unfold gateway_ambient_closed;intros;exact I).
  destruct(gateway_actual_return_before_call backend(Clight.globalenv prog)(fun _ _=>True)CLOSED(Vint status)(Some _t'27)
    f_host_exchange environment temporaries(Kseq spawn_selected_cast(Kseq spawn_bind_started(Kseq spawn_after_decision Kstop)))
    before world events(Internal helper)arguments continuation after next I RUN)
    as(pending&rest&returned&current&EVENTS&AMBIENT&PREFIX&READY&REST).
  destruct(gateway_memory_prefix_cut backend(Clight.globalenv prog)_ _ _ _ returned current rest
    (Callstate(Internal helper)arguments continuation after)next
    (actual_spawn_return_status_prefix backend(fun _ _=>True)CLOSED environment temporaries returned status)I I REST)
    as(prefix&suffix&memory&owner&TAIL&QUIET&TO_STATUS&FINAL&SUFFIX).
  eapply gateway_symbolic_barrier_excludes_call with(protected:=_started)(word:=status)(continuation:=Kstop)
    (temporaries:=exchange_spawn_return_temps status temporaries)(body:=spawn_after_decision);
    [exact(actual_exchange_error_internal_bindings allocation_before environment allocated helper ALLOC)|
      exact ZERO|apply PTree.gss|exact actual_started_cleanup_returns|reflexivity|exact SUFFIX].
Qed.
