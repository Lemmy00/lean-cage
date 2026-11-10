(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Nonzero setup selects the original caller's cleanup before spawning. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewaySpawnABI GatewaySpawnVectors GatewaySpawnCall GatewayMemoryPrefixes
  GatewayExchangeErrors GatewayExchangeSetup GatewayFramedRuntime GatewaySymbolicBarrier GatewayLaunchPaths GatewayLaunchMemory.
Import ListNotations.

Theorem actual_started_cleanup_returns:gateway_symbolic_returns exchange_error_allowed _started spawn_after_decision.
Proof. vm_compute;tauto. Qed.

Definition exchange_failed_started word temporaries:=PTree.set _started(Vint word)(PTree.set _t'26(Vint word)temporaries).

Lemma actual_failed_setup_decision_prefix {World Event}(backend:gateway_backend World Event)
    environment temporaries memory word:
  temporaries!_setup=Some(Vint word)->Int.eq word Int.zero=false->
  gateway_memory_prefix backend(Clight.globalenv prog)
    (State f_host_exchange spawn_after_decision Kstop environment(exchange_failed_started word temporaries)memory)
    (fun _ _=>True)(fun _ _=>True)
    (State f_host_exchange(spawn_vector_after 6)Kstop environment temporaries memory).
Proof.
  intros SETUP NONZERO.
  assert(CLOSED:gateway_ambient_closed backend(fun _ _=>True))by(unfold gateway_ambient_closed;intros;exact I).
  eapply gateway_memory_same with(following:=State f_host_exchange spawn_decision_sequence
    (Kseq spawn_after_decision Kstop)environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_memory_same with(following:=State f_host_exchange spawn_decision
    (Kseq spawn_bind_started(Kseq spawn_after_decision Kstop))environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_memory_same with(following:=State f_host_exchange(Sset _t'26(Ecast(Etempvar _setup tint)tint))
    (Kseq spawn_bind_started(Kseq spawn_after_decision Kstop))environment temporaries memory);
    [exact CLOSED|cbn;tauto| |].
  { intros before world READY;apply certified_if_edge with(v:=Vint word)(b:=true).
    - apply old_expression_value,value_temp;exact SETUP.
    - change(Some(negb(Int.eq word Int.zero))=Some true);rewrite NONZERO;reflexivity. }
  set(selected:=PTree.set _t'26(Vint word)temporaries).
  eapply gateway_memory_same with(following:=State f_host_exchange Sskip
    (Kseq spawn_bind_started(Kseq spawn_after_decision Kstop))environment selected memory);
    [exact CLOSED|cbn;tauto| |].
  { intros before world READY;apply certified_set_edge,old_expression_value;eapply value_cast with(v:=Vint word);
      [apply value_temp;exact SETUP|reflexivity]. }
  eapply gateway_memory_same with(following:=State f_host_exchange spawn_bind_started
    (Kseq spawn_after_decision Kstop)environment selected memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_memory_same with(following:=State f_host_exchange Sskip(Kseq spawn_after_decision Kstop)environment
    (exchange_failed_started word temporaries)memory);
    [exact CLOSED|cbn;tauto|intros;apply certified_set_edge,old_expression_value,value_temp;apply PTree.gss|].
  eapply gateway_memory_same with(following:=State f_host_exchange spawn_after_decision Kstop environment
    (exchange_failed_started word temporaries)memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  apply gateway_memory_identity.
Qed.

Theorem actual_failed_setup_decision_path {World Event}(backend:gateway_backend World Event)
    target allocation_before allocated environment temporaries memory word:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  temporaries!_setup=Some(Vint word)->Int.eq word Int.zero=false->
  gateway_launch_path backend target(fun _ _=>True)
    (State f_host_exchange(spawn_vector_after 6)Kstop environment temporaries memory).
Proof.
  intros ALLOC SETUP NONZERO.
  eapply gateway_launch_after_memory_prefix;
    [exact(actual_failed_setup_decision_prefix backend environment temporaries memory word SETUP NONZERO)|].
  eapply gateway_launch_symbolic_failure with(allowed:=exchange_error_allowed)(protected:=_started)(word:=word).
  - exact(actual_exchange_error_bindings allocation_before environment allocated ALLOC).
  - exact NONZERO.
  - apply PTree.gss.
  - exact actual_started_cleanup_returns.
  - reflexivity.
Qed.

Theorem actual_failed_setup_decision_excludes_spawn {World Event}(backend:gateway_backend World Event)
    allocation_before allocated environment temporaries before world word events arguments continuation after next:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  temporaries!_setup=Some(Vint word)->Int.eq word Int.zero=false->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_exchange(spawn_vector_after 6)Kstop environment temporaries before)world)events
    (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after)next)->False.
Proof.
  intros ALLOC SETUP NONZERO RUN.
  destruct(gateway_memory_prefix_cut backend(Clight.globalenv prog)_ _ _ _ before world events
    (Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after)next
    (actual_failed_setup_decision_prefix backend environment temporaries before word SETUP NONZERO)I I RUN)
    as(prefix&suffix&memory&current&EVENTS&QUIET&PREFIX&READY&SUFFIX).
  eapply gateway_symbolic_barrier_excludes_call with(continuation:=Kstop)(protected:=_started)(word:=word)
    (temporaries:=exchange_failed_started word temporaries)(body:=spawn_after_decision);
    [exact(actual_exchange_error_bindings allocation_before environment allocated ALLOC)|exact NONZERO|apply PTree.gss|
      exact actual_started_cleanup_returns|reflexivity|exact SUFFIX].
Qed.
