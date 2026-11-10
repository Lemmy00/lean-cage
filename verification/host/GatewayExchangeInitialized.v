(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual original-exchange progress passes the initialization guard. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayOperations GatewayFrames GatewayReadonly
  GatewayFramedRuntime GatewayMemoryPrefixes GatewayBoundaryValues GatewayReturnBarrier GatewayExchangeSetup
  GatewayExchangeErrors GatewaySpawnABI.
Import ListNotations.

Definition exchange_initialized_load:=match exchange_entry_guard with Ssequence load _=>load|_=>Sskip end.
Definition exchange_initialized_test:=match exchange_entry_guard with Ssequence _ test=>test|_=>Sskip end.
Definition exchange_uninitialized_body:=match exchange_initialized_test with Sifthenelse _ denied _=>denied|_=>Sskip end.
Definition exchange_entry_temps(value:val)(temporaries:temp_env):=PTree.set _t'105 value temporaries.

Theorem actual_exchange_initialized_structure:
  fn_body f_host_exchange=Ssequence exchange_entry_guard(exchange_setup_after 0) /\
  exchange_entry_guard=Ssequence exchange_initialized_load exchange_initialized_test /\
  exchange_initialized_load=Sset _t'105(Evar _host_initialized tint) /\
  exchange_initialized_test=Sifthenelse(Eunop Onotbool(Etempvar _t'105 tint)tint)exchange_uninitialized_body Sskip.
Proof. repeat split;reflexivity. Qed.
Lemma actual_exchange_uninitialized_returns:gateway_barrier_returns exchange_error_allowed exchange_uninitialized_body.
Proof. vm_compute;tauto. Qed.

Section Initialized.
Context {World Event}(backend:gateway_backend World Event)(property:mem->World->Prop).
Hypothesis CLOSED:gateway_ambient_closed backend property.
Variables environment:env.
Variable temporaries:temp_env.

Lemma actual_exchange_to_initialized_load memory:
  gateway_memory_prefix backend(Clight.globalenv prog)
    (State f_host_exchange exchange_initialized_load
      (Kseq exchange_initialized_test(Kseq(exchange_setup_after 0)Kstop))environment temporaries memory)
    property property(State f_host_exchange(fn_body f_host_exchange)Kstop environment temporaries memory).
Proof.
  eapply gateway_memory_same with(following:=State f_host_exchange exchange_entry_guard
    (Kseq(exchange_setup_after 0)Kstop)environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_memory_same with(following:=State f_host_exchange exchange_initialized_load
    (Kseq exchange_initialized_test(Kseq(exchange_setup_after 0)Kstop))environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|apply gateway_memory_identity].
Qed.

Lemma actual_exchange_initialized_to_test value memory:
  gateway_memory_prefix backend(Clight.globalenv prog)
    (State f_host_exchange exchange_initialized_test(Kseq(exchange_setup_after 0)Kstop)environment
      (exchange_entry_temps value temporaries)memory)property property
    (State f_host_exchange Sskip(Kseq exchange_initialized_test(Kseq(exchange_setup_after 0)Kstop))environment
      (exchange_entry_temps value temporaries)memory).
Proof.
  eapply gateway_memory_same with(following:=State f_host_exchange exchange_initialized_test
    (Kseq(exchange_setup_after 0)Kstop)environment(exchange_entry_temps value temporaries)memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|apply gateway_memory_identity].
Qed.
Lemma actual_exchange_initialized_to_body value memory:
  gateway_memory_prefix backend(Clight.globalenv prog)
    (State f_host_exchange(exchange_setup_after 0)Kstop environment(exchange_entry_temps value temporaries)memory)
    property property(State f_host_exchange Sskip(Kseq(exchange_setup_after 0)Kstop)environment
      (exchange_entry_temps value temporaries)memory).
Proof.
  eapply gateway_memory_same with(following:=State f_host_exchange(exchange_setup_after 0)Kstop environment
    (exchange_entry_temps value temporaries)memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|apply gateway_memory_identity].
Qed.

Theorem actual_exchange_initialized_cut allocation_before allocated before world events arguments continuation after next:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  property before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_exchange(fn_body f_host_exchange)Kstop environment temporaries before)world)events
    (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after)next)->
  exists prefix suffix memory current value,
    events=prefix++suffix /\Forall gateway_quiet_event prefix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange(fn_body f_host_exchange)Kstop environment temporaries before)world)prefix
      (gateway_live(State f_host_exchange(exchange_setup_after 0)Kstop environment
        (exchange_entry_temps value temporaries)memory)current) /\property memory current /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange(exchange_setup_after 0)Kstop environment
        (exchange_entry_temps value temporaries)memory)current)suffix
      (gateway_live(Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after)next).
Proof.
  intros ALLOC INITIAL RUN.
  destruct(gateway_memory_prefix_cut backend(Clight.globalenv prog)_ _ _ _ before world events
    (Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after)next
    (actual_exchange_to_initialized_load before)I INITIAL RUN)
    as(p0 & rest0 & m0 & w0 & E0S & Q0 & P0 & C0 & R0).
  cbn[gateway_replace_memory]in P0,R0.
  destruct(gateway_boundary_set_cut backend(Clight.globalenv prog)property CLOSED f_host_exchange _t'105
    (Evar _host_initialized tint)(Kseq exchange_initialized_test(Kseq(exchange_setup_after 0)Kstop))environment temporaries
    m0 w0 rest0(Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after)next I C0 R0)
    as(p1 & rest1 & m1 & w1 & value & E1 & Q1 & P1 & VALUE & C1 & R1).
  destruct(gateway_memory_prefix_cut backend(Clight.globalenv prog)_ _ _ _ m1 w1 rest1
    (Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after)next
    (actual_exchange_initialized_to_test value m1)I C1 R1)
    as(p2 & rest2 & m2 & w2 & E2 & Q2 & P2 & C2 & R2).
  cbn[gateway_replace_memory]in P2,R2.
  destruct(gateway_boundary_if_cut backend(Clight.globalenv prog)property CLOSED f_host_exchange
    (Eunop Onotbool(Etempvar _t'105 tint)tint)exchange_uninitialized_body Sskip
    (Kseq(exchange_setup_after 0)Kstop)environment(exchange_entry_temps value temporaries)
    m2 w2 rest2(Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after)next I C2 R2)
    as(p3 & rest3 & m3 & w3 & condition & branch & E3 & Q3 & P3 & CONDITION & BOOL & C3 & R3).
  destruct branch.
  - exfalso;eapply gateway_return_barrier_excludes_call with(continuation:=Kseq(exchange_setup_after 0)Kstop);
      [exact(actual_exchange_error_bindings allocation_before environment allocated ALLOC)
      |exact actual_exchange_uninitialized_returns|reflexivity|exact R3].
  - destruct(gateway_memory_prefix_cut backend(Clight.globalenv prog)_ _ _ _ m3 w3 rest3
      (Callstate(gateway_spawn_signature gateway_posix_spawn_api)arguments continuation after)next
      (actual_exchange_initialized_to_body value m3)I C3 R3)
      as(p4 & suffix & memory & current & E4 & Q4 & P4 & FINAL & SUFFIX).
    cbn[gateway_replace_memory]in P4,SUFFIX.
    exists(p0++p1++gateway_source E0::p2++p3++gateway_source E0::p4),suffix,memory,current,value.
    split.
    + rewrite E0S,E1,E2,E3,E4;repeat(rewrite <-app_assoc;cbn[app]);reflexivity.
    + split.
      * apply Forall_app;split;[exact Q0|]. apply Forall_app;split.
        -- eapply Forall_impl;[|exact Q1];intros event SAME;right;exact SAME.
        -- constructor;[left;reflexivity|]. apply Forall_app;split;[exact Q2|].
           apply Forall_app;split.
           ++ eapply Forall_impl;[|exact Q3];intros event SAME;right;exact SAME.
           ++ constructor;[left;reflexivity|exact Q4].
      * split.
        -- eapply gateway_steps_append;[exact P0|]. eapply gateway_steps_append;[exact P1|].
           econstructor.
           ++ apply gateway_internal;[exact I|apply step_set;exact VALUE].
           ++ eapply gateway_steps_append;[exact P2|]. eapply gateway_steps_append;[exact P3|].
              econstructor.
              ** apply gateway_internal;[exact I|eapply step_ifthenelse;[exact CONDITION|exact BOOL]].
              ** exact P4.
        -- split;assumption.
Qed.
End Initialized.
