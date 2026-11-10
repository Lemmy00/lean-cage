(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Flag calls load the same pair's actual engine-facing descriptor. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayBindings GatewaySpawnABI
  GatewayFramedRuntime GatewayMemoryPrefixes GatewayExchangeSetup GatewayExchangeLoads GatewayPairContext GatewayPairMemory.
Import ListNotations.

Definition exchange_get_flags_prefix:=match exchange_get_flags with Ssequence prefix _=>prefix|_=>Sskip end.
Definition exchange_get_flags_bind:=match exchange_get_flags with Ssequence _ bind=>bind|_=>Sskip end.
Definition exchange_get_flags_load:=match exchange_get_flags_prefix with Ssequence load _=>load|_=>Sskip end.
Definition exchange_get_flags_call:=match exchange_get_flags_prefix with Ssequence _ call=>call|_=>Sskip end.
Definition exchange_get_flags_cont environment temporaries:=
  Kcall(Some _t'8)f_host_exchange environment temporaries
    (Kseq exchange_get_flags_bind(Kseq(exchange_setup_after 5)Kstop)).

Lemma actual_exchange_get_flags_call(ge:Clight.genv)environment temporaries memory right symbol:
  temporaries!_t'99=Some(Vint(Int.repr right))->environment!_leancage_host_fcntl=None->
  Genv.find_symbol ge _leancage_host_fcntl=Some symbol->
  Genv.find_funct_ptr ge symbol=Some(gateway_spawn_signature gateway_fcntl_api)->
  store_edge ge(State f_host_exchange exchange_get_flags_call
    (Kseq exchange_get_flags_bind(Kseq(exchange_setup_after 5)Kstop))environment temporaries memory)
    (Callstate(gateway_spawn_signature gateway_fcntl_api)[Vint(Int.repr right);Vint(Int.repr 3);Vint Int.zero]
      (exchange_get_flags_cont environment temporaries)memory).
Proof.
  intros FD UNSHADOWED SYMBOL FUNCTION;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value;eapply value_function;[exact UNSHADOWED|exact SYMBOL|reflexivity].
  - eapply cons_argument_values with(v:=Vint(Int.repr right));[apply old_expression_value,value_temp;exact FD|reflexivity|].
    eapply cons_argument_values with(v:=Vint(Int.repr 3));[apply old_expression_value;constructor|reflexivity|].
    eapply cons_argument_values with(v:=Vint Int.zero);[apply old_expression_value;constructor|reflexivity|apply no_argument_values].
  - cbn;exact FUNCTION.
  - reflexivity.
Qed.

Theorem actual_exchange_get_flags_prefix {World Event}(backend:gateway_backend World Event)
    property(CLOSED:gateway_ambient_closed backend property)environment temporaries memory object left right symbol:
  environment!_pair=Some(object,tarray tint 2)->environment!_leancage_host_fcntl=None->
  Genv.find_symbol(Clight.globalenv prog)_leancage_host_fcntl=Some symbol->
  Genv.find_funct_ptr(Clight.globalenv prog)symbol=Some(gateway_spawn_signature gateway_fcntl_api)->
  (forall before world,property before world->gateway_pair_cells before object Ptrofs.zero left right)->
  gateway_memory_prefix backend(Clight.globalenv prog)
    (Callstate(gateway_spawn_signature gateway_fcntl_api)[Vint(Int.repr right);Vint(Int.repr 3);Vint Int.zero]
      (exchange_get_flags_cont environment(PTree.set _t'99(Vint(Int.repr right))temporaries))memory)property property
    (State f_host_exchange(exchange_setup_after 4)Kstop environment temporaries memory).
Proof.
  intros ARRAY UNSHADOWED SYMBOL FUNCTION CELLS.
  eapply gateway_memory_same with(following:=State f_host_exchange exchange_get_flags
    (Kseq(exchange_setup_after 5)Kstop)environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_memory_same with(following:=State f_host_exchange exchange_get_flags_prefix
    (Kseq exchange_get_flags_bind(Kseq(exchange_setup_after 5)Kstop))environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_memory_same with(following:=State f_host_exchange exchange_get_flags_load
    (Kseq exchange_get_flags_call(Kseq exchange_get_flags_bind(Kseq(exchange_setup_after 5)Kstop)))
    environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  set(loaded:=PTree.set _t'99(Vint(Int.repr right))temporaries).
  eapply gateway_memory_same with(following:=State f_host_exchange Sskip
    (Kseq exchange_get_flags_call(Kseq exchange_get_flags_bind(Kseq(exchange_setup_after 5)Kstop)))
    environment loaded memory);
    [exact CLOSED|cbn;tauto| |].
  { intros before world READY;apply certified_set_edge.
    change(expression_value(Clight.globalenv prog)environment temporaries before
      (Ederef(exchange_endpoint_element _pair 1)tint)(Vint(Int.repr right))).
    exact(actual_exchange_endpoint_load _ environment temporaries before _pair object left right 1 ARRAY(CELLS before world READY)ltac:(lia)). }
  eapply gateway_memory_same with(following:=State f_host_exchange exchange_get_flags_call
    (Kseq exchange_get_flags_bind(Kseq(exchange_setup_after 5)Kstop))environment loaded memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_memory_same with(following:=Callstate(gateway_spawn_signature gateway_fcntl_api)
    [Vint(Int.repr right);Vint(Int.repr 3);Vint Int.zero](exchange_get_flags_cont environment loaded)memory);
    [exact CLOSED|cbn;tauto| |].
  { intros before world READY;apply actual_exchange_get_flags_call with(symbol:=symbol);[apply PTree.gss|exact UNSHADOWED|exact SYMBOL|exact FUNCTION]. }
  apply gateway_memory_identity.
Qed.
