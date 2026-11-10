(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Parent peer closes load the same selected pair cells. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewaySpawnABI GatewayPostSpawnSource GatewaySDKCall
  GatewayExchangeSetup GatewayExchangeLoads GatewayPairContext GatewayMemoryPrefixes GatewayFramedRuntime.
Import ListNotations.
Open Scope Z_scope.

Inductive gateway_parent_peer:=gateway_parent_data_peer|gateway_parent_control_peer.
Definition postspawn_peer_index peer:nat:=match peer with gateway_parent_data_peer=>2|gateway_parent_control_peer=>3 end.
Definition postspawn_peer_identifier peer:=match peer with gateway_parent_data_peer=>_pair|gateway_parent_control_peer=>_control end.
Definition postspawn_peer_temp peer:=match peer with gateway_parent_data_peer=>_t'79|gateway_parent_control_peer=>_t'78 end.
Definition postspawn_peer_load peer:=match postspawn_at(postspawn_peer_index peer)with Ssequence first _=>first|_=>Sskip end.
Definition postspawn_peer_call peer:=match postspawn_at(postspawn_peer_index peer)with Ssequence _ rest=>rest|_=>Sskip end.
Definition postspawn_peer_temps peer fd temporaries:=PTree.set(postspawn_peer_temp peer)(Vint(Int.repr fd))temporaries.
Definition postspawn_peer_cont peer environment temporaries:=Kcall None f_host_exchange environment temporaries
  (Kseq(postspawn_after(S(postspawn_peer_index peer)))Kstop).

Lemma actual_postspawn_peer_call ge peer environment temporaries memory fd:
  environment!_close=None->gateway_function_binding ge _close(gateway_spawn_signature gateway_close_api)->
  temporaries!(postspawn_peer_temp peer)=Some(Vint(Int.repr fd))->
  store_edge ge(State f_host_exchange(postspawn_peer_call peer)(Kseq(postspawn_after(S(postspawn_peer_index peer)))Kstop)
    environment temporaries memory)
    (Callstate(gateway_spawn_signature gateway_close_api)[Vint(Int.repr fd)](postspawn_peer_cont peer environment temporaries)memory).
Proof.
  intros LOCAL[symbol[SYMBOL FUNCTION]]FD;destruct peer.
  all:eapply gateway_sdk_source_call with(api:=gateway_close_api);
    [exact LOCAL|exact SYMBOL|exact FUNCTION|eapply cons_argument_values with(v:=Vint(Int.repr fd));
      [apply old_expression_value,value_temp;exact FD|reflexivity|apply no_argument_values]].
Qed.

Theorem actual_postspawn_peer_prefix {World Event}(backend:gateway_backend World Event)
    property(CLOSED:gateway_ambient_closed backend property)peer allocation_before allocated environment temporaries memory object left right:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  environment!(postspawn_peer_identifier peer)=Some(object,tarray tint 2)->
  (forall memory world,property memory world->gateway_pair_cells memory object Ptrofs.zero left right)->
  gateway_memory_prefix backend(Clight.globalenv prog)
    (Callstate(gateway_spawn_signature gateway_close_api)[Vint(Int.repr right)]
      (postspawn_peer_cont peer environment(postspawn_peer_temps peer right temporaries))memory)property property
    (State f_host_exchange(postspawn_after(postspawn_peer_index peer))Kstop environment temporaries memory).
Proof.
  intros ALLOC ARRAY CELLS.
  eapply gateway_memory_same with(following:=State f_host_exchange(postspawn_at(postspawn_peer_index peer))
    (Kseq(postspawn_after(S(postspawn_peer_index peer)))Kstop)environment temporaries memory);
    [exact CLOSED|destruct peer;cbn;tauto|intros;destruct peer;apply unchanged_store_edge,edge_seq|].
  eapply gateway_memory_same with(following:=State f_host_exchange(postspawn_peer_load peer)
    (Kseq(postspawn_peer_call peer)(Kseq(postspawn_after(S(postspawn_peer_index peer)))Kstop))environment temporaries memory);
    [exact CLOSED|destruct peer;cbn;tauto|intros;destruct peer;apply unchanged_store_edge,edge_seq|].
  eapply gateway_memory_same with(following:=State f_host_exchange Sskip
    (Kseq(postspawn_peer_call peer)(Kseq(postspawn_after(S(postspawn_peer_index peer)))Kstop))environment
    (postspawn_peer_temps peer right temporaries)memory);
    [exact CLOSED|destruct peer;cbn;tauto| |].
  - intros before world READY;destruct peer;apply certified_set_edge.
    all:eapply actual_exchange_endpoint_load with(left:=left)(right:=right)(index:=1);[exact ARRAY|exact(CELLS before world READY)|lia].
  - eapply gateway_memory_same with(following:=State f_host_exchange(postspawn_peer_call peer)
      (Kseq(postspawn_after(S(postspawn_peer_index peer)))Kstop)environment(postspawn_peer_temps peer right temporaries)memory);
      [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
    eapply gateway_memory_same with(following:=Callstate(gateway_spawn_signature gateway_close_api)[Vint(Int.repr right)]
      (postspawn_peer_cont peer environment(postspawn_peer_temps peer right temporaries))memory);
      [exact CLOSED|destruct peer;cbn;tauto| |apply gateway_memory_identity].
    intros before world READY;apply actual_postspawn_peer_call.
    + eapply actual_exchange_setup_unshadowed;[exact ALLOC|cbn;intuition discriminate].
    + exact(actual_gateway_spawn_binding gateway_close_api).
    + apply PTree.gss.
Qed.
