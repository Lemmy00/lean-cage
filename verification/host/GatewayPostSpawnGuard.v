(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual zero spawn-status branch reaches stream initialization. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPostSpawnSource GatewayPostSpawnCleanup GatewayMemoryPrefixes GatewayFramedRuntime.
Import ListNotations.

Lemma postspawn_cleanup_keeps data_right control_right temporaries identifier:
  identifier<>_t'79->identifier<>_t'78->
  (postspawn_cleanup_temps data_right control_right temporaries)!identifier=temporaries!identifier.
Proof.
  intros DATA CONTROL;unfold postspawn_cleanup_temps,GatewayPostSpawnPeers.postspawn_peer_temps,GatewayPostSpawnPeers.postspawn_peer_temp;
    rewrite !PTree.gso by congruence;reflexivity.
Qed.

Theorem actual_postspawn_zero_guard {World Event}(backend:gateway_backend World Event)ge
    property(CLOSED:gateway_ambient_closed backend property)environment temporaries memory:
  temporaries!_started=Some(Vint Int.zero)->
  gateway_memory_prefix backend ge(State f_host_exchange(postspawn_after 5)Kstop environment temporaries memory)
    property property(State f_host_exchange(postspawn_after 4)Kstop environment temporaries memory).
Proof.
  intro ZERO.
  eapply gateway_memory_same with(following:=State f_host_exchange(postspawn_at 4)(Kseq(postspawn_after 5)Kstop)
    environment temporaries memory);[exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_memory_same with(following:=State f_host_exchange Sskip(Kseq(postspawn_after 5)Kstop)environment temporaries memory);
    [exact CLOSED|cbn;tauto| |].
  - intros;apply certified_if_edge with(v:=Vint Int.zero)(b:=false);
      [apply old_expression_value,value_temp;exact ZERO|reflexivity].
  - eapply gateway_memory_same with(following:=State f_host_exchange(postspawn_after 5)Kstop environment temporaries memory);
      [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|apply gateway_memory_identity].
Qed.
