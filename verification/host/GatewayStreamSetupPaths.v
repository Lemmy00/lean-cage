(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Real pair loads precede their corresponding stream assignments. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPostSpawnSource GatewayStreamSetupSource GatewayExchangeLoads
  GatewayPairContext GatewayMemoryPrefixes GatewayFramedRuntime.
Import ListNotations.
Open Scope Z_scope.

Lemma stream_setup_temps_keeps data_left control_left count temporaries identifier:
  identifier<>_t'74->identifier<>_t'73->
  (stream_setup_temps data_left control_left count temporaries)!identifier=temporaries!identifier.
Proof.
  intros DATA CONTROL;destruct count as[|[|count]];cbn[stream_setup_temps];try reflexivity;rewrite !PTree.gso by congruence;reflexivity.
Qed.
Lemma actual_stream_setup_source_tail index:
  (index<8)%nat->postspawn_after(5+index)=Ssequence(stream_setup_at index)(postspawn_after(6+index)).
Proof. intro BOUND;do 8(destruct index as[|index];[reflexivity|]);lia. Qed.

Section Prefix.
Context {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
  (property:mem->World->Prop)(CLOSED:gateway_ambient_closed backend property).
Variables(environment:env)(temporaries:temp_env)(memory:mem)(data control:Values.block)(data_left data_right control_left control_right:Z).
Hypotheses(DATA:environment!_pair=Some(data,tarray tint 2))(CONTROL:environment!_control=Some(control,tarray tint 2))
  (CELLS:forall memory world,property memory world->gateway_pair_cells memory data Ptrofs.zero data_left data_right /\
    gateway_pair_cells memory control Ptrofs.zero control_left control_right).

Ltac stream_same sink:=eapply gateway_memory_same with(following:=sink);[exact CLOSED|cbn;tauto| |].
Ltac stream_structure sink edge:=stream_same sink;[intros;apply unchanged_store_edge,edge|].

Lemma actual_stream_setup_field_prefix index:
  (index<8)%nat->gateway_memory_prefix backend ge
    (State f_host_exchange(stream_setup_assignment index)(Kseq(postspawn_after(6+index))Kstop)environment
      (stream_setup_temps data_left control_left(S index)temporaries)memory)property property
    (State f_host_exchange(postspawn_after(5+index))Kstop environment
      (stream_setup_temps data_left control_left index temporaries)memory).
Proof.
  intro BOUND;rewrite(actual_stream_setup_source_tail index BOUND).
  stream_structure(State f_host_exchange(stream_setup_at index)(Kseq(postspawn_after(6+index))Kstop)environment
    (stream_setup_temps data_left control_left index temporaries)memory)edge_seq.
  destruct index as[|[|index]].
  - stream_structure(State f_host_exchange(Sset _t'74(Ederef(exchange_endpoint_element _pair 0)tint))
      (Kseq(stream_setup_assignment 0)(Kseq(postspawn_after 6)Kstop))environment temporaries memory)edge_seq.
    stream_same(State f_host_exchange Sskip(Kseq(stream_setup_assignment 0)(Kseq(postspawn_after 6)Kstop))environment
      (stream_setup_temps data_left control_left 1 temporaries)memory).
    + intros before world READY;apply certified_set_edge;eapply actual_exchange_endpoint_load with(left:=data_left)(right:=data_right)(index:=0);
        [exact DATA|exact(proj1(CELLS before world READY))|lia].
    + stream_structure(State f_host_exchange(stream_setup_assignment 0)(Kseq(postspawn_after 6)Kstop)environment
        (stream_setup_temps data_left control_left 1 temporaries)memory)edge_skip_seq.
      apply gateway_memory_identity.
  - stream_structure(State f_host_exchange(Sset _t'73(Ederef(exchange_endpoint_element _control 0)tint))
      (Kseq(stream_setup_assignment 1)(Kseq(postspawn_after 7)Kstop))environment
      (stream_setup_temps data_left control_left 1 temporaries)memory)edge_seq.
    stream_same(State f_host_exchange Sskip(Kseq(stream_setup_assignment 1)(Kseq(postspawn_after 7)Kstop))environment
      (stream_setup_temps data_left control_left 2 temporaries)memory).
    + intros before world READY;apply certified_set_edge;eapply actual_exchange_endpoint_load with(left:=control_left)(right:=control_right)(index:=0);
        [exact CONTROL|exact(proj2(CELLS before world READY))|lia].
    + stream_structure(State f_host_exchange(stream_setup_assignment 1)(Kseq(postspawn_after 7)Kstop)environment
        (stream_setup_temps data_left control_left 2 temporaries)memory)edge_skip_seq.
      apply gateway_memory_identity.
  - apply gateway_memory_identity.
Qed.
End Prefix.
