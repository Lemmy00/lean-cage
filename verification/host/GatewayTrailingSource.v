(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: The real trailing-byte guard loads the parser's same remaining budget. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayMemoryPrefixes GatewayFramedRuntime
  GatewayStreamInterface GatewayStreamLayout GatewayExchangeTransport GatewayResponseParserSource.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_trailing_flag(word:int64):int:=if Int64.eq word Int64.zero then Int.zero else Int.one.
Definition gateway_trailing_temps remaining(temporaries:temp_env):=
  PTree.set _t'45(Vint(gateway_trailing_flag remaining))(PTree.set _t'64(Vlong remaining)temporaries).
Definition exchange_trailing_load_body:=match exchange_trailing_select with Sifthenelse _ first _=>first|_=>Sskip end.
Definition exchange_trailing_load:=match exchange_trailing_load_body with Ssequence first _=>first|_=>Sskip end.
Definition exchange_trailing_cast:=match exchange_trailing_load_body with Ssequence _ rest=>rest|_=>Sskip end.

Lemma gateway_remaining_bool_cast ge environment temporaries memory identifier word:
  temporaries!identifier=Some(Vlong word)->
  expression_value ge environment temporaries memory(Ecast(Etempvar identifier tulong)tbool)(Vint(gateway_trailing_flag word)).
Proof.
  intro LOOK;apply old_expression_value;eapply value_cast with(v:=Vlong word);[apply value_temp;exact LOOK|].
  reflexivity.
Qed.

Theorem actual_trailing_select_path {World Event}(backend:gateway_backend World Event)ge
    property(CLOSED:gateway_ambient_closed backend property)environment temporaries memory stream initial object offset:
  environment!_stream=Some(stream,Tstruct _host_stream noattr)->stream_member_layout ge _remaining 24->
  temporaries!_result=Some(Vptr object offset)->
  (forall before world,property before world->gateway_stream_memory before stream Ptrofs.zero initial)->
  (forall before world,property before world->Mem.weak_valid_pointer before object(Ptrofs.unsigned offset)=true)->
  gateway_memory_prefix backend ge
    (State f_host_exchange exchange_trailing_test(Kseq(exchange_transport_after 7)Kstop)environment
      (gateway_trailing_temps(stream_remaining initial)temporaries)memory)property property
    (State f_host_exchange(exchange_transport_after 6)Kstop environment temporaries memory).
Proof.
  intros STREAM LAYOUT RESULT CELLS POINTER.
  eapply gateway_memory_same with(following:=State f_host_exchange exchange_trailing_phase
    (Kseq(exchange_transport_after 7)Kstop)environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_memory_same with(following:=State f_host_exchange exchange_trailing_select
    (Kseq exchange_trailing_test(Kseq(exchange_transport_after 7)Kstop))environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_memory_same with(following:=State f_host_exchange exchange_trailing_load_body
    (Kseq exchange_trailing_test(Kseq(exchange_transport_after 7)Kstop))environment temporaries memory);
    [exact CLOSED|cbn;tauto| |].
  - intros before world READY;apply certified_if_edge with(v:=Vptr object offset)(b:=true).
    + apply old_expression_value,value_temp;exact RESULT.
    + change((if Mem.weak_valid_pointer before object(Ptrofs.unsigned offset)then Some true else None)=Some true).
      rewrite(POINTER before world READY);reflexivity.
  - eapply gateway_memory_same with(following:=State f_host_exchange exchange_trailing_load
      (Kseq exchange_trailing_cast(Kseq exchange_trailing_test(Kseq(exchange_transport_after 7)Kstop)))environment temporaries memory);
      [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
    eapply gateway_memory_same with(following:=State f_host_exchange Sskip
      (Kseq exchange_trailing_cast(Kseq exchange_trailing_test(Kseq(exchange_transport_after 7)Kstop)))environment
      (PTree.set _t'64(Vlong(stream_remaining initial))temporaries)memory);
      [exact CLOSED|cbn;tauto| |].
    + intros before world READY;apply certified_set_edge;eapply actual_local_response_remaining;
        [exact STREAM|exact LAYOUT|exact(CELLS before world READY)].
    + eapply gateway_memory_same with(following:=State f_host_exchange exchange_trailing_cast
        (Kseq exchange_trailing_test(Kseq(exchange_transport_after 7)Kstop))environment
        (PTree.set _t'64(Vlong(stream_remaining initial))temporaries)memory);
        [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
      eapply gateway_memory_same with(following:=State f_host_exchange Sskip
        (Kseq exchange_trailing_test(Kseq(exchange_transport_after 7)Kstop))environment
        (gateway_trailing_temps(stream_remaining initial)temporaries)memory);
        [exact CLOSED|cbn;tauto|intros;apply certified_set_edge;apply gateway_remaining_bool_cast;apply PTree.gss|].
      eapply gateway_memory_same with(following:=State f_host_exchange exchange_trailing_test
        (Kseq(exchange_transport_after 7)Kstop)environment(gateway_trailing_temps(stream_remaining initial)temporaries)memory);
        [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|apply gateway_memory_identity].
Qed.
