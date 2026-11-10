(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Cleanup uses the real post-spawn source and selected SDK headers. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewaySpawnABI GatewaySpawnCall GatewaySpawnActions
  GatewayPostSpawnRelease GatewaySDKCall GatewayExchangeSetup GatewayPrefix GatewayMemoryPrefixes GatewayFramedRuntime.
Import ListNotations.
Open Scope Z_scope.

Fixpoint postspawn_after(count:nat):statement:=match count with O=>spawn_after_decision|
  S prior=>match postspawn_after prior with Ssequence _ rest=>rest|_=>Sskip end end.
Definition postspawn_at count:=match postspawn_after count with Ssequence first _=>first|_=>Sskip end.
Definition postspawn_release_index kind:nat:=match kind with gateway_release_actions=>1|gateway_release_attributes=>0 end.
Definition postspawn_release_identifier kind:=match kind with gateway_release_actions=>_actions|gateway_release_attributes=>_attributes end.
Definition postspawn_release_type kind:=match kind with gateway_release_actions=>gateway_actions_type|gateway_release_attributes=>gateway_attributes_type end.
Definition postspawn_release_cont kind environment temporaries:=Kcall None f_host_exchange environment temporaries
  (Kseq(postspawn_after(S(postspawn_release_index kind)))Kstop).

Theorem actual_postspawn_release_call ge kind environment temporaries memory object:
  environment!(postspawn_release_identifier kind)=Some(object,postspawn_release_type kind)->
  environment!(gateway_spawn_identifier(gateway_release_api kind))=None->
  gateway_function_binding ge(gateway_spawn_identifier(gateway_release_api kind))(gateway_spawn_signature(gateway_release_api kind))->
  store_edge ge(State f_host_exchange(postspawn_at(postspawn_release_index kind))
    (Kseq(postspawn_after(S(postspawn_release_index kind)))Kstop)environment temporaries memory)
    (Callstate(gateway_spawn_signature(gateway_release_api kind))[Vptr object Ptrofs.zero]
      (postspawn_release_cont kind environment temporaries)memory).
Proof.
  intros HEADER LOCAL[symbol[SYMBOL FUNCTION]];destruct kind.
  all:first[eapply gateway_sdk_source_call with(api:=gateway_actions_destroy_api)|
    eapply gateway_sdk_source_call with(api:=gateway_attributes_destroy_api)];
    [exact LOCAL|exact SYMBOL|exact FUNCTION|eapply cons_argument_values with(v:=Vptr object Ptrofs.zero);
      [apply local_address_expression;exact HEADER|reflexivity|apply no_argument_values]].
Qed.

Theorem actual_postspawn_release_prefix {World Event}(backend:gateway_backend World Event)
    property(CLOSED:gateway_ambient_closed backend property)kind allocation_before allocated environment temporaries memory object:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  environment!(postspawn_release_identifier kind)=Some(object,postspawn_release_type kind)->
  gateway_memory_prefix backend(Clight.globalenv prog)
    (Callstate(gateway_spawn_signature(gateway_release_api kind))[Vptr object Ptrofs.zero]
      (postspawn_release_cont kind environment temporaries)memory)property property
    (State f_host_exchange(postspawn_after(postspawn_release_index kind))Kstop environment temporaries memory).
Proof.
  intros ALLOC HEADER.
  eapply gateway_memory_same with(following:=State f_host_exchange(postspawn_at(postspawn_release_index kind))
    (Kseq(postspawn_after(S(postspawn_release_index kind)))Kstop)environment temporaries memory);
    [exact CLOSED|destruct kind;cbn;tauto|intros;destruct kind;apply unchanged_store_edge,edge_seq|].
  eapply gateway_memory_same with(following:=Callstate(gateway_spawn_signature(gateway_release_api kind))[Vptr object Ptrofs.zero]
    (postspawn_release_cont kind environment temporaries)memory);
    [exact CLOSED|cbn;destruct kind;tauto| |apply gateway_memory_identity].
  intros before world READY;apply actual_postspawn_release_call;[exact HEADER| |apply actual_gateway_spawn_binding].
  eapply actual_exchange_setup_unshadowed;[exact ALLOC|destruct kind;cbn;intuition discriminate].
Qed.

Lemma actual_postspawn_return_next {World Event}(backend:gateway_backend World Event)ge
    property(CLOSED:gateway_ambient_closed backend property)index environment temporaries memory:
  gateway_memory_prefix backend ge(State f_host_exchange(postspawn_after(S index))Kstop environment temporaries memory)
    property property(State f_host_exchange Sskip(Kseq(postspawn_after(S index))Kstop)environment temporaries memory).
Proof.
  eapply gateway_memory_same with(following:=State f_host_exchange(postspawn_after(S index))Kstop environment temporaries memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|apply gateway_memory_identity].
Qed.
