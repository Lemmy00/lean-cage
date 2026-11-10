(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: The first pair's caller reaches the actual second pair call. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayBindings GatewayExchangeSetup
  GatewayExchangePairPaths GatewayLaunchQuiet GatewayLaunchPaths GatewayFramedRuntime GatewayPure.
Import ListNotations.

Lemma actual_exchange_control_pair_call(ge:Clight.genv)environment temporaries memory control symbol:
  environment!_control=Some(control,tarray tint 2)->environment!_host_private_pair=None->
  Genv.find_symbol ge _host_private_pair=Some symbol->Genv.find_funct_ptr ge symbol=Some(Internal f_host_private_pair)->
  store_edge ge(State f_host_exchange exchange_control_pair_call
    (Kseq exchange_control_pair_guard(Kseq(exchange_setup_after 4)Kstop))environment temporaries memory)
    (Callstate(Internal f_host_private_pair)[Vptr control Ptrofs.zero]
      (exchange_pair_cont exchange_control_stage environment temporaries)memory).
Proof.
  intros ARRAY UNSHADOWED SYMBOL FUNCTION;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value;eapply value_function;[exact UNSHADOWED|exact SYMBOL|reflexivity].
  - eapply cons_argument_values with(v:=Vptr control Ptrofs.zero).
    + apply exchange_endpoint_reference;exact ARRAY.
    + reflexivity.
    + apply no_argument_values.
  - cbn;exact FUNCTION.
  - reflexivity.
Qed.

Definition exchange_control_pair_point {World}(property:mem->World->Prop)environment temporaries control source world:Prop:=
  exists memory,source=Callstate(Internal f_host_private_pair)[Vptr control Ptrofs.zero]
    (exchange_pair_cont exchange_control_stage environment temporaries)memory /\property memory world.

Theorem actual_exchange_control_pair_script {World Event}(backend:gateway_backend World Event)
    property(CLOSED:gateway_ambient_closed backend property)allocation_before allocated environment temporaries memory control:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  environment!_control=Some(control,tarray tint 2)->
  gateway_quiet_launch_path backend(exchange_control_pair_point property environment temporaries control)property
    (State f_host_exchange(exchange_setup_after 3)Kstop environment temporaries memory).
Proof.
  intros ALLOC ARRAY.
  eapply gateway_quiet_launch_same with(following:=State f_host_exchange exchange_control_pair
    (Kseq(exchange_setup_after 4)Kstop)environment temporaries memory);
    [exact CLOSED|cbn;tauto|exact I|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_quiet_launch_same with(following:=State f_host_exchange exchange_control_pair_call
    (Kseq exchange_control_pair_guard(Kseq(exchange_setup_after 4)Kstop))environment temporaries memory);
    [exact CLOSED|cbn;tauto|exact I|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_quiet_launch_same with(following:=Callstate(Internal f_host_private_pair)[Vptr control Ptrofs.zero]
    (exchange_pair_cont exchange_control_stage environment temporaries)memory);
    [exact CLOSED|cbn;tauto|exact I| |].
  - intros available world READY.
    destruct(gateway_actual_function_binding _host_private_pair(Internal f_host_private_pair)
      ltac:(vm_compute;reflexivity))as[symbol[SYMBOL FUNCTION]].
    eapply actual_exchange_control_pair_call;[exact ARRAY| |exact SYMBOL|exact FUNCTION].
    eapply actual_exchange_setup_unshadowed;[exact ALLOC|cbn;intuition discriminate].
  - apply gateway_quiet_launch_reached;intros available world READY;exists available;split;[reflexivity|exact READY].
Qed.
