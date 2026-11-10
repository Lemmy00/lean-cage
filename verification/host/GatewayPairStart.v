(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: The genuine socketpair success initializes the maintained normalization loop. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewaySpawnABI GatewaySpawnResources GatewaySpawnRuntime
  GatewayPairContext GatewayPairSource GatewayPairStatements GatewayPairLoop
  GatewayThreadRuntime GatewayFramedRuntime GatewaySetupPaths GatewayOperations GatewayFrames GatewayStreamInterface GatewayPairBuffers.
Import ListNotations.
Open Scope Z_scope.

Section PairStart.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
  (native_private:World->block->Prop)(stable_readonly:World->block->Z->Prop)
  (discipline:option val->mem->World->Prop)(thread_errno:World->int)
  (resources:World->gateway_resource_state)(ipc:nat->Prop).
Context(runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno)
  (descriptors:gateway_spawn_descriptor_runtime backend io native_private stable_readonly discipline resources ipc).
Variable ge:Clight.genv.
Variable identity:gateway_pair_identity ipc.
Variable object:block.
Variable offset:ptrofs.
Variable history:mem->World->Prop.
Context(buffers:gateway_pair_buffer_laws backend native_private stable_readonly discipline object offset history).
Variables duplicate_symbol close_symbol:block.
Hypotheses(DUPLICATE_SYMBOL:Genv.find_symbol ge _leancage_host_fcntl=Some duplicate_symbol)
  (DUPLICATE_FUNCTION:Genv.find_funct_ptr ge duplicate_symbol=Some(gateway_spawn_signature gateway_fcntl_api))
  (CLOSE_SYMBOL:Genv.find_symbol ge _close=Some close_symbol)
  (CLOSE_FUNCTION:Genv.find_funct_ptr ge close_symbol=Some(gateway_spawn_signature gateway_close_api)).
Variable result:mem->World->Prop.
Hypothesis FINAL:forall left right memory world,4<=left->4<=right->
  gateway_pair_full_context native_private discipline resources ipc identity object offset left right history memory world->result memory world.
Local Definition pair_context left right:=gateway_pair_full_context native_private discipline resources ipc identity object offset left right history.
Local Lemma pair_context_closed left right:gateway_ambient_closed backend(pair_context left right).
Proof. apply gateway_pair_full_context_ambient with(io:=io)(stable_readonly:=stable_readonly)(thread_errno:=thread_errno);assumption. Qed.
Local Ltac pair_same target:=eapply gateway_setup_same with(next:=target);
  [apply pair_context_closed|cbn;tauto|intros available current GOOD|].

Theorem actual_pair_started_script left right memory:
  gateway_setup_path backend ge result(pair_context left right)
    (Returnstate(Vint Int.zero)(pair_socket_cont(Vptr object offset))memory).
Proof.
  set(temporaries:=PTree.set _t'1(Vint Int.zero)(pair_parameters(Vptr object offset))).
  pair_same(State f_host_private_pair Sskip(Kseq pair_socket_guard(Kseq pair_after_first Kstop))empty_env temporaries memory).
  { apply unchanged_store_edge,edge_returnstate. }
  pair_same(State f_host_private_pair pair_socket_guard(Kseq pair_after_first Kstop)empty_env temporaries memory).
  { apply unchanged_store_edge,edge_skip_seq. }
  pair_same(State f_host_private_pair Sskip(Kseq pair_after_first Kstop)empty_env temporaries memory).
  { apply certified_if_edge with(v:=Vint Int.zero)(b:=false);
      [apply old_expression_value,value_temp;apply PTree.gss|reflexivity]. }
  pair_same(State f_host_private_pair pair_after_first Kstop empty_env temporaries memory).
  { apply unchanged_store_edge,edge_skip_seq. }
  pair_same(State f_host_private_pair pair_for(Kseq pair_return Kstop)empty_env temporaries memory).
  { apply unchanged_store_edge,edge_seq. }
  pair_same(State f_host_private_pair pair_initialize(Kseq pair_loop(Kseq pair_return Kstop))empty_env temporaries memory).
  { apply unchanged_store_edge,edge_seq. }
  pair_same(State f_host_private_pair Sskip(Kseq pair_loop(Kseq pair_return Kstop))empty_env
    (PTree.set _index(Vint Int.zero)temporaries)memory).
  { apply certified_set_edge,old_expression_value;constructor. }
  pair_same(State f_host_private_pair pair_loop(Kseq pair_return Kstop)empty_env
    (PTree.set _index(Vint Int.zero)temporaries)memory).
  { apply unchanged_store_edge,edge_skip_seq. }
  eapply actual_pair_loop_script with(remaining:=2%nat)(index:=0)(io:=io)(stable_readonly:=stable_readonly)
    (thread_errno:=thread_errno)(duplicate_symbol:=duplicate_symbol)(close_symbol:=close_symbol);
    try eassumption;try reflexivity.
  - lia.
  - split;intros;lia.
Qed.
End PairStart.
