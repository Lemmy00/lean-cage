(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: The actual unsigned counter executes two pair-normalization iterations. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPairStatements GatewayFramedRuntime GatewaySetupPaths.
Import ListNotations.
Open Scope Z_scope.

Section PairLoopControl.
Context {World Event}(backend:gateway_backend World Event)(ge:Clight.genv).
Variable ready:mem->World->Prop.
Context(CLOSED:gateway_ambient_closed backend ready).
Local Ltac pair_same target:=eapply gateway_setup_same with(next:=target);
  [exact CLOSED|cbn;tauto|intros available current GOOD|].

Lemma actual_pair_loop_end temporaries memory result:
  temporaries!_index=Some(Vint(Int.repr 2))->
  (forall memory world,ready memory world->result memory world)->
  gateway_setup_path backend ge result ready
    (State f_host_private_pair pair_loop(Kseq pair_return Kstop)empty_env temporaries memory).
Proof.
  intros INDEX POST.
  pair_same(State f_host_private_pair pair_iteration pair_loop_cont empty_env temporaries memory).
  { apply unchanged_store_edge,edge_loop. }
  pair_same(State f_host_private_pair pair_limit(Kseq pair_work pair_loop_cont)empty_env temporaries memory).
  { apply unchanged_store_edge,edge_seq. }
  pair_same(State f_host_private_pair Sbreak(Kseq pair_work pair_loop_cont)empty_env temporaries memory).
  { apply certified_if_edge with(v:=Vint Int.zero)(b:=false).
    - pose proof(actual_pair_limit ge temporaries available 2 INDEX ltac:(lia))as VALUE.
      destruct(zlt 2 2);[lia|exact VALUE].
    - reflexivity. }
  pair_same(State f_host_private_pair Sbreak pair_loop_cont empty_env temporaries memory).
  { apply unchanged_store_edge,edge_break_seq. }
  pair_same(State f_host_private_pair Sskip(Kseq pair_return Kstop)empty_env temporaries memory).
  { apply unchanged_store_edge,edge_break_loop1. }
  pair_same(State f_host_private_pair pair_return Kstop empty_env temporaries memory).
  { apply unchanged_store_edge,edge_skip_seq. }
  pair_same(Returnstate(Vint Int.zero)Kstop memory).
  { apply unchanged_store_edge;eapply edge_return with(v:=Vint Int.zero);[constructor|reflexivity]. }
  constructor;assumption.
Qed.

Lemma actual_pair_loop_advance temporaries memory index result:
  temporaries!_index=Some(Vint(Int.repr index))->0<=index<2->
  gateway_setup_path backend ge result ready
    (State f_host_private_pair pair_loop(Kseq pair_return Kstop)empty_env
      (PTree.set _index(Vint(Int.repr(index+1)))temporaries)memory)->
  gateway_setup_path backend ge result ready
    (State f_host_private_pair Sskip pair_loop_cont empty_env temporaries memory).
Proof.
  intros INDEX BOUND REST.
  pair_same(State f_host_private_pair pair_increment
    (Kloop2 pair_iteration pair_increment(Kseq pair_return Kstop))empty_env temporaries memory).
  { apply unchanged_store_edge,edge_skip_loop1. }
  pair_same(State f_host_private_pair Sskip(Kloop2 pair_iteration pair_increment(Kseq pair_return Kstop))empty_env
    (PTree.set _index(Vint(Int.repr(index+1)))temporaries)memory).
  { apply certified_set_edge,old_expression_value;eapply value_binary.
    - apply value_temp;exact INDEX.
    - constructor.
    - change(Some(Vint(Int.add(Int.repr index)Int.one))=Some(Vint(Int.repr(index+1)))).
      rewrite Int.add_unsigned,Int.unsigned_repr by(change Int.max_unsigned with 4294967295;lia).
      reflexivity. }
  pair_same(State f_host_private_pair pair_loop(Kseq pair_return Kstop)empty_env
    (PTree.set _index(Vint(Int.repr(index+1)))temporaries)memory).
  { apply unchanged_store_edge,edge_skip_loop2. }
  exact REST.
Qed.
End PairLoopControl.
