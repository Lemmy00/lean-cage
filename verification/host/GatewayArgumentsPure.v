(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Root-loop control follows the actual unsigned guard and increment. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayFramedRuntime GatewayEffectRuntime GatewayArgumentsSource.
Import ListNotations.
Open Scope Z_scope.

Lemma arguments_increment_value index:
  0<=index<=14->Int.add(Int.repr index)Int.one=Int.repr(index+1).
Proof.
  intro BOUND;rewrite Int.add_unsigned,Int.unsigned_repr by(change Int.max_unsigned with 4294967295;lia).
  reflexivity.
Qed.

Section ArgumentsPure.
Context {World Event}(backend:gateway_backend World Event)(ge:Clight.genv).
Variable ready:mem->World->Prop.
Context(CLOSED:gateway_ambient_closed backend ready).

Ltac arguments_same target:=
  eapply gateway_effect_same with(next:=target);[exact CLOSED|cbn;tauto|intros available current GOOD;
    cbn[gateway_replace_memory]|].

Lemma actual_arguments_end temporaries memory count value result:
  temporaries!_index=Some(Vint(Int.repr count))->temporaries!_count=Some(Vint(Int.repr count))->
  0<=count<=14->value=Vundef->(forall memory world,ready memory world->result memory world)->
  gateway_effect_path backend ge ready
    (State f_host_arguments_retain arguments_retain_loop Kstop empty_env temporaries memory)value result.
Proof.
  intros INDEX COUNT BOUND VALUE POST;subst value.
  arguments_same(State f_host_arguments_retain arguments_retain_first arguments_retain_cont empty_env temporaries memory).
  { apply unchanged_store_edge,edge_loop. }
  arguments_same(State f_host_arguments_retain(Sifthenelse arguments_guard Sskip Sbreak)
    (Kseq arguments_retain_body arguments_retain_cont)empty_env temporaries memory).
  { apply unchanged_store_edge,edge_seq. }
  arguments_same(State f_host_arguments_retain Sbreak(Kseq arguments_retain_body arguments_retain_cont)empty_env temporaries memory).
  { apply certified_if_edge with(v:=Vint Int.zero)(b:=false).
    - pose proof(actual_arguments_guard ge temporaries available count count INDEX COUNT BOUND BOUND)as TEST.
      destruct(zlt count count);[lia|exact TEST].
    - reflexivity. }
  arguments_same(State f_host_arguments_retain Sbreak arguments_retain_cont empty_env temporaries memory).
  { apply unchanged_store_edge,edge_break_seq. }
  arguments_same(State f_host_arguments_retain Sskip Kstop empty_env temporaries memory).
  { apply unchanged_store_edge,edge_break_loop1. }
  arguments_same(Returnstate Vundef Kstop memory).
  { apply void_return_edge;exact I. }
  constructor;assumption.
Qed.

Lemma actual_arguments_increment temporaries memory index value result:
  temporaries!_index=Some(Vint(Int.repr index))->0<=index<=14->
  gateway_effect_path backend ge ready
    (State f_host_arguments_retain arguments_retain_loop Kstop empty_env
      (PTree.set _index(Vint(Int.repr(index+1)))temporaries)memory)value result->
  gateway_effect_path backend ge ready
    (State f_host_arguments_retain Sskip arguments_retain_cont empty_env temporaries memory)value result.
Proof.
  intros INDEX BOUND REST.
  arguments_same(State f_host_arguments_retain arguments_retain_increment
    (Kloop2 arguments_retain_first arguments_retain_increment Kstop)empty_env temporaries memory).
  { apply unchanged_store_edge,edge_skip_loop1. }
  arguments_same(State f_host_arguments_retain Sskip
    (Kloop2 arguments_retain_first arguments_retain_increment Kstop)empty_env
    (PTree.set _index(Vint(Int.repr(index+1)))temporaries)memory).
  { apply certified_set_edge;apply old_expression_value;eapply value_binary.
    - apply value_temp;exact INDEX.
    - constructor.
    - change(Some(Vint(Int.add(Int.repr index)Int.one))=Some(Vint(Int.repr(index+1)))).
      rewrite arguments_increment_value by exact BOUND;reflexivity. }
  arguments_same(State f_host_arguments_retain arguments_retain_loop Kstop empty_env
    (PTree.set _index(Vint(Int.repr(index+1)))temporaries)memory).
  { apply unchanged_store_edge,edge_skip_loop2. }
  exact REST.
Qed.

End ArgumentsPure.
