(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The real field counter reaches exactly eight before shutdown. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From HostGateway Require Import GatewaySource GatewayMachine GatewayMemoryPrefixes GatewayFramedRuntime GatewayReadonly
  GatewayPayloadControl GatewayExchangeTransport GatewayPayloadPaths.
Import ListNotations.
Open Scope Z_scope.

Definition payload_exit_temps(temporaries:temp_env):=PTree.set _t'31(Vint Int.zero)temporaries.
Definition gateway_payload_temps_frame(before after:temp_env):Prop:=forall identifier,
  identifier<>_index__1->identifier<>_failed->identifier<>_t'31->identifier<>_t'32->identifier<>_t'69->identifier<>_t'70->
  after!identifier=before!identifier.

Section Exit.
Context {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
  (property:mem->World->Prop)(CLOSED:gateway_ambient_closed backend property).
Variables(environment:env)(temporaries:temp_env)(memory:mem).

Ltac payload_exit_same sink:=eapply gateway_memory_same with(following:=sink);[exact CLOSED|cbn;tauto| |].
Ltac payload_exit_structure sink edge:=payload_exit_same sink;[intros;apply unchanged_store_edge,edge|].

Theorem actual_payload_exit_path:
  temporaries!_failed=Some(Vint Int.zero)->temporaries!_index__1=Some(Vint(Int.repr 8))->
  gateway_memory_prefix backend ge
    (State f_host_exchange(exchange_transport_after 1)Kstop environment(payload_exit_temps temporaries)memory)
    property property(State f_host_exchange payload_loop payload_loop_cont environment temporaries memory).
Proof.
  intros FAILED INDEX.
  payload_exit_structure(State f_host_exchange payload_iteration payload_iteration_cont environment temporaries memory)edge_loop.
  payload_exit_structure(State f_host_exchange payload_guard(Kseq payload_body payload_iteration_cont)
    environment temporaries memory)edge_seq.
  payload_exit_structure(State f_host_exchange payload_guard_select
    (Kseq payload_guard_test(Kseq payload_body payload_iteration_cont))environment temporaries memory)edge_seq.
  payload_exit_same(State f_host_exchange(Sset _t'31(Ecast(Ebinop Olt(Etempvar _index__1 tuint)
    (Econst_int(Int.repr 8)tint)tint)tbool))
    (Kseq payload_guard_test(Kseq payload_body payload_iteration_cont))environment temporaries memory).
  - intros;apply certified_if_edge with(v:=Vint Int.one)(b:=true);
      [apply old_expression_value;WriteAll.expression|reflexivity].
  - payload_exit_same(State f_host_exchange Sskip(Kseq payload_guard_test(Kseq payload_body payload_iteration_cont))
      environment(payload_exit_temps temporaries)memory).
    + intros;apply certified_set_edge;eapply cast_expression_value with(v:=Vint Int.zero);[|reflexivity].
      eapply binary_expression_value;
        [apply old_expression_value,value_temp;exact INDEX|apply old_expression_value;constructor|reflexivity].
    + payload_exit_structure(State f_host_exchange payload_guard_test(Kseq payload_body payload_iteration_cont)
        environment(payload_exit_temps temporaries)memory)edge_skip_seq.
      payload_exit_same(State f_host_exchange Sbreak(Kseq payload_body payload_iteration_cont)
        environment(payload_exit_temps temporaries)memory).
      * intros;apply certified_if_edge with(v:=Vint Int.zero)(b:=false);
          [apply old_expression_value,value_temp;apply PTree.gss|reflexivity].
      * payload_exit_structure(State f_host_exchange Sbreak payload_iteration_cont
          environment(payload_exit_temps temporaries)memory)edge_break_seq.
        payload_exit_structure(State f_host_exchange Sskip payload_loop_cont
          environment(payload_exit_temps temporaries)memory)edge_break_loop1.
        payload_exit_structure(State f_host_exchange(exchange_transport_after 1)Kstop
          environment(payload_exit_temps temporaries)memory)edge_skip_seq.
        apply gateway_memory_identity.
Qed.
End Exit.
