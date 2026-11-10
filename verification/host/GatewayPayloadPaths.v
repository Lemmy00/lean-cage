(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual bounded field guards select the same transfer call. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewayPrefix GatewayMemoryPrefixes
  GatewayFramedRuntime GatewayHeaderTransfer GatewayPayloadControl GatewayPayloadReturn GatewayPayloadSend GatewayReadonly.
Import ListNotations.
Open Scope Z_scope.

Definition payload_field_sequence:=match payload_body with Ssequence first _=>first|_=>Sskip end.
Definition payload_data_set:=match payload_field_sequence with Ssequence first _=>first|_=>Sskip end.
Definition payload_size_sequence:=match payload_field_sequence with Ssequence _ rest=>rest|_=>Sskip end.
Definition payload_size_set:=match payload_size_sequence with Ssequence first _=>first|_=>Sskip end.
Definition payload_transfer_call:=match payload_size_sequence with Ssequence _ rest=>rest|_=>Sskip end.
Definition payload_data_expression:=match payload_data_set with Sset _ expression=>expression|_=>Econst_int Int.zero tint end.
Definition payload_size_expression:=match payload_size_set with Sset _ expression=>expression|_=>Econst_int Int.zero tint end.
Definition payload_guard_temps temporaries:=PTree.set _t'31(Vint Int.one)temporaries.
Definition payload_data_temps(temporaries:temp_env)(pointer:val):=PTree.set _t'69 pointer temporaries.
Definition payload_call_temps temporaries pointer size:=PTree.set _t'70(Vlong size)(payload_data_temps temporaries pointer).
Definition payload_next_temps temporaries index:=PTree.set _index__1(Vint(Int.repr(Z.of_nat(S index))))
  (PTree.set _failed(Vint Int.zero)(PTree.set _t'32(Vint Int.zero)temporaries)).

Section Paths.
Context {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
  (property:mem->World->Prop)(CLOSED:gateway_ambient_closed backend property).
Variables(environment:env)(temporaries:temp_env)(memory:mem).

Ltac payload_same sink:=eapply gateway_memory_same with(following:=sink);[exact CLOSED|cbn;tauto| |].
Ltac payload_structure sink edge:=payload_same sink;[intros;apply unchanged_store_edge,edge|].

Lemma actual_payload_enter:
  gateway_memory_prefix backend ge
    (State f_host_exchange payload_loop payload_loop_cont environment(PTree.set _index__1(Vint Int.zero)temporaries)memory)
    property property(State f_host_exchange header_transfer_after Kstop environment temporaries memory).
Proof.
  payload_structure(State f_host_exchange payload_phase payload_loop_cont environment temporaries memory)edge_seq.
  payload_structure(State f_host_exchange(Sset _index__1(Econst_int Int.zero tint))(Kseq payload_loop payload_loop_cont)
    environment temporaries memory)edge_seq.
  payload_same(State f_host_exchange Sskip(Kseq payload_loop payload_loop_cont)environment
    (PTree.set _index__1(Vint Int.zero)temporaries)memory).
  - intros;apply certified_set_edge,old_expression_value;constructor.
  - payload_structure(State f_host_exchange payload_loop payload_loop_cont environment
      (PTree.set _index__1(Vint Int.zero)temporaries)memory)edge_skip_seq.
    apply gateway_memory_identity.
Qed.

Lemma actual_payload_guard_path index:
  (index<8)%nat->temporaries!_failed=Some(Vint Int.zero)->
  temporaries!_index__1=Some(Vint(Int.repr(Z.of_nat index)))->
  gateway_memory_prefix backend ge
    (State f_host_exchange payload_body payload_iteration_cont environment(payload_guard_temps temporaries)memory)
    property property(State f_host_exchange payload_loop payload_loop_cont environment temporaries memory).
Proof.
  intros BOUND FAILED INDEX.
  payload_structure(State f_host_exchange payload_iteration payload_iteration_cont environment temporaries memory)edge_loop.
  payload_structure(State f_host_exchange payload_guard(Kseq payload_body payload_iteration_cont)environment temporaries memory)edge_seq.
  payload_structure(State f_host_exchange payload_guard_select
    (Kseq payload_guard_test(Kseq payload_body payload_iteration_cont))environment temporaries memory)edge_seq.
  payload_same(State f_host_exchange(Sset _t'31(Ecast(Ebinop Olt(Etempvar _index__1 tuint)
    (Econst_int(Int.repr 8)tint)tint)tbool))
    (Kseq payload_guard_test(Kseq payload_body payload_iteration_cont))environment temporaries memory).
  - intros;apply certified_if_edge with(v:=Vint Int.one)(b:=true);
      [apply old_expression_value;WriteAll.expression|reflexivity].
  - payload_same(State f_host_exchange Sskip(Kseq payload_guard_test(Kseq payload_body payload_iteration_cont))
      environment(payload_guard_temps temporaries)memory).
    + intros;apply certified_set_edge;eapply cast_expression_value with(v:=Vint Int.one);[|reflexivity].
      eapply binary_expression_value;[apply old_expression_value,value_temp;exact INDEX|apply old_expression_value;constructor|].
      change(Some(Val.of_bool(Int.ltu(Int.repr(Z.of_nat index))(Int.repr 8)))=Some(Vint Int.one)).
      unfold Int.ltu;rewrite Int.unsigned_repr by(change Int.max_unsigned with 4294967295;lia).
      change(Int.unsigned(Int.repr 8))with 8;rewrite zlt_true by lia;reflexivity.
    + payload_structure(State f_host_exchange payload_guard_test(Kseq payload_body payload_iteration_cont)
        environment(payload_guard_temps temporaries)memory)edge_skip_seq.
      payload_same(State f_host_exchange Sskip(Kseq payload_body payload_iteration_cont)
        environment(payload_guard_temps temporaries)memory).
      * intros;apply certified_if_edge with(v:=Vint Int.one)(b:=true);
          [apply old_expression_value,value_temp;apply PTree.gss|reflexivity].
      * payload_structure(State f_host_exchange payload_body payload_iteration_cont
          environment(payload_guard_temps temporaries)memory)edge_skip_seq.
        apply gateway_memory_identity.
Qed.

Lemma actual_payload_fields_path pointer size:
  (forall memory world,property memory world->expression_value ge environment temporaries memory payload_data_expression pointer)->
  (forall memory world,property memory world->expression_value ge environment(payload_data_temps temporaries pointer)
    memory payload_size_expression(Vlong size))->
  gateway_memory_prefix backend ge
    (State f_host_exchange payload_transfer_call(Kseq payload_bind_failed payload_iteration_cont)
      environment(payload_call_temps temporaries pointer size)memory)property property
    (State f_host_exchange payload_body payload_iteration_cont environment temporaries memory).
Proof.
  intros DATA SIZE.
  payload_structure(State f_host_exchange payload_field_sequence(Kseq payload_bind_failed payload_iteration_cont)
    environment temporaries memory)edge_seq.
  payload_structure(State f_host_exchange payload_data_set(Kseq payload_size_sequence(Kseq payload_bind_failed payload_iteration_cont))
    environment temporaries memory)edge_seq.
  payload_same(State f_host_exchange Sskip(Kseq payload_size_sequence(Kseq payload_bind_failed payload_iteration_cont))
    environment(payload_data_temps temporaries pointer)memory).
  - intros available current GOOD;apply certified_set_edge;apply DATA with(world:=current);exact GOOD.
  - payload_structure(State f_host_exchange payload_size_sequence(Kseq payload_bind_failed payload_iteration_cont)
      environment(payload_data_temps temporaries pointer)memory)edge_skip_seq.
    payload_structure(State f_host_exchange payload_size_set(Kseq payload_transfer_call(Kseq payload_bind_failed payload_iteration_cont))
      environment(payload_data_temps temporaries pointer)memory)edge_seq.
    payload_same(State f_host_exchange Sskip(Kseq payload_transfer_call(Kseq payload_bind_failed payload_iteration_cont))
      environment(payload_call_temps temporaries pointer size)memory).
    + intros available current GOOD;apply certified_set_edge;apply SIZE with(world:=current);exact GOOD.
    + payload_structure(State f_host_exchange payload_transfer_call(Kseq payload_bind_failed payload_iteration_cont)
        environment(payload_call_temps temporaries pointer size)memory)edge_skip_seq.
      apply gateway_memory_identity.
Qed.

Lemma actual_payload_increment_path index:
  (index<8)%nat->temporaries!_index__1=Some(Vint(Int.repr(Z.of_nat index)))->
  gateway_memory_prefix backend ge
    (State f_host_exchange payload_loop payload_loop_cont environment(payload_next_temps temporaries index)memory)
    property property(State f_host_exchange Sskip(Kseq payload_bind_failed payload_iteration_cont)
      environment(PTree.set _t'32(Vint Int.zero)temporaries)memory).
Proof.
  intros BOUND INDEX.
  payload_structure(State f_host_exchange payload_bind_failed payload_iteration_cont
    environment(PTree.set _t'32(Vint Int.zero)temporaries)memory)edge_skip_seq.
  payload_same(State f_host_exchange Sskip payload_iteration_cont
    environment(PTree.set _failed(Vint Int.zero)(PTree.set _t'32(Vint Int.zero)temporaries))memory).
  - intros;apply certified_set_edge,old_expression_value,value_temp;apply PTree.gss.
  - payload_structure(State f_host_exchange payload_increment(Kloop2 payload_iteration payload_increment payload_loop_cont)
      environment(PTree.set _failed(Vint Int.zero)(PTree.set _t'32(Vint Int.zero)temporaries))memory)edge_skip_loop1.
    payload_same(State f_host_exchange Sskip(Kloop2 payload_iteration payload_increment payload_loop_cont)
      environment(payload_next_temps temporaries index)memory).
    + intros;apply certified_set_edge;eapply binary_expression_value.
      * apply old_expression_value,value_temp;rewrite !PTree.gso by discriminate;exact INDEX.
      * apply old_expression_value;constructor.
      * change(Some(Vint(Int.add(Int.repr(Z.of_nat index))Int.one))=Some(Vint(Int.repr(Z.of_nat(S index))))).
        unfold Int.add;rewrite Int.unsigned_repr by(change Int.max_unsigned with 4294967295;lia).
        change(Int.unsigned Int.one)with 1;rewrite Nat2Z.inj_succ;f_equal;f_equal;lia.
    + payload_structure(State f_host_exchange payload_loop payload_loop_cont
        environment(payload_next_temps temporaries index)memory)edge_skip_loop2.
      apply gateway_memory_identity.
Qed.
End Paths.

Lemma actual_payload_transfer_call ge environment temporaries memory stream pointer size:
  environment!_stream=Some(stream,Tstruct _host_stream noattr)->environment!_host_transfer=None->
  gateway_function_binding ge _host_transfer(Internal f_host_transfer)->
  temporaries!_t'69=Some pointer->temporaries!_t'70=Some(Vlong size)->
  sem_cast pointer(tptr tschar)(tptr tvoid)memory=Some pointer->
  store_edge ge(State f_host_exchange payload_transfer_call(Kseq payload_bind_failed payload_iteration_cont)
    environment temporaries memory)
    (Callstate(Internal f_host_transfer)(payload_transfer_arguments stream pointer size)(payload_transfer_cont environment temporaries)memory).
Proof.
  intros STREAM LOCAL[symbol[SYMBOL FUNCTION]]DATA SIZE CAST.
  eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value;eapply value_function;[exact LOCAL|exact SYMBOL|reflexivity].
  - eapply cons_argument_values with(v:=Vptr stream Ptrofs.zero).
    + apply local_address_expression;exact STREAM.
    + reflexivity.
    + eapply cons_argument_values with(v:=pointer).
      * eapply cast_expression_value;[apply old_expression_value,value_temp;exact DATA|exact CAST].
      * destruct pointer;try discriminate CAST;reflexivity.
      * eapply cons_argument_values with(v:=Vlong size);
          [apply old_expression_value,value_temp;exact SIZE|reflexivity|].
        eapply cons_argument_values with(v:=Vint Int.one);
          [apply old_expression_value;constructor|reflexivity|apply no_argument_values].
  - cbn;exact FUNCTION.
  - reflexivity.
Qed.
