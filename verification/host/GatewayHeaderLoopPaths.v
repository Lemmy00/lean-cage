(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: All eight descriptor iterations retain the real caller control. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayMemoryPrefixes GatewayFramedRuntime
  GatewayHeaderInitialization GatewayHeaderFields GatewayHeaderExpression GatewayReadonly.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Definition header_kind_temps temporaries kind:=PTree.set _t'72(Vint kind)temporaries.
Definition header_size_temps temporaries size:=PTree.set _t'71(Vlong size)temporaries.
Definition header_next_temps temporaries index:=PTree.set _index(Vint(Int.repr(Z.of_nat(S index))))temporaries.

Section Paths.
Context {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
  (property:mem->World->Prop)(CLOSED:gateway_ambient_closed backend property).
Variables(environment:env)(temporaries:temp_env)(memory:mem).

Ltac header_same sink:=
  eapply gateway_memory_same with(following:=sink);
    [exact CLOSED|cbn;tauto| |].
Ltac header_struct sink edge:=header_same sink;
  [intros;apply unchanged_store_edge;apply edge|].

Lemma actual_header_fields_enter:
  gateway_memory_prefix backend ge
    (State f_host_exchange header_fields_loop(Kseq header_fields_after Kstop)environment
      (PTree.set _index(Vint Int.zero)temporaries)memory)property property
    (State f_host_exchange(header_source_after 114)Kstop environment temporaries memory).
Proof.
  header_struct(State f_host_exchange header_fields_sequence(Kseq header_fields_after Kstop)
    environment temporaries memory)edge_seq.
  header_struct(State f_host_exchange(Sset _index(Econst_int Int.zero tint))
    (Kseq header_fields_loop(Kseq header_fields_after Kstop))environment temporaries memory)edge_seq.
  header_same(State f_host_exchange Sskip(Kseq header_fields_loop(Kseq header_fields_after Kstop))
    environment(PTree.set _index(Vint Int.zero)temporaries)memory).
  - intros;apply certified_set_edge,old_expression_value;constructor.
  - header_struct(State f_host_exchange header_fields_loop(Kseq header_fields_after Kstop)
      environment(PTree.set _index(Vint Int.zero)temporaries)memory)edge_skip_seq.
    apply gateway_memory_identity.
Qed.

Lemma actual_header_kind_path index kind:
  (index<8)%nat->temporaries!_index=Some(Vint(Int.repr(Z.of_nat index)))->
  (forall memory world,property memory world->
    expression_value ge environment temporaries memory header_fields_kind_expr(Vint kind))->
  gateway_memory_prefix backend ge
    (State f_host_exchange header_fields_kind_call(Kseq header_fields_size header_fields_cont)
      environment(header_kind_temps temporaries kind)memory)property property
    (State f_host_exchange header_fields_loop(Kseq header_fields_after Kstop)environment temporaries memory).
Proof.
  intros BOUND INDEX KIND.
  header_struct(State f_host_exchange header_fields_iteration header_fields_cont environment temporaries memory)edge_loop.
  header_struct(State f_host_exchange(Sifthenelse header_fields_test Sskip Sbreak)
    (Kseq header_fields_body header_fields_cont)environment temporaries memory)edge_seq.
  header_same(State f_host_exchange Sskip(Kseq header_fields_body header_fields_cont)environment temporaries memory).
  - intros available current GOOD;apply certified_if_edge with(v:=Vint Int.one)(b:=true).
    + unfold header_fields_test;eapply binary_expression_value;
        [apply old_expression_value,value_temp;exact INDEX|apply old_expression_value;constructor|].
      change(Some(Val.of_bool(Int.ltu(Int.repr(Z.of_nat index))(Int.repr 8)))=Some(Vint Int.one)).
      unfold Int.ltu;rewrite Int.unsigned_repr by(change Int.max_unsigned with 4294967295;lia).
      change(Int.unsigned(Int.repr 8))with 8;rewrite zlt_true by lia;reflexivity.
    + reflexivity.
  - header_struct(State f_host_exchange header_fields_body header_fields_cont environment temporaries memory)edge_skip_seq.
    header_struct(State f_host_exchange header_fields_kind(Kseq header_fields_size header_fields_cont)
      environment temporaries memory)edge_seq.
    header_struct(State f_host_exchange(Sset _t'72 header_fields_kind_expr)
      (Kseq header_fields_kind_call(Kseq header_fields_size header_fields_cont))environment temporaries memory)edge_seq.
    header_same(State f_host_exchange Sskip(Kseq header_fields_kind_call(Kseq header_fields_size header_fields_cont))
      environment(header_kind_temps temporaries kind)memory).
    + intros available current GOOD;apply certified_set_edge;apply KIND with(world:=current);exact GOOD.
    + header_struct(State f_host_exchange header_fields_kind_call(Kseq header_fields_size header_fields_cont)
        environment(header_kind_temps temporaries kind)memory)edge_skip_seq.
      apply gateway_memory_identity.
Qed.

Lemma actual_header_size_path size:
  (forall memory world,property memory world->
    expression_value ge environment temporaries memory header_fields_size_expr(Vlong size))->
  gateway_memory_prefix backend ge
    (State f_host_exchange header_fields_size_call header_fields_cont environment(header_size_temps temporaries size)memory)
    property property
    (State f_host_exchange Sskip(Kseq header_fields_size header_fields_cont)environment temporaries memory).
Proof.
  intro SIZE.
  header_struct(State f_host_exchange header_fields_size header_fields_cont environment temporaries memory)edge_skip_seq.
  header_struct(State f_host_exchange(Sset _t'71 header_fields_size_expr)(Kseq header_fields_size_call header_fields_cont)
    environment temporaries memory)edge_seq.
  header_same(State f_host_exchange Sskip(Kseq header_fields_size_call header_fields_cont)
    environment(header_size_temps temporaries size)memory).
  - intros available current GOOD;apply certified_set_edge;apply SIZE with(world:=current);exact GOOD.
  - header_struct(State f_host_exchange header_fields_size_call header_fields_cont
      environment(header_size_temps temporaries size)memory)edge_skip_seq.
    apply gateway_memory_identity.
Qed.

Lemma actual_header_increment_path index:
  (index<8)%nat->temporaries!_index=Some(Vint(Int.repr(Z.of_nat index)))->
  gateway_memory_prefix backend ge
    (State f_host_exchange header_fields_loop(Kseq header_fields_after Kstop)
      environment(header_next_temps temporaries index)memory)property property
    (State f_host_exchange Sskip header_fields_cont environment temporaries memory).
Proof.
  intros BOUND INDEX.
  header_struct(State f_host_exchange header_fields_increment
    (Kloop2 header_fields_iteration header_fields_increment(Kseq header_fields_after Kstop))environment temporaries memory)edge_skip_loop1.
  header_same(State f_host_exchange Sskip(Kloop2 header_fields_iteration header_fields_increment(Kseq header_fields_after Kstop))
    environment(header_next_temps temporaries index)memory).
  - intros available current GOOD;apply certified_set_edge;eapply binary_expression_value;
      [apply old_expression_value,value_temp;exact INDEX|apply old_expression_value;constructor|].
    change(Some(Vint(Int.add(Int.repr(Z.of_nat index))Int.one))=Some(Vint(Int.repr(Z.of_nat(S index))))).
    unfold Int.add;rewrite Int.unsigned_repr by(change Int.max_unsigned with 4294967295;lia).
    change(Int.unsigned Int.one)with 1;rewrite Nat2Z.inj_succ;f_equal;f_equal;lia.
  - header_struct(State f_host_exchange header_fields_loop(Kseq header_fields_after Kstop)
      environment(header_next_temps temporaries index)memory)edge_skip_loop2.
    apply gateway_memory_identity.
Qed.

Lemma actual_header_fields_exit:
  temporaries!_index=Some(Vint(Int.repr 8))->
  gateway_memory_prefix backend ge(State f_host_exchange header_fields_after Kstop environment temporaries memory)property property
    (State f_host_exchange header_fields_loop(Kseq header_fields_after Kstop)environment temporaries memory).
Proof.
  intro INDEX.
  header_struct(State f_host_exchange header_fields_iteration header_fields_cont environment temporaries memory)edge_loop.
  header_struct(State f_host_exchange(Sifthenelse header_fields_test Sskip Sbreak)
    (Kseq header_fields_body header_fields_cont)environment temporaries memory)edge_seq.
  header_same(State f_host_exchange Sbreak(Kseq header_fields_body header_fields_cont)environment temporaries memory).
  - intros available current GOOD;apply certified_if_edge with(v:=Vint Int.zero)(b:=false).
    + unfold header_fields_test;eapply binary_expression_value;
        [apply old_expression_value,value_temp;exact INDEX|apply old_expression_value;constructor|reflexivity].
    + reflexivity.
  - header_struct(State f_host_exchange Sbreak header_fields_cont environment temporaries memory)edge_break_seq.
    header_struct(State f_host_exchange Sskip(Kseq header_fields_after Kstop)environment temporaries memory)edge_break_loop1.
    header_struct(State f_host_exchange header_fields_after Kstop environment temporaries memory)edge_skip_seq.
    apply gateway_memory_identity.
Qed.
End Paths.
