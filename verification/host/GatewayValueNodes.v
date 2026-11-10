(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual stream-node exhaustion selects the decoder's NULL-return branch. *)
From Stdlib Require Import ZArith Lia List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayFrames GatewayPure GatewaySourceCuts
  GatewayFramedRuntime GatewayValueEntry GatewayValueGuards GatewayFailurePaths GatewayStreamInterface
  GatewayStreamAccess GatewayStreamLayout.
Import ListNotations.
Open Scope Z_scope.

Lemma gateway_value_positive_depth_expression ge environment temporaries memory depth :
  temporaries!_depth=Some(Vint depth) ->depth<>Int.zero ->
  expression_value ge environment temporaries memory(Eunop Onotbool(Etempvar _depth tuint)tint)(Vint Int.zero).
Proof.
  intros DEPTH NONZERO;apply old_expression_value;eapply value_unary;[apply value_temp;exact DEPTH|].
  cbn;rewrite Int.eq_false by exact NONZERO;reflexivity.
Qed.

Definition gateway_value_node_read:=
  Sset _t'96(stream_member _nodes tulong).
Definition gateway_value_node_zero:=
  Sset _t'1(Ecast(Eunop Onotbool(Etempvar _t'96 tulong)tint)tbool).

Lemma gateway_value_depth_check_nodes :gateway_value_depth_check=
  Sifthenelse(Eunop Onotbool(Etempvar _depth tuint)tint)
    (Sset _t'1(Econst_int Int.one tint))
    (Ssequence gateway_value_node_read gateway_value_node_zero).
Proof. reflexivity. Qed.

Theorem gateway_value_zero_nodes_fails {World Event}(backend:gateway_backend World Event)ge
    (property:mem->World->Prop)slots arguments memory stream_block stream_offset :
  gateway_ambient_closed backend property ->gateway_value_depth arguments<>Int.zero ->
  gateway_value_stream arguments=Vptr stream_block stream_offset ->stream_member_layout ge _nodes 32 ->
  (forall memory world,property memory world->
    Mem.loadv Mint64 memory(gateway_stream_slot stream_block stream_offset 32)=Some(Vlong Int64.zero)) ->
  gateway_failure_when backend ge property(State f_host_value(fn_body f_host_value)Kstop
    (gateway_value_environment slots)(gateway_value_parameters arguments)memory).
Proof.
  intros CLOSED DEPTH STREAM LAYOUT CELLS;rewrite gateway_value_body_guard_shape.
  eapply gateway_failure_when_same with(target:=State f_host_value
    (Ssequence gateway_value_depth_check gateway_value_guard)(Kseq gateway_value_after_check Kstop)
    (gateway_value_environment slots)(gateway_value_parameters arguments)memory).
  - exact CLOSED.
  - cbn;tauto.
  - intros;apply unchanged_store_edge,edge_seq.
  - eapply gateway_failure_when_same with(target:=State f_host_value gateway_value_depth_check
      (Kseq gateway_value_guard(Kseq gateway_value_after_check Kstop))
      (gateway_value_environment slots)(gateway_value_parameters arguments)memory).
    + exact CLOSED.
    + cbn;tauto.
    + intros;apply unchanged_store_edge,edge_seq.
    + rewrite gateway_value_depth_check_nodes.
      eapply gateway_failure_when_same with(target:=State f_host_value
        (Ssequence gateway_value_node_read gateway_value_node_zero)
        (Kseq gateway_value_guard(Kseq gateway_value_after_check Kstop))
        (gateway_value_environment slots)(gateway_value_parameters arguments)memory).
      * exact CLOSED.
      * cbn;tauto.
      * intros;eapply certified_if_edge with(b:=false).
        -- eapply gateway_value_positive_depth_expression;[unfold gateway_value_parameters;apply PTree.gss|exact DEPTH].
        -- reflexivity.
      * eapply gateway_failure_when_same with(target:=State f_host_value gateway_value_node_read
          (Kseq gateway_value_node_zero(Kseq gateway_value_guard(Kseq gateway_value_after_check Kstop)))
          (gateway_value_environment slots)(gateway_value_parameters arguments)memory).
        -- exact CLOSED.
        -- cbn;tauto.
        -- intros;apply unchanged_store_edge,edge_seq.
        -- eapply gateway_failure_when_same with(target:=State f_host_value Sskip
            (Kseq gateway_value_node_zero(Kseq gateway_value_guard(Kseq gateway_value_after_check Kstop)))
            (gateway_value_environment slots)
            (PTree.set _t'96(Vlong Int64.zero)(gateway_value_parameters arguments))memory).
           ++ exact CLOSED.
           ++ cbn;tauto.
           ++ intros current world GOOD;apply certified_set_edge.
              eapply actual_stream_member_read with(delta:=32)(chunk:=Mint64).
              ** unfold gateway_value_parameters;rewrite PTree.gso by discriminate.
                 rewrite PTree.gss;f_equal;exact STREAM.
              ** exact LAYOUT.
              ** reflexivity.
              ** apply CELLS with(world:=world);exact GOOD.
           ++ eapply gateway_failure_when_same with(target:=State f_host_value gateway_value_node_zero
                (Kseq gateway_value_guard(Kseq gateway_value_after_check Kstop))(gateway_value_environment slots)
                (PTree.set _t'96(Vlong Int64.zero)(gateway_value_parameters arguments))memory).
              ** exact CLOSED.
              ** cbn;tauto.
              ** intros;apply unchanged_store_edge,edge_skip_seq.
              ** eapply gateway_failure_when_same with(target:=State f_host_value Sskip
                   (Kseq gateway_value_guard(Kseq gateway_value_after_check Kstop))(gateway_value_environment slots)
                   (PTree.set _t'1(Vint Int.one)
                     (PTree.set _t'96(Vlong Int64.zero)(gateway_value_parameters arguments)))memory).
                 --- exact CLOSED.
                 --- cbn;tauto.
                 --- intros;apply certified_set_edge,old_expression_value.
                     eapply value_cast;[eapply value_unary;[apply value_temp;apply PTree.gss|reflexivity]|reflexivity].
                 --- eapply gateway_failure_when_same with(target:=State f_host_value gateway_value_guard
                      (Kseq gateway_value_after_check Kstop)(gateway_value_environment slots)
                      (PTree.set _t'1(Vint Int.one)
                        (PTree.set _t'96(Vlong Int64.zero)(gateway_value_parameters arguments)))memory).
                     +++ exact CLOSED.
                     +++ cbn;tauto.
                     +++ intros;apply unchanged_store_edge,edge_skip_seq.
                     +++ eapply gateway_failure_when_same with(target:=State f_host_value gateway_value_guard_failure
                          (Kseq gateway_value_after_check Kstop)(gateway_value_environment slots)
                          (PTree.set _t'1(Vint Int.one)
                            (PTree.set _t'96(Vlong Int64.zero)(gateway_value_parameters arguments)))memory).
                         *** exact CLOSED.
                         *** cbn;tauto.
                         *** intros;eapply certified_if_edge with(b:=true).
                             ---- apply old_expression_value,value_temp;apply PTree.gss.
                             ---- reflexivity.
                         *** apply gateway_failure_when_selected,gateway_failure_selected.
                             ---- exact gateway_value_pointer_return.
                             ---- exact gateway_value_guard_failure_profile.
                             ---- reflexivity.
Qed.
