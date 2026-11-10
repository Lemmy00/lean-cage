(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A successful decoder debits its actual node cell before its first byte read. *)
From Stdlib Require Import ZArith Lia List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayFrames GatewayPure GatewayValueEntry
  GatewayValueGuards GatewayValueNodes GatewayValueNodeMemory GatewayValueContext GatewayStreamInterface
  GatewayStreamMemory GatewayStreamAccess GatewayStreamLayout GatewayStreamWord GatewaySourcePaths
  GatewaySourceCuts GatewayThreadRuntime GatewayFramedRuntime GatewayPrefix.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_value_node_debit_statement:=
  match gateway_value_after_check with Ssequence first _=>first|_=>Sskip end.
Definition gateway_value_after_node_debit:=
  match gateway_value_after_check with Ssequence _ rest=>rest|_=>Sskip end.
Definition gateway_value_tag_read:=
  match gateway_value_after_node_debit with Ssequence(Ssequence first _) _=>first|_=>Sskip end.
Definition gateway_value_tag_guard:=
  match gateway_value_after_node_debit with Ssequence(Ssequence _ second) _=>second|_=>Sskip end.
Definition gateway_value_after_tag:=
  match gateway_value_after_node_debit with Ssequence _ rest=>rest|_=>Sskip end.

Definition gateway_value_checked_parameters arguments initial:=
  PTree.set _t'1(Vint Int.zero)(PTree.set _t'96(Vlong(stream_nodes initial))(gateway_value_parameters arguments)).
Definition gateway_value_debited_parameters arguments initial:=
  PTree.set _t'94(Vlong(stream_nodes initial))(gateway_value_checked_parameters arguments initial).
Definition gateway_value_tag_arguments slots arguments :gateway_word_arguments:={|
  word_stream:=gateway_value_stream arguments;word_width:=Int.one;
  word_output:=Vptr(gateway_value_tag_slot slots)Ptrofs.zero|}.
Definition gateway_value_tag_cont slots arguments initial:=
  Kcall(Some _t'2)f_host_value(gateway_value_environment slots)(gateway_value_debited_parameters arguments initial)
    (Kseq gateway_value_tag_guard(Kseq gateway_value_after_tag Kstop)).

Lemma gateway_value_after_check_shape :gateway_value_after_check=
  Ssequence gateway_value_node_debit_statement gateway_value_after_node_debit.
Proof. reflexivity. Qed.
Lemma gateway_value_after_debit_shape :gateway_value_after_node_debit=
  Ssequence(Ssequence gateway_value_tag_read gateway_value_tag_guard)gateway_value_after_tag.
Proof. reflexivity. Qed.
Lemma gateway_value_node_debit_shape :gateway_value_node_debit_statement=
  Ssequence(Sset _t'94(stream_member _nodes tulong))
    (Sassign(stream_member _nodes tulong)
      (Ebinop Osub(Etempvar _t'94 tulong)(Econst_int Int.one tint)tulong)).
Proof. reflexivity. Qed.

Section ValueTag.
Context {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
  (io:Event->option gateway_native_io)(native:World->block->Prop)(stable:World->block->Z->Prop)
  (discipline:option val->mem->World->Prop)(thread_errno:World->int).
Context(runtime:gateway_thread_runtime backend io native stable discipline thread_errno).

Lemma gateway_value_allocated_nodes slots stream_block stream_offset initial readonly original memory world :
  gateway_value_allocated native stable discipline slots stream_block stream_offset initial readonly original memory world ->
  Mem.loadv Mint64 memory(gateway_stream_slot stream_block stream_offset 32)=Some(Vlong(stream_nodes initial)).
Proof.
  intros[[SIDE[PRIVATE[READONLY[INPUT FRAME]]]]REST].
  destruct(gateway_value_stream_cells _ _ _ _ _ INPUT)as(A &B &C &D &E &F &G &H);exact G.
Qed.

Lemma gateway_value_node_nonzero_expression environment temporaries memory initial :
  temporaries!_t'96=Some(Vlong(stream_nodes initial)) ->stream_nodes initial<>Int64.zero ->
  expression_value ge environment temporaries memory
    (Ecast(Eunop Onotbool(Etempvar _t'96 tulong)tint)tbool)(Vint Int.zero).
Proof.
  intros TEMP NONZERO;apply old_expression_value;eapply value_cast.
  - eapply value_unary;[apply value_temp;exact TEMP|]. cbn;rewrite Int64.eq_false by exact NONZERO;reflexivity.
  - reflexivity.
Qed.

Theorem gateway_value_body_tag_path slots arguments memory stream_block stream_offset initial readonly original symbol :
  gateway_value_depth arguments<>Int.zero ->stream_nodes initial<>Int64.zero ->
  gateway_value_stream arguments=Vptr stream_block stream_offset ->stream_member_layout ge _nodes 32 ->
  Genv.find_symbol ge _host_word=Some symbol ->Genv.find_funct_ptr ge symbol=Some(Internal f_host_word) ->
  gateway_source_path backend ge(Internal f_host_word)(gateway_word_values(gateway_value_tag_arguments slots arguments))
    (gateway_value_tag_cont slots arguments initial)
    (gateway_value_allocated native stable discipline slots stream_block stream_offset initial readonly original)
    (State f_host_value(fn_body f_host_value)Kstop(gateway_value_environment slots)(gateway_value_parameters arguments)memory)
    (gateway_value_allocated native stable discipline slots stream_block stream_offset
      (gateway_stream_node_debit initial)readonly original).
Proof.
  intros DEPTH NODES STREAM LAYOUT SYMBOL FUNCTION.
  set(before_property:=gateway_value_allocated native stable discipline slots stream_block stream_offset initial readonly original).
  set(after_property:=gateway_value_allocated native stable discipline slots stream_block stream_offset
    (gateway_stream_node_debit initial)readonly original).
  assert(BEFORE_CLOSED:gateway_ambient_closed backend before_property).
  { eapply gateway_value_allocated_ambient;exact runtime. }
  assert(AFTER_CLOSED:gateway_ambient_closed backend after_property).
  { eapply gateway_value_allocated_ambient;exact runtime. }
  rewrite gateway_value_body_guard_shape.
  eapply gateway_source_same with(target:=State f_host_value
    (Ssequence gateway_value_depth_check gateway_value_guard)(Kseq gateway_value_after_check Kstop)
    (gateway_value_environment slots)(gateway_value_parameters arguments)memory);
    [exact BEFORE_CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  eapply gateway_source_same with(target:=State f_host_value gateway_value_depth_check
    (Kseq gateway_value_guard(Kseq gateway_value_after_check Kstop))
    (gateway_value_environment slots)(gateway_value_parameters arguments)memory);
    [exact BEFORE_CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
  rewrite gateway_value_depth_check_nodes.
  eapply gateway_source_same with(target:=State f_host_value(Ssequence gateway_value_node_read gateway_value_node_zero)
    (Kseq gateway_value_guard(Kseq gateway_value_after_check Kstop))
    (gateway_value_environment slots)(gateway_value_parameters arguments)memory).
  - exact BEFORE_CLOSED.
  - cbn;tauto.
  - intros;eapply certified_if_edge with(b:=false).
    + eapply gateway_value_positive_depth_expression;[unfold gateway_value_parameters;apply PTree.gss|exact DEPTH].
    + reflexivity.
  - eapply gateway_source_same with(target:=State f_host_value gateway_value_node_read
      (Kseq gateway_value_node_zero(Kseq gateway_value_guard(Kseq gateway_value_after_check Kstop)))
      (gateway_value_environment slots)(gateway_value_parameters arguments)memory);
      [exact BEFORE_CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
    eapply gateway_source_same with(target:=State f_host_value Sskip
      (Kseq gateway_value_node_zero(Kseq gateway_value_guard(Kseq gateway_value_after_check Kstop)))
      (gateway_value_environment slots)
      (PTree.set _t'96(Vlong(stream_nodes initial))(gateway_value_parameters arguments))memory).
    + exact BEFORE_CLOSED.
    + cbn;tauto.
    + intros current world GOOD;apply certified_set_edge.
      eapply actual_stream_member_read with(delta:=32)(chunk:=Mint64).
      * unfold gateway_value_parameters;rewrite PTree.gso by discriminate;rewrite PTree.gss;f_equal;exact STREAM.
      * exact LAYOUT.
      * reflexivity.
      * eapply gateway_value_allocated_nodes;exact GOOD.
    + eapply gateway_source_same with(target:=State f_host_value gateway_value_node_zero
        (Kseq gateway_value_guard(Kseq gateway_value_after_check Kstop))(gateway_value_environment slots)
        (PTree.set _t'96(Vlong(stream_nodes initial))(gateway_value_parameters arguments))memory);
        [exact BEFORE_CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
      eapply gateway_source_same with(target:=State f_host_value Sskip
        (Kseq gateway_value_guard(Kseq gateway_value_after_check Kstop))(gateway_value_environment slots)
        (gateway_value_checked_parameters arguments initial)memory).
      * exact BEFORE_CLOSED.
      * cbn;tauto.
      * intros;apply certified_set_edge;eapply gateway_value_node_nonzero_expression;[apply PTree.gss|exact NODES].
      * eapply gateway_source_same with(target:=State f_host_value gateway_value_guard
          (Kseq gateway_value_after_check Kstop)(gateway_value_environment slots)
          (gateway_value_checked_parameters arguments initial)memory);
          [exact BEFORE_CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
        eapply gateway_source_same with(target:=State f_host_value Sskip
          (Kseq gateway_value_after_check Kstop)(gateway_value_environment slots)
          (gateway_value_checked_parameters arguments initial)memory).
        -- exact BEFORE_CLOSED.
        -- cbn;tauto.
        -- intros;eapply certified_if_edge with(b:=false).
           ++ apply old_expression_value,value_temp;apply PTree.gss.
           ++ reflexivity.
        -- eapply gateway_source_same with(target:=State f_host_value gateway_value_after_check Kstop
             (gateway_value_environment slots)(gateway_value_checked_parameters arguments initial)memory);
             [exact BEFORE_CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
           rewrite gateway_value_after_check_shape.
           eapply gateway_source_same with(target:=State f_host_value gateway_value_node_debit_statement
             (Kseq gateway_value_after_node_debit Kstop)(gateway_value_environment slots)
             (gateway_value_checked_parameters arguments initial)memory);
             [exact BEFORE_CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
           rewrite gateway_value_node_debit_shape.
           eapply gateway_source_same with(target:=State f_host_value(Sset _t'94(stream_member _nodes tulong))
             (Kseq(Sassign(stream_member _nodes tulong)
               (Ebinop Osub(Etempvar _t'94 tulong)(Econst_int Int.one tint)tulong))
               (Kseq gateway_value_after_node_debit Kstop))(gateway_value_environment slots)
             (gateway_value_checked_parameters arguments initial)memory);
             [exact BEFORE_CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
           eapply gateway_source_same with(target:=State f_host_value Sskip
             (Kseq(Sassign(stream_member _nodes tulong)
               (Ebinop Osub(Etempvar _t'94 tulong)(Econst_int Int.one tint)tulong))
               (Kseq gateway_value_after_node_debit Kstop))(gateway_value_environment slots)
             (gateway_value_debited_parameters arguments initial)memory).
           ++ exact BEFORE_CLOSED.
           ++ cbn;tauto.
           ++ intros current world GOOD;apply certified_set_edge.
              eapply actual_stream_member_read with(delta:=32)(chunk:=Mint64).
              ** unfold gateway_value_checked_parameters,gateway_value_parameters;
                   repeat rewrite PTree.gso by discriminate;rewrite PTree.gss;f_equal;exact STREAM.
              ** exact LAYOUT.
              ** reflexivity.
              ** eapply gateway_value_allocated_nodes;exact GOOD.
           ++ eapply gateway_source_same with(target:=State f_host_value
                (Sassign(stream_member _nodes tulong)
                  (Ebinop Osub(Etempvar _t'94 tulong)(Econst_int Int.one tint)tulong))
                (Kseq gateway_value_after_node_debit Kstop)(gateway_value_environment slots)
                (gateway_value_debited_parameters arguments initial)memory);
                [exact BEFORE_CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
              eapply gateway_source_next with(target:=State f_host_value Sskip
                (Kseq gateway_value_after_node_debit Kstop)(gateway_value_environment slots)
                (gateway_value_debited_parameters arguments initial)memory)(middle:=after_property).
              ** exact BEFORE_CLOSED.
              ** cbn;tauto.
              ** intros current world GOOD.
                 destruct GOOD as[CONTEXT REST];pose proof CONTEXT as[SIDE[PRIVATE[READONLY[INPUT FRAME]]]].
                 destruct(gateway_value_node_allocate _ _ _ _ _ INPUT)as[stored STORE].
                 exists stored;split.
                 --- eapply actual_stream_member_store with(delta:=32)(chunk:=Mint64)
                       (value:=Vlong(Int64.sub(stream_nodes initial)Int64.one)).
                     +++ unfold gateway_value_debited_parameters,gateway_value_checked_parameters,gateway_value_parameters;
                           repeat rewrite PTree.gso by discriminate;rewrite PTree.gss;f_equal;exact STREAM.
                     +++ exact LAYOUT.
                     +++ reflexivity.
                     +++ apply old_expression_value;eapply value_binary;[apply value_temp;apply PTree.gss|constructor|reflexivity].
                     +++ reflexivity.
                     +++ unfold gateway_stream_slot,Mem.storev.
                         rewrite(gateway_stream_slot_unsigned stream_offset 32 ltac:(lia)
                           (gateway_value_stream_bounds _ _ _ _ _ INPUT)).
                         rewrite zle_true by(pose proof(gateway_value_stream_bounds _ _ _ _ _ INPUT);cbn[size_chunk];lia).
                         exact STORE.
                 --- eapply gateway_value_allocated_node_store;[exact runtime|split;eassumption|exact STORE].
              ** eapply gateway_source_same with(target:=State f_host_value gateway_value_after_node_debit Kstop
                   (gateway_value_environment slots)(gateway_value_debited_parameters arguments initial)memory);
                   [exact AFTER_CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
                 rewrite gateway_value_after_debit_shape.
                 eapply gateway_source_same with(target:=State f_host_value
                   (Ssequence gateway_value_tag_read gateway_value_tag_guard)(Kseq gateway_value_after_tag Kstop)
                   (gateway_value_environment slots)(gateway_value_debited_parameters arguments initial)memory);
                   [exact AFTER_CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
                 eapply gateway_source_same with(target:=State f_host_value gateway_value_tag_read
                   (Kseq gateway_value_tag_guard(Kseq gateway_value_after_tag Kstop))
                   (gateway_value_environment slots)(gateway_value_debited_parameters arguments initial)memory);
                   [exact AFTER_CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
                 eapply gateway_source_same with(target:=Callstate(Internal f_host_word)
                   (gateway_word_values(gateway_value_tag_arguments slots arguments))
                   (gateway_value_tag_cont slots arguments initial)memory).
                 --- exact AFTER_CLOSED.
                 --- cbn;tauto.
                 --- intros current world GOOD;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
                     +++ reflexivity.
                     +++ apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
                     +++ apply cons_argument_values with(v:=gateway_value_stream arguments).
                         *** apply old_expression_value,value_temp.
                             unfold gateway_value_debited_parameters,gateway_value_checked_parameters,gateway_value_parameters;
                               repeat rewrite PTree.gso by discriminate;apply PTree.gss.
                         *** cbn[gateway_value_tag_arguments word_stream];rewrite STREAM;reflexivity.
                         *** apply cons_argument_values with(v:=Vint Int.one);[apply old_expression_value;constructor|reflexivity|].
                             apply cons_argument_values with(v:=Vptr(gateway_value_tag_slot slots)Ptrofs.zero).
                             ---- apply local_address_expression;unfold gateway_value_environment;
                                    rewrite PTree.gso by discriminate;apply PTree.gss.
                             ---- reflexivity.
                             ---- apply no_argument_values.
                     +++ change(Genv.find_funct_ptr ge symbol=Some(Internal f_host_word));exact FUNCTION.
                     +++ reflexivity.
                 --- apply gateway_source_reached;auto.
Qed.

End ValueTag.
