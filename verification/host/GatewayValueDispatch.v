(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Nonzero tags cross the actual null test before later decoder cases. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayFrames GatewayPure GatewayValueEntry GatewayValueTag
  GatewayValueNull GatewaySourceSegments GatewayFramedRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_value_nonzero_tag_parameters arguments initial tag:=
  PTree.set _t'93(Vlong tag)(gateway_value_after_word_parameters arguments initial).

Theorem gateway_value_nonzero_tag_segment {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)slots arguments initial memory tag :
  gateway_ambient_closed backend property ->tag<>Int64.zero ->
  (forall memory world,property memory world->Mem.loadv Mint64 memory
    (Vptr(gateway_value_tag_slot slots)Ptrofs.zero)=Some(Vlong tag)) ->
  gateway_source_segment backend ge property
    (Returnstate(Vint Int.zero)(gateway_value_tag_cont slots arguments initial)memory)
    (State f_host_value gateway_value_after_null Kstop(gateway_value_environment slots)
      (gateway_value_nonzero_tag_parameters arguments initial tag)memory)property.
Proof.
  intros CLOSED NONZERO LOADED.
  eapply gateway_segment_same with(next:=State f_host_value Sskip
    (Kseq gateway_value_tag_guard(Kseq gateway_value_after_tag Kstop))(gateway_value_environment slots)
    (gateway_value_after_word_parameters arguments initial)memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_returnstate|].
  eapply gateway_segment_same with(next:=State f_host_value gateway_value_tag_guard
    (Kseq gateway_value_after_tag Kstop)(gateway_value_environment slots)
    (gateway_value_after_word_parameters arguments initial)memory);
    [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
  eapply gateway_segment_same with(next:=State f_host_value Sskip(Kseq gateway_value_after_tag Kstop)
    (gateway_value_environment slots)(gateway_value_after_word_parameters arguments initial)memory).
  - exact CLOSED.
  - cbn;tauto.
  - intros;eapply certified_if_edge with(b:=false);[apply old_expression_value,value_temp;apply PTree.gss|reflexivity].
  - eapply gateway_segment_same with(next:=State f_host_value gateway_value_after_tag Kstop
      (gateway_value_environment slots)(gateway_value_after_word_parameters arguments initial)memory);
      [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
    change gateway_value_after_tag with(Ssequence gateway_value_null_test gateway_value_after_null).
    eapply gateway_segment_same with(next:=State f_host_value gateway_value_null_test(Kseq gateway_value_after_null Kstop)
      (gateway_value_environment slots)(gateway_value_after_word_parameters arguments initial)memory);
      [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
    change gateway_value_null_test with(Ssequence gateway_value_null_load gateway_value_null_guard).
    eapply gateway_segment_same with(next:=State f_host_value gateway_value_null_load
      (Kseq gateway_value_null_guard(Kseq gateway_value_after_null Kstop))
      (gateway_value_environment slots)(gateway_value_after_word_parameters arguments initial)memory);
      [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
    eapply gateway_segment_same with(next:=State f_host_value Sskip
      (Kseq gateway_value_null_guard(Kseq gateway_value_after_null Kstop))
      (gateway_value_environment slots)(gateway_value_nonzero_tag_parameters arguments initial tag)memory).
    + exact CLOSED.
    + cbn;tauto.
    + intros current world GOOD;apply certified_set_edge.
      apply location_read_value with(b:=gateway_value_tag_slot slots)(ofs:=Ptrofs.zero).
      * apply local_location_value;unfold gateway_value_environment;rewrite PTree.gso by discriminate;apply PTree.gss.
      * apply deref_loc_value with(chunk:=Mint64);[reflexivity|apply LOADED with(world:=world);exact GOOD].
    + eapply gateway_segment_same with(next:=State f_host_value gateway_value_null_guard
        (Kseq gateway_value_after_null Kstop)(gateway_value_environment slots)
        (gateway_value_nonzero_tag_parameters arguments initial tag)memory);
        [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
      eapply gateway_segment_same with(next:=State f_host_value Sskip(Kseq gateway_value_after_null Kstop)
        (gateway_value_environment slots)(gateway_value_nonzero_tag_parameters arguments initial tag)memory).
      * exact CLOSED.
      * cbn;tauto.
      * intros;eapply certified_if_edge with(b:=false).
        -- apply old_expression_value;eapply value_unary;[apply value_temp;apply PTree.gss|].
           cbn;rewrite Int64.eq_false by exact NONZERO;reflexivity.
        -- reflexivity.
      * eapply gateway_segment_same with(next:=State f_host_value gateway_value_after_null Kstop
          (gateway_value_environment slots)(gateway_value_nonzero_tag_parameters arguments initial tag)memory);
          [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
        apply gateway_segment_here.
Qed.
