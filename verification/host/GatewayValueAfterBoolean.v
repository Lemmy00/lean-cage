(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Scalar and container dispatch follow both actual Boolean comparisons. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayFrames GatewayValueEntry GatewayValueNull
  GatewayValueDispatch GatewayValueExpressions GatewayValueBoolean GatewaySourceSegments GatewaySourceTactics GatewayFramedRuntime.
Import ListNotations.

Definition gateway_value_nonboolean_first_parameters arguments initial tag:=
  PTree.set _t'91(Vlong tag)(gateway_value_nonzero_tag_parameters arguments initial tag).
Definition gateway_value_nonboolean_second_parameters arguments initial tag:=
  PTree.set _t'92(Vlong tag)(gateway_value_nonboolean_first_parameters arguments initial tag).
Definition gateway_value_nonboolean_parameters arguments initial tag:=
  PTree.set _t'4(Vint Int.zero)(gateway_value_nonboolean_second_parameters arguments initial tag).

Theorem gateway_value_nonboolean_segment {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:Memory.mem->World->Prop)slots arguments initial memory tag :
  gateway_ambient_closed backend property ->tag<>Int64.one ->tag<>Int64.repr 2 ->
  (forall memory world,property memory world->Mem.loadv Mint64 memory
    (Vptr(gateway_value_tag_slot slots)Ptrofs.zero)=Some(Vlong tag)) ->
  gateway_source_segment backend ge property
    (State f_host_value gateway_value_after_null Kstop(gateway_value_environment slots)
      (gateway_value_nonzero_tag_parameters arguments initial tag)memory)
    (State f_host_value gateway_value_after_boolean Kstop(gateway_value_environment slots)
      (gateway_value_nonboolean_parameters arguments initial tag)memory)property.
Proof.
  intros CLOSED NOT_ONE NOT_TWO LOADED.
  change gateway_value_after_null with(Ssequence gateway_value_boolean_test gateway_value_after_boolean).
  gateway_segment_seq CLOSED.
  change gateway_value_boolean_test with(Ssequence gateway_value_boolean_check gateway_value_boolean_guard).
  gateway_segment_seq CLOSED.
  change gateway_value_boolean_check with(Ssequence gateway_value_boolean_first_read gateway_value_boolean_first_guard).
  gateway_segment_seq CLOSED.
  eapply gateway_segment_same with(next:=State f_host_value Sskip
    (Kseq gateway_value_boolean_first_guard(Kseq gateway_value_boolean_guard(Kseq gateway_value_after_boolean Kstop)))
    (gateway_value_environment slots)(gateway_value_nonboolean_first_parameters arguments initial tag)memory).
  - exact CLOSED.
  - cbn;tauto.
  - intros current world GOOD;apply certified_set_edge,gateway_value_tag_expression.
    apply LOADED with(world:=world);exact GOOD.
  - gateway_segment_skip CLOSED.
    eapply gateway_segment_same with(next:=State f_host_value gateway_value_boolean_second
      (Kseq gateway_value_boolean_guard(Kseq gateway_value_after_boolean Kstop))(gateway_value_environment slots)
      (gateway_value_nonboolean_first_parameters arguments initial tag)memory).
    + exact CLOSED.
    + cbn;tauto.
    + intros;eapply certified_if_edge with(b:=false).
      * apply old_expression_value;eapply value_binary with(result:=Vint Int.zero);
          [apply value_temp;apply PTree.gss|constructor|].
        change(Some(Val.of_bool(Int64.eq tag Int64.one))=Some(Vint Int.zero)).
        rewrite Int64.eq_false by exact NOT_ONE;reflexivity.
      * reflexivity.
    + change gateway_value_boolean_second with(Ssequence gateway_value_boolean_second_read gateway_value_boolean_second_set).
      gateway_segment_seq CLOSED.
      eapply gateway_segment_same with(next:=State f_host_value Sskip
        (Kseq gateway_value_boolean_second_set(Kseq gateway_value_boolean_guard(Kseq gateway_value_after_boolean Kstop)))
        (gateway_value_environment slots)(gateway_value_nonboolean_second_parameters arguments initial tag)memory).
      * exact CLOSED.
      * cbn;tauto.
      * intros current world GOOD;apply certified_set_edge,gateway_value_tag_expression.
        apply LOADED with(world:=world);exact GOOD.
      * gateway_segment_skip CLOSED.
        eapply gateway_segment_same with(next:=State f_host_value Sskip
          (Kseq gateway_value_boolean_guard(Kseq gateway_value_after_boolean Kstop))(gateway_value_environment slots)
          (gateway_value_nonboolean_parameters arguments initial tag)memory).
        -- exact CLOSED.
        -- cbn;tauto.
        -- intros;apply certified_set_edge,old_expression_value;eapply value_cast.
           ++ eapply value_binary with(result:=Vint Int.zero);[apply value_temp;apply PTree.gss|constructor|].
              change(Some(Val.of_bool(Int64.eq tag(Int64.repr 2)))=Some(Vint Int.zero)).
              rewrite Int64.eq_false by exact NOT_TWO;reflexivity.
           ++ reflexivity.
        -- gateway_segment_skip CLOSED.
           eapply gateway_segment_same with(next:=State f_host_value Sskip(Kseq gateway_value_after_boolean Kstop)
             (gateway_value_environment slots)(gateway_value_nonboolean_parameters arguments initial tag)memory).
           ++ exact CLOSED.
           ++ cbn;tauto.
           ++ intros;eapply certified_if_edge with(b:=false).
              ** apply old_expression_value,value_temp;apply PTree.gss.
              ** reflexivity.
           ++ gateway_segment_skip CLOSED;apply gateway_segment_here.
Qed.
