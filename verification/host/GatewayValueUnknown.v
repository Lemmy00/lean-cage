(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Unknown received tags follow the actual denial branch, including
   arbitrary callbacks, ambient steps and loss along that same wider source execution. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayFrames GatewayFramedRuntime GatewayValueEntry
  GatewayValueTag GatewayValueNull GatewayValueGuards GatewayValueExpressions GatewayValueDispatch GatewayValueBoolean GatewayValueAfterBoolean
  GatewayScalarLength GatewayContainerLength
  GatewaySourceSegments GatewaySourceCuts GatewaySourceDynamic GatewayFailurePaths.
Import ListNotations.
Open Scope Z_scope.

Lemma gateway_segment_then_failure {World Event}(backend:gateway_backend World Event)ge property source target result:
  gateway_source_segment backend ge property source target result->
  gateway_failure_when backend ge result target->gateway_failure_when backend ge property source.
Proof.
  intro SEGMENT;induction SEGMENT;intro FAILURE;[exact FAILURE|].
  eapply gateway_failure_when_edge;[exact H|exact H0|exact H1|apply IHSEGMENT;exact FAILURE].
Qed.

Lemma gateway_unknown_tag_equal number constant:
  10<=number<=255->0<=constant<=9->Int64.eq(Int64.repr number)(Int64.repr constant)=false.
Proof.
  intros NUMBER CONSTANT;apply Int64.eq_false;intro SAME;apply(f_equal Int64.unsigned)in SAME.
  rewrite !Int64.unsigned_repr in SAME by(change Int64.max_unsigned with 18446744073709551615;lia);lia.
Qed.
Lemma gateway_unknown_tag_lower number constant:
  10<=number<=255->0<=constant<=9->Int64.ltu(Int64.repr number)(Int64.repr constant)=false.
Proof.
  intros NUMBER CONSTANT;unfold Int64.ltu;rewrite !Int64.unsigned_repr by
    (change Int64.max_unsigned with 18446744073709551615;lia);apply zlt_false;lia.
Qed.
Lemma gateway_unknown_tag_upper number constant:
  10<=number<=255->0<=constant<=9->Int64.ltu(Int64.repr constant)(Int64.repr number)=true.
Proof.
  intros NUMBER CONSTANT;unfold Int64.ltu;rewrite !Int64.unsigned_repr by
    (change Int64.max_unsigned with 18446744073709551615;lia);apply zlt_true;lia.
Qed.

Ltac gateway_unknown_tag_reduce number :=
  cbn -[Int64.ltu Int64.eq Int64.unsigned Int64.repr];
  repeat rewrite Int.signed_repr by(change Int.min_signed with (-2147483648);
    change Int.max_signed with 2147483647;lia);
  repeat first[
    rewrite(gateway_unknown_tag_equal number _)by lia|
    rewrite(gateway_unknown_tag_lower number _)by lia|
    rewrite(gateway_unknown_tag_upper number _)by lia];reflexivity.

Theorem gateway_value_unknown_tag_failure {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:Memory.mem->World->Prop)slots arguments initial memory number:
  gateway_ambient_closed backend property->10<=number<=255->
  (forall memory world,property memory world->Mem.loadv Mint64 memory
    (Vptr(gateway_value_tag_slot slots)Ptrofs.zero)=Some(Vlong(Int64.repr number)))->
  gateway_failure_when backend ge property
    (Returnstate(Vint Int.zero)(gateway_value_tag_cont slots arguments initial)memory).
Proof.
  intros CLOSED RANGE LOADED.
  eapply gateway_segment_then_failure.
  - apply gateway_value_nonzero_tag_segment;[exact CLOSED| |exact LOADED].
    intro SAME;apply(f_equal Int64.unsigned)in SAME;rewrite Int64.unsigned_repr in SAME by
      (change Int64.max_unsigned with 18446744073709551615;lia);change(number=0)in SAME;lia.
  - eapply gateway_segment_then_failure.
    + apply gateway_value_nonboolean_segment;[exact CLOSED| | |exact LOADED].
      * intro SAME;apply(f_equal Int64.unsigned)in SAME;rewrite Int64.unsigned_repr in SAME by
          (change Int64.max_unsigned with 18446744073709551615;lia);change(number=1)in SAME;lia.
      * intro SAME;apply(f_equal Int64.unsigned)in SAME;rewrite !Int64.unsigned_repr in SAME by
          (change Int64.max_unsigned with 18446744073709551615;lia);lia.
    + unfold gateway_value_after_boolean,gateway_value_after_scalar,gateway_value_after_container.
      gateway_source_dynamic_failure CLOSED
        ltac:(fun _=>apply gateway_value_tag_expression;eapply LOADED;eassumption)
        ltac:(fun _=>gateway_unknown_tag_reduce number)
        gateway_value_pointer_return.
Qed.
