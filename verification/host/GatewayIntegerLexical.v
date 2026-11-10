(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual sign, canonical-head and every-byte digit checks yield
   the constructor flag on the same source path; the null result survives rejected forms. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayValueEntry GatewayScalarContext GatewayScalarTerminate
  GatewayIntegerLoop GatewayIntegerScan GatewayIntegerScanRetained GatewayIntegerPrefix GatewayIntegerPrefixSource
  GatewayIntegerCanonical GatewaySourceSegments GatewayFramedRuntime.
Import ListNotations.
Open Scope Z_scope.

Lemma gateway_integer_digits_length bytes:
  0<=gateway_integer_start bytes /\
  gateway_integer_start bytes+Z.of_nat(length(gateway_integer_digits bytes))=Z.of_nat(length bytes).
Proof.
  destruct bytes as[|byte rest];[split;reflexivity|].
  unfold gateway_integer_start,gateway_integer_digits,gateway_integer_negative;cbn[tl].
  destruct(Byte.eq byte(Byte.repr 45));split;cbn[length];rewrite ?Nat2Z.inj_succ;lia.
Qed.

Theorem gateway_integer_lexical_segment {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)slots parameters object bytes memory:
  gateway_ambient_closed backend property->Z.of_nat(length bytes)<=32->parameters!_bytes=Some(Vptr object Ptrofs.zero)->
  (forall memory world,property memory world->Mem.loadv Mint64 memory(Vptr(gateway_value_tag_slot slots)Ptrofs.zero)=Some(Vlong(Int64.repr 3)))->
  (forall memory world,property memory world->Mem.loadv Mint64 memory(Vptr(gateway_value_size_slot slots)Ptrofs.zero)=Some(Vlong(Int64.repr(Z.of_nat(length bytes)))))->
  (forall index byte,nth_error bytes index=Some byte->forall memory world,property memory world->
    Mem.loadv Mint8signed memory(Vptr object(Ptrofs.repr(Z.of_nat index)))=Some(Vint(Int.repr(Byte.signed byte))))->
  exists final_parameters,
    gateway_source_segment backend ge property
      (gateway_scalar_terminated_state slots(Int64.repr(Z.of_nat(length bytes)))parameters memory)
      (State f_host_value Sskip gateway_integer_loop_cont(gateway_value_environment slots)final_parameters memory)property /\
    final_parameters!_bytes=Some(Vptr object Ptrofs.zero) /\final_parameters!_value=Some Vnullptr /\
    final_parameters!_valid=Some(Vint(if gateway_integer_check bytes then Int.one else Int.zero)).
Proof.
  intros CLOSED BOUND BYTES TAG SIZE LOADS.
  destruct(gateway_integer_actual_prefix backend ge property slots parameters object bytes memory CLOSED BOUND BYTES TAG SIZE LOADS)
    as(loop_parameters &PREFIX &LOOP_BYTES &LOOP_NULL &LOOP_START &LOOP_INDEX &LOOP_VALID).
  destruct(gateway_integer_digits_length bytes)as[START COUNT].
  destruct(gateway_integer_scan_segment_retained backend ge property slots gateway_integer_loop_cont object(Z.of_nat(length bytes))memory
    CLOSED ltac:(lia)SIZE(gateway_integer_digits bytes)loop_parameters(gateway_integer_start bytes)(gateway_integer_initial_flag bytes)
    START COUNT LOOP_BYTES LOOP_INDEX LOOP_VALID
    ltac:(intros offset character SELECTED current world GOOD;
      unfold gateway_integer_digits,gateway_integer_start,gateway_integer_negative in *;
      destruct bytes as[|first rest];[destruct offset;discriminate|];destruct(Byte.eq first(Byte.repr 45));cbn[tl]in *;
      [replace(1+Z.of_nat offset)with(Z.of_nat(S offset))by(rewrite Nat2Z.inj_succ;lia);
        eapply(LOADS(S offset)character);[exact SELECTED|exact GOOD]|
       rewrite Z.add_0_l;eapply(LOADS offset character);[exact SELECTED|exact GOOD]]))
    as(final_parameters &SCAN &FINAL_BYTES &FINAL_INDEX &FINAL_VALID &FINAL_NULL).
  exists final_parameters;split;[eapply gateway_integer_segments_append;eassumption|].
  split;[exact FINAL_BYTES|]. split;[rewrite FINAL_NULL;exact LOOP_NULL|].
  rewrite gateway_integer_checked_flag in FINAL_VALID;exact FINAL_VALID.
Qed.
