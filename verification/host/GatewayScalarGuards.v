(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Both actual scalar length guards precede any payload allocation. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayValueEntry GatewayValueGuards GatewayValueExpressions
  GatewayScalarLength GatewayScalarContext GatewaySourceDynamic GatewaySourceCuts GatewayFailurePaths GatewayFramedRuntime
  GatewayStreamInterface GatewayStreamLayout GatewayStreamAccess GatewayThreadRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_scalar_maximum scalar :Z:=
  match scalar with
  |gateway_scalar_long=>32|gateway_scalar_text=>16777216|gateway_scalar_bytes=>268435456
  |gateway_scalar_path=>4095|gateway_scalar_number=>65536
  end.

Lemma gateway_scalar_maximum_unsigned scalar :
  Int64.unsigned(Int64.repr(gateway_scalar_maximum scalar))=gateway_scalar_maximum scalar.
Proof. destruct scalar;reflexivity. Qed.

Ltac gateway_scalar_guard_loads input stream stream_parameter layout :=
  first[apply gateway_value_tag_expression;exact(proj2(proj1 input))|
    apply gateway_value_size_expression;exact(proj2 input)|
    eapply actual_stream_member_read with(delta:=24)(chunk:=Mint64);
      [rewrite<-stream;unfold set_opttemp;repeat rewrite PTree.gso by discriminate;exact stream_parameter|
        exact layout|reflexivity|eapply gateway_sized_remaining;exact input]].

Ltac gateway_scalar_current_loads :=
  match goal with
  |INPUT:gateway_value_sized _ _ _ _ _ _ _ _ _ _ _ _ _,
    STREAM:gateway_value_stream _=Vptr _ _,
    PARAMETER:PTree.get _stream _=Some(gateway_value_stream _),
    LAYOUT:stream_member_layout _ _remaining 24|-_=>
      gateway_scalar_guard_loads INPUT STREAM PARAMETER LAYOUT
  end.

Ltac gateway_scalar_guard_reduce :=
  cbn -[Int64.ltu Int64.eq Int64.unsigned];
  repeat match goal with |-context[Int.signed(Int.repr ?constant)]=>
    let normalized:=eval vm_compute in(Int.signed(Int.repr constant))in
    progress(change(Int.signed(Int.repr constant))with normalized)
  end;
  repeat match goal with H:context[gateway_scalar_maximum _]|-_=>
    progress(cbn[gateway_scalar_maximum]in H)
  end;
  repeat match goal with H:Int64.ltu _ _=_|-_=>progress(rewrite H)end;
  reflexivity.

Theorem gateway_scalar_bound_failure {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    io native stable discipline thread_errno(runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    scalar slots arguments parameters stream_block stream_offset initial readonly original size memory :
  gateway_value_stream arguments=Vptr stream_block stream_offset ->parameters!_stream=Some(gateway_value_stream arguments) ->
  stream_member_layout ge _remaining 24 ->
  (Int64.ltu(Int64.repr(gateway_scalar_maximum scalar))size=true \/Int64.ltu(stream_remaining initial)size=true) ->
  gateway_failure_when backend ge
    (gateway_value_sized native stable discipline scalar slots stream_block stream_offset initial readonly original size)
    (Returnstate(Vint Int.zero)(gateway_value_scalar_size_cont slots parameters)memory).
Proof.
  intros STREAM STREAM_PARAMETER LAYOUT BAD.
  pose proof(gateway_value_sized_ambient backend io native stable discipline thread_errno runtime
    scalar slots stream_block stream_offset initial readonly original size)as CLOSED.
  destruct(Int64.ltu(Int64.repr(gateway_scalar_maximum scalar))size)eqn:MAXIMUM.
  - destruct scalar;gateway_source_dynamic_failure CLOSED ltac:(fun _=>gateway_scalar_current_loads) ltac:(fun _=>gateway_scalar_guard_reduce)
      gateway_value_pointer_return.
  - destruct(Int64.ltu(stream_remaining initial)size)eqn:REMAINING.
    + destruct scalar;gateway_source_dynamic_failure CLOSED ltac:(fun _=>gateway_scalar_current_loads) ltac:(fun _=>gateway_scalar_guard_reduce)
        gateway_value_pointer_return.
    + destruct BAD;discriminate.
Qed.

Theorem gateway_actual_scalar_bounds {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    io native stable discipline thread_errno(runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    scalar slots arguments parameters stream_block stream_offset initial readonly original size before world events value after next :
  gateway_value_stream arguments=Vptr stream_block stream_offset ->parameters!_stream=Some(gateway_value_stream arguments) ->
  stream_member_layout ge _remaining 24 ->
  gateway_value_sized native stable discipline scalar slots stream_block stream_offset initial readonly original size before world ->
  gateway_steps backend ge
    (gateway_live(Returnstate(Vint Int.zero)(gateway_value_scalar_size_cont slots parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value<>Vnullptr ->
  Int64.unsigned size<=gateway_scalar_maximum scalar /\Int64.unsigned size<=Int64.unsigned(stream_remaining initial).
Proof.
  intros STREAM STREAM_PARAMETER LAYOUT INPUT RUN NONNULL.
  assert(MAXIMUM:Int64.ltu(Int64.repr(gateway_scalar_maximum scalar))size=false).
  { destruct(Int64.ltu(Int64.repr(gateway_scalar_maximum scalar))size)eqn:MAXIMUM;[|reflexivity].
    exfalso;apply NONNULL;eapply(gateway_scalar_bound_failure backend ge io native stable discipline thread_errno runtime
      scalar slots arguments parameters stream_block stream_offset initial readonly original size before
      STREAM STREAM_PARAMETER LAYOUT(or_introl MAXIMUM));[exact INPUT|exact RUN]. }
  assert(REMAINING:Int64.ltu(stream_remaining initial)size=false).
  { destruct(Int64.ltu(stream_remaining initial)size)eqn:REMAINING;[|reflexivity].
    exfalso;apply NONNULL;eapply(gateway_scalar_bound_failure backend ge io native stable discipline thread_errno runtime
      scalar slots arguments parameters stream_block stream_offset initial readonly original size before
      STREAM STREAM_PARAMETER LAYOUT(or_intror REMAINING));[exact INPUT|exact RUN]. }
  unfold Int64.ltu in MAXIMUM,REMAINING.
  rewrite gateway_scalar_maximum_unsigned in MAXIMUM.
  destruct(zlt(gateway_scalar_maximum scalar)(Int64.unsigned size));[discriminate|].
  destruct(zlt(Int64.unsigned(stream_remaining initial))(Int64.unsigned size));[discriminate|lia].
Qed.
