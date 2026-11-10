(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Every prefix reaching scalar allocation has passed both actual bounds. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayValueEntry GatewayValueGuards GatewayScalarLength
  GatewayScalarContext GatewayScalarGuards GatewayScalarAllocationPath GatewayFailurePaths GatewayFailureControl
  GatewayFailureEvaluation GatewayStreamInterface GatewayStreamLayout GatewayThreadRuntime GatewayFramedRuntime.
Import ListNotations.
Open Scope Z_scope.

Lemma gateway_scalar_malloc_cont_not_null slots parameters :
  ~gateway_nested_null(gateway_value_scalar_malloc_cont slots parameters).
Proof. vm_compute;intuition discriminate. Qed.

Theorem gateway_scalar_bound_control {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    io native stable discipline thread_errno(runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    scalar slots arguments parameters stream_block stream_offset initial readonly original size memory :
  gateway_value_stream arguments=Vptr stream_block stream_offset ->parameters!_stream=Some(gateway_value_stream arguments) ->
  stream_member_layout ge _remaining 24 ->
  (Int64.ltu(Int64.repr(gateway_scalar_maximum scalar))size=true \/Int64.ltu(stream_remaining initial)size=true) ->
  gateway_failure_control backend ge
    (gateway_value_sized native stable discipline scalar slots stream_block stream_offset initial readonly original size)
    (Returnstate(Vint Int.zero)(gateway_value_scalar_size_cont slots parameters)memory).
Proof.
  intros STREAM STREAM_PARAMETER LAYOUT BAD.
  pose proof(gateway_value_sized_ambient backend io native stable discipline thread_errno runtime
    scalar slots stream_block stream_offset initial readonly original size)as CLOSED.
  destruct(Int64.ltu(Int64.repr(gateway_scalar_maximum scalar))size)eqn:MAXIMUM.
  - destruct scalar;gateway_source_failure_control CLOSED ltac:(fun _=>gateway_scalar_current_loads) ltac:(fun _=>gateway_scalar_guard_reduce)
      gateway_value_pointer_return.
  - destruct(Int64.ltu(stream_remaining initial)size)eqn:REMAINING.
    + destruct scalar;gateway_source_failure_control CLOSED ltac:(fun _=>gateway_scalar_current_loads) ltac:(fun _=>gateway_scalar_guard_reduce)
        gateway_value_pointer_return.
    + destruct BAD;discriminate.
Qed.

Theorem gateway_prefix_scalar_bounds {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    io native stable discipline thread_errno(runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    scalar slots arguments parameters stream_block stream_offset initial readonly original size before world events
    allocated_arguments called_parameters memory next :
  gateway_value_stream arguments=Vptr stream_block stream_offset ->parameters!_stream=Some(gateway_value_stream arguments) ->
  stream_member_layout ge _remaining 24 ->
  gateway_value_sized native stable discipline scalar slots stream_block stream_offset initial readonly original size before world ->
  gateway_steps backend ge
    (gateway_live(Returnstate(Vint Int.zero)(gateway_value_scalar_size_cont slots parameters)before)world)events
    (gateway_live(Callstate(External EF_malloc[tulong](tptr tvoid)cc_default)allocated_arguments
      (gateway_value_scalar_malloc_cont slots called_parameters)memory)next) ->
  Int64.unsigned size<=gateway_scalar_maximum scalar /\Int64.unsigned size<=Int64.unsigned(stream_remaining initial).
Proof.
  intros STREAM STREAM_PARAMETER LAYOUT INPUT RUN.
  assert(MAXIMUM:Int64.ltu(Int64.repr(gateway_scalar_maximum scalar))size=false).
  { destruct(Int64.ltu(Int64.repr(gateway_scalar_maximum scalar))size)eqn:MAXIMUM;[|reflexivity].
    exfalso;eapply gateway_failure_control_cannot_call;
      [exact(gateway_scalar_bound_control backend ge io native stable discipline thread_errno runtime
        scalar slots arguments parameters stream_block stream_offset initial readonly original size before
        STREAM STREAM_PARAMETER LAYOUT(or_introl MAXIMUM))|exact INPUT|
        exact(gateway_scalar_malloc_cont_not_null slots called_parameters)|exact RUN]. }
  assert(REMAINING:Int64.ltu(stream_remaining initial)size=false).
  { destruct(Int64.ltu(stream_remaining initial)size)eqn:REMAINING;[|reflexivity].
    exfalso;eapply gateway_failure_control_cannot_call;
      [exact(gateway_scalar_bound_control backend ge io native stable discipline thread_errno runtime
        scalar slots arguments parameters stream_block stream_offset initial readonly original size before
        STREAM STREAM_PARAMETER LAYOUT(or_intror REMAINING))|exact INPUT|
        exact(gateway_scalar_malloc_cont_not_null slots called_parameters)|exact RUN]. }
  unfold Int64.ltu in MAXIMUM,REMAINING;rewrite gateway_scalar_maximum_unsigned in MAXIMUM.
  destruct(zlt(gateway_scalar_maximum scalar)(Int64.unsigned size));[discriminate|].
  destruct(zlt(Int64.unsigned(stream_remaining initial))(Int64.unsigned size));[discriminate|lia].
Qed.
