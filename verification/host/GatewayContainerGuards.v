(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual container bounds precede object allocation and recursive calls. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayValueEntry GatewayValueGuards GatewayValueExpressions
  GatewayValueTag GatewayValueStack GatewayValueContext GatewayValueRegions GatewayContainerLength GatewayScalarContext
  GatewaySourceDynamic GatewaySourceCuts GatewayFailurePaths GatewayFramedRuntime GatewayStreamMemory
  GatewayStreamInterface GatewayStreamLayout GatewayStreamAccess GatewayThreadRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_container_capacity container nodes :int64:=
  match container with gateway_container_array=>nodes|gateway_container_object=>Int64.divu nodes(Int64.repr 2)end.
Definition gateway_container_counted {World}native stable discipline container slots stream_block stream_offset initial readonly original
    size memory world :Prop:=
  @gateway_value_tagged World native stable discipline slots stream_block stream_offset initial readonly original
    (Int64.repr(gateway_container_code container))memory world /\
  Mem.loadv Mint64 memory(Vptr(gateway_value_size_slot slots)Ptrofs.zero)=Some(Vlong size).

Lemma gateway_container_counted_ambient {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    container slots stream_block stream_offset initial readonly original size :
  gateway_ambient_closed backend(gateway_container_counted native stable discipline container slots stream_block stream_offset
    initial readonly original size).
Proof.
  intros before world after next[TAGGED LOAD]INTERFERENCE;split.
  - eapply gateway_value_tagged_ambient;[exact runtime|exact TAGGED|exact INTERFERENCE].
  - destruct TAGGED as[[[SIDE CONTEXT][TAG_NATIVE[SIZE_NATIVE REST]]]TAG_LOAD].
    destruct(gateway_thread_ambient _ _ _ _ _ _ runtime None _ _ _ _ SIDE INTERFERENCE)as[_[_ FRAME]].
    change(Mem.load Mint64 before(gateway_value_size_slot slots)0=Some(Vlong size))in LOAD.
    change(Mem.load Mint64 after(gateway_value_size_slot slots)0=Some(Vlong size)).
    eapply Mem.load_unchanged_on;[exact FRAME| |exact LOAD].
    intros position RANGE;split;[left;exact SIZE_NATIVE|unfold gateway_native_no_output;tauto].
Qed.

Lemma gateway_counted_nodes {World}native stable discipline container slots stream_block stream_offset initial readonly original
    size memory world :
  @gateway_container_counted World native stable discipline container slots stream_block stream_offset initial readonly original size memory world ->
  Mem.loadv Mint64 memory(gateway_stream_slot stream_block stream_offset 32)=Some(Vlong(stream_nodes initial)).
Proof.
  intros[[[[SIDE[STREAM[READONLY[INPUT FRAME]]]]REST]TAG]SIZE].
  destruct(gateway_value_stream_cells _ _ _ _ _ INPUT)as(A&B&C&D&E&F&G&H);exact G.
Qed.

Ltac gateway_container_guard_loads input stream stream_parameter layout :=
  first[apply gateway_value_tag_expression;exact(proj2(proj1 input))|
    apply gateway_value_size_expression;exact(proj2 input)|
    eapply actual_stream_member_read with(delta:=32)(chunk:=Mint64);
      [rewrite<-stream;unfold set_opttemp;repeat rewrite PTree.gso by discriminate;exact stream_parameter|
        exact layout|reflexivity|eapply gateway_counted_nodes;exact input]].

Ltac gateway_container_current_loads :=
  match goal with
  |INPUT:gateway_container_counted _ _ _ _ _ _ _ _ _ _ _ _ _,
    STREAM:gateway_value_stream _=Vptr _ _,
    PARAMETER:PTree.get _stream _=Some(gateway_value_stream _),
    LAYOUT:stream_member_layout _ _nodes 32|-_=>
      gateway_container_guard_loads INPUT STREAM PARAMETER LAYOUT
  end.

Ltac gateway_container_guard_reduce :=
  cbn -[Int64.ltu Int64.eq Int64.unsigned Int64.divu];
  repeat match goal with |-context[Int.signed(Int.repr ?constant)]=>
    let normalized:=eval vm_compute in(Int.signed(Int.repr constant))in
    progress(change(Int.signed(Int.repr constant))with normalized)
  end;
  repeat match goal with H:context[gateway_container_capacity _ _]|-_=>
    progress(cbn[gateway_container_capacity]in H)
  end;
  repeat match goal with H:Int64.ltu _ _=_|-_=>progress(rewrite H)end;
  reflexivity.

Theorem gateway_container_bound_failure {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    io native stable discipline thread_errno(runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    container slots arguments parameters stream_block stream_offset initial readonly original size memory :
  gateway_value_stream arguments=Vptr stream_block stream_offset ->parameters!_stream=Some(gateway_value_stream arguments) ->
  stream_member_layout ge _nodes 32 ->Int64.ltu(gateway_container_capacity container(stream_nodes initial))size=true ->
  gateway_failure_when backend ge
    (gateway_container_counted native stable discipline container slots stream_block stream_offset initial readonly original size)
    (Returnstate(Vint Int.zero)(gateway_value_container_size_cont slots parameters)memory).
Proof.
  intros STREAM STREAM_PARAMETER LAYOUT BAD.
  pose proof(gateway_container_counted_ambient backend io native stable discipline thread_errno runtime
    container slots stream_block stream_offset initial readonly original size)as CLOSED.
  destruct container;gateway_source_dynamic_failure CLOSED ltac:(fun _=>gateway_container_current_loads)
    ltac:(fun _=>gateway_container_guard_reduce)gateway_value_pointer_return.
Qed.

Theorem gateway_actual_container_bound {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    io native stable discipline thread_errno(runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    container slots arguments parameters stream_block stream_offset initial readonly original size before world events value after next :
  gateway_value_stream arguments=Vptr stream_block stream_offset ->parameters!_stream=Some(gateway_value_stream arguments) ->
  stream_member_layout ge _nodes 32 ->
  gateway_container_counted native stable discipline container slots stream_block stream_offset initial readonly original size before world ->
  gateway_steps backend ge
    (gateway_live(Returnstate(Vint Int.zero)(gateway_value_container_size_cont slots parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value<>Vnullptr ->
  Int64.unsigned size<=Int64.unsigned(gateway_container_capacity container(stream_nodes initial)).
Proof.
  intros STREAM STREAM_PARAMETER LAYOUT INPUT RUN NONNULL.
  assert(BOUND:Int64.ltu(gateway_container_capacity container(stream_nodes initial))size=false).
  { destruct(Int64.ltu(gateway_container_capacity container(stream_nodes initial))size)eqn:BOUND;[|reflexivity].
    exfalso;apply NONNULL;eapply(gateway_container_bound_failure backend ge io native stable discipline thread_errno runtime
      container slots arguments parameters stream_block stream_offset initial readonly original size before
      STREAM STREAM_PARAMETER LAYOUT BOUND);[exact INPUT|exact RUN]. }
  unfold Int64.ltu in BOUND;destruct(zlt _ _);[discriminate|lia].
Qed.
