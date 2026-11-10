(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: The read guard consumes actual function entry and raw owned
   cells. *)
From Stdlib Require Import ZArith List.
From compcert Require Import AST Values Memory Integers Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayFunctionEntry GatewayCalls GatewayFrames
  GatewayStreamInterface GatewayStreamLayout GatewayStreamMemory GatewayReadGuard.
Import ListNotations.
Open Scope Z_scope.

Lemma actual_read_entry_canonical ge stream data amount before environment temporaries allocated :
  function_entry2 ge f_host_read[stream;data;Vlong(Int64.repr amount)]before
    environment temporaries allocated ->
  environment=empty_env /\temporaries=read_parameters stream data amount /\allocated=before.
Proof.
  intro ENTRY;inversion ENTRY;subst.
  match goal with ALLOC:alloc_variables _ _ _ _ _ _|-_=>
    change(alloc_variables ge empty_env before [] environment allocated)in ALLOC;
    inversion ALLOC;subst end.
  match goal with BIND:bind_parameter_temps _ _ _=Some temporaries|-_=>
    change(Some(read_parameters stream data amount)=Some temporaries)in BIND;
    inversion BIND;subst end.
  auto.
Qed.

Theorem actual_successful_read_passed_guard {World Event}(backend:gateway_backend World Event)ge
    stream_block stream_offset data amount initial before world events after next active
    (private:gateway_private_contract backend(gateway_stream_region stream_block stream_offset)active) :
  active world ->gateway_stream_memory before stream_block stream_offset initial ->
  stream_member_layout ge _remaining 24 ->Ptrofs.unsigned stream_offset+48<=Ptrofs.modulus ->
  0<=amount<=Int64.max_unsigned ->
  gateway_steps backend ge
    (gateway_live(Callstate(Internal f_host_read)
      [Vptr stream_block stream_offset;data;Vlong(Int64.repr amount)]Kstop before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next) ->
  amount<=Int64.unsigned(stream_remaining initial).
Proof.
  intros ACTIVE CELLS LAYOUT BOUND AMOUNT RUN.
  destruct(actual_gateway_function_entry_ambient backend ge f_host_read
    [Vptr stream_block stream_offset;data;Vlong(Int64.repr amount)]Kstop before world events
    (Vint Int.zero)Kstop after next RUN)
    as[prefix[suffix[entry_memory[entry_world[environment[temporaries[allocated
      [EVENTS[AMBIENT[PREFIX[ENTRY REST]]]]]]]]]]].
  destruct(actual_read_entry_canonical ge(Vptr stream_block stream_offset)data amount
    entry_memory environment temporaries allocated ENTRY)as[ENV[TEMPS MEMORY]];subst.
  assert(ENTRY_CELLS:active entry_world /\gateway_stream_memory entry_memory stream_block stream_offset initial).
  { eapply gateway_ambient_run_ready with(backend:=backend)(ge:=ge)
      (ready:=fun memory world=>active world /\gateway_stream_memory memory stream_block stream_offset initial)
      (before:=before)(world:=world)(events:=prefix)(after:=entry_memory)(next:=entry_world)
      (source:=Callstate(Internal f_host_read)
        [Vptr stream_block stream_offset;data;Vlong(Int64.repr amount)]Kstop before).
    - intros previous current changed other[ALIVE INPUT]INTERFERENCE.
      destruct(gateway_private_ambient _ _ _ private _ _ _ _ ALIVE INTERFERENCE)as[LIVE FRAME].
      split;[exact LIVE|eapply gateway_stream_memory_closed;[exact BOUND|exact INPUT|exact FRAME]].
    - split;assumption.
    - exact AMBIENT.
    - exact PREFIX. }
  destruct ENTRY_CELLS as[LIVE INPUT].
  eapply actual_successful_read_body_passed_guard with(active:=active)(private:=private);
    [exact LIVE|exact INPUT|exact LAYOUT|exact BOUND|exact AMOUNT|exact REST].
Qed.
