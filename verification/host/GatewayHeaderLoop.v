(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual bounded loop writes exactly eight retained descriptors. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Ctypes Ctypesdefs Clight.
Require Import Machine Writers.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewayReadonly GatewayThreadRuntime
  GatewayStreamInterface GatewayMemoryPrefixes GatewayFramedRuntime GatewayFieldStores GatewayHeaderPacket
  GatewayHeaderRuntime GatewayHeaderFields GatewayHeaderLoopPaths GatewayHeaderFieldMemory GatewayHeaderIteration GatewayWordReceipt GatewayHeaderBoundary.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Fixpoint gateway_header_rows(rows:nat->int*int64)(index remaining:nat)(bytes:list Byte.int):list Byte.int:=
  match remaining with O=>bytes|S rest=>gateway_header_rows rows(S index)rest
    (header_row_bytes bytes(fst(rows index))(snd(rows index)))end.
Definition gateway_header_temps_frame(before after:temp_env):Prop:=forall identifier,
  identifier<>_index->identifier<>_t'72->identifier<>_t'71->after!identifier=before!identifier.

Lemma gateway_header_iteration_frame temporaries index kind size:
  gateway_header_temps_frame temporaries(header_iteration_temps temporaries index kind size).
Proof.
  unfold gateway_header_temps_frame,header_iteration_temps,header_next_temps,header_size_temps,header_kind_temps.
  intros identifier INDEX KIND SIZE;rewrite !PTree.gso by congruence;reflexivity.
Qed.

Section Loop.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
  (native:World->block->Prop)(stable:World->block->Z->Prop)
  (discipline:option val->mem->World->Prop)(thread_errno:World->int).
Context(runtime:gateway_thread_runtime backend io native stable discipline thread_errno).
Variable ge:Clight.genv.
Variables(mode:option val)(header:Values.block)(held:list Values.block)(readonly:Values.block->Z->Prop)
  (reference:mem)(origin:World)(environment:env)(object:Values.block)(offset:ptrofs)(rows:nat->int*int64).
Hypotheses(ARRAY:environment!_header=Some(header,tarray tuchar 112))
  (LOCAL32:environment!_host_put32=None)(LOCAL64:environment!_host_put64=None)
  (FUNCTION32:gateway_function_binding ge _host_put32(Internal f_host_put32))
  (FUNCTION64:gateway_function_binding ge _host_put64(Internal f_host_put64))
  (SIZEOF:sizeof(genv_cenv ge)(Tstruct _host_field noattr)=40)
  (KIND:field_member_layout ge _kind 0)(SIZE:field_member_layout ge _size 8)
  (SPAN:Ptrofs.unsigned offset+320<=Ptrofs.modulus)
  (CELLS:gateway_header_field_cells reference object offset rows)
  (COVER:forall position,Ptrofs.unsigned offset<=position<Ptrofs.unsigned offset+320->readonly object position)
  (DISJOINT:forall position,0<=position<112->~readonly header position).
Local Definition packet bytes:=gateway_header_packet native stable discipline mode header held readonly reference origin bytes.
Local Lemma packet_closed bytes:gateway_ambient_closed backend(packet bytes).
Proof. apply gateway_header_packet_ambient with(io:=io)(thread_errno:=thread_errno);exact runtime. Qed.

Theorem actual_header_loop_boundary_bounded remaining:
  forall temporaries index bytes before world events terminal next,
  gateway_header_boundary terminal->(index+remaining=8)%nat->temporaries!_fields=Some(Vptr object offset)->
  temporaries!_index=Some(Vint(Int.repr(Z.of_nat index)))->length bytes=(16+12*index)%nat->
  packet bytes before world->
  gateway_steps backend ge
    (gateway_live(State f_host_exchange header_fields_loop(Kseq header_fields_after Kstop)environment temporaries before)world)events
    (gateway_live terminal next)->
  exists prefix suffix memory current final_temps,
    events=prefix++suffix /\Forall gateway_quiet_event prefix /\
    gateway_steps backend ge
      (gateway_live(State f_host_exchange header_fields_loop(Kseq header_fields_after Kstop)environment temporaries before)world)prefix
      (gateway_live(State f_host_exchange header_fields_after Kstop environment final_temps memory)current) /\
    packet(gateway_header_rows rows index remaining bytes)memory current /\gateway_header_temps_frame temporaries final_temps /\
    gateway_steps backend ge
      (gateway_live(State f_host_exchange header_fields_after Kstop environment final_temps memory)current)suffix
      (gateway_live terminal next).
Proof.
  induction remaining as[|remaining IH];intros temporaries index bytes before world events terminal next
    BOUNDARY COUNT FIELDS INDEX LENGTH READY RUN.
  - assert(SAME:index=8%nat)by lia;subst index.
    destruct(gateway_memory_prefix_cut backend ge _ _ _ _ before world events
      terminal next
      (actual_header_fields_exit backend ge(packet bytes)(packet_closed bytes)environment temporaries before INDEX)
      (gateway_header_boundary_instruction terminal BOUNDARY)READY RUN)as(prefix & suffix & memory & current & EVENTS & QUIET & PREFIX & FINAL & SUFFIX).
    cbn[gateway_replace_memory]in PREFIX,SUFFIX.
    exists prefix,suffix,memory,current,temporaries;split;[exact EVENTS|]. split;[exact QUIET|].
    split;[exact PREFIX|]. split;[exact FINAL|]. split;[intros identifier A B C;reflexivity|exact SUFFIX].
  - assert(BOUND:(index<8)%nat)by lia.
    destruct(actual_header_fields_boundary_iteration backend io native stable discipline thread_errno runtime ge mode header held
      readonly reference origin environment object offset rows ARRAY LOCAL32 LOCAL64 FUNCTION32 FUNCTION64 SIZEOF KIND SIZE
      SPAN CELLS COVER DISJOINT temporaries index bytes before world events terminal next
      BOUNDARY BOUND FIELDS INDEX LENGTH READY RUN)
      as(first & rest & middle & middle_world & EVENTS1 & QUIET1 & FIRST & MIDDLE & REST).
    set(temps:=header_iteration_temps temporaries index(fst(rows index))(snd(rows index))).
    assert(NEXT_FIELDS:temps!_fields=Some(Vptr object offset)).
    { unfold temps,header_iteration_temps,header_next_temps,header_size_temps,header_kind_temps;
        rewrite !PTree.gso by discriminate;exact FIELDS. }
    assert(NEXT_INDEX:temps!_index=Some(Vint(Int.repr(Z.of_nat(S index))))).
    { unfold temps,header_iteration_temps,header_next_temps;apply PTree.gss. }
    assert(NEXT_LENGTH:length(header_row_bytes bytes(fst(rows index))(snd(rows index)))=(16+12*S index)%nat).
    { unfold header_row_bytes,gateway_native_bytes,put32_values,put64_values;
        rewrite !length_app,!length_map;cbn[length];lia. }
    destruct(IH temps(S index)(header_row_bytes bytes(fst(rows index))(snd(rows index)))middle middle_world rest
      terminal next BOUNDARY ltac:(lia)NEXT_FIELDS NEXT_INDEX NEXT_LENGTH MIDDLE REST)
      as(second & suffix & memory & current & final_temps & EVENTS2 & QUIET2 & SECOND & FINAL & FRAME & SUFFIX).
    exists(first++second),suffix,memory,current,final_temps.
    split;[rewrite EVENTS1,EVENTS2,app_assoc;reflexivity|]. split;[apply Forall_app;split;assumption|].
    split;[eapply gateway_steps_append;[exact FIRST|exact SECOND]|]. split;[exact FINAL|]. split;[|exact SUFFIX].
    intros identifier INDEX_NE KIND_NE SIZE_NE;rewrite(FRAME identifier INDEX_NE KIND_NE SIZE_NE).
    apply gateway_header_iteration_frame;assumption.
Qed.

Theorem actual_header_loop_bounded remaining:
  forall temporaries index bytes before world events arguments continuation after next,
  (index+remaining=8)%nat->temporaries!_fields=Some(Vptr object offset)->
  temporaries!_index=Some(Vint(Int.repr(Z.of_nat index)))->length bytes=(16+12*index)%nat->
  packet bytes before world->
  gateway_steps backend ge
    (gateway_live(State f_host_exchange header_fields_loop(Kseq header_fields_after Kstop)environment temporaries before)world)events
    (gateway_live(Callstate(Internal f_host_transfer)arguments continuation after)next)->
  exists prefix suffix memory current final_temps,
    events=prefix++suffix /\Forall gateway_quiet_event prefix /\
    gateway_steps backend ge
      (gateway_live(State f_host_exchange header_fields_loop(Kseq header_fields_after Kstop)environment temporaries before)world)prefix
      (gateway_live(State f_host_exchange header_fields_after Kstop environment final_temps memory)current) /\
    packet(gateway_header_rows rows index remaining bytes)memory current /\gateway_header_temps_frame temporaries final_temps /\
    gateway_steps backend ge
      (gateway_live(State f_host_exchange header_fields_after Kstop environment final_temps memory)current)suffix
      (gateway_live(Callstate(Internal f_host_transfer)arguments continuation after)next).
Proof. intros;eapply actual_header_loop_boundary_bounded;try eassumption;reflexivity. Qed.
End Loop.
