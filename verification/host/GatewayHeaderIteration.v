(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: One real field iteration appends its original kind and size. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events
  Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps LocalAccess Writers.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewayReadonly GatewayThreadRuntime
  GatewayStreamInterface GatewayMemoryPrefixes GatewayFramedRuntime GatewayHeaderPacket GatewayHeaderRuntime
  GatewayHeaderExpression GatewayFieldStores GatewayHeaderFields GatewayHeaderLoopPaths GatewayHeaderFieldMemory GatewayWordReceipt GatewayHeaderBoundary.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Definition header_iteration_temps temporaries index kind size:=
  header_next_temps(header_size_temps(header_kind_temps temporaries kind)size)index.
Definition header_row_bytes bytes kind size:=bytes++gateway_native_bytes(put32_values kind)++gateway_native_bytes(put64_values size).

Section Iteration.
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

Theorem actual_header_fields_boundary_iteration temporaries index bytes before world events terminal next:
  gateway_header_boundary terminal->(index<8)%nat->temporaries!_fields=Some(Vptr object offset)->
  temporaries!_index=Some(Vint(Int.repr(Z.of_nat index)))->length bytes=(16+12*index)%nat->
  packet bytes before world->
  gateway_steps backend ge
    (gateway_live(State f_host_exchange header_fields_loop(Kseq header_fields_after Kstop)environment temporaries before)world)events
    (gateway_live terminal next)->
  exists prefix suffix memory current,
    events=prefix++suffix /\Forall gateway_quiet_event prefix /\
    gateway_steps backend ge
      (gateway_live(State f_host_exchange header_fields_loop(Kseq header_fields_after Kstop)environment temporaries before)world)prefix
      (gateway_live(State f_host_exchange header_fields_loop(Kseq header_fields_after Kstop)
        environment(header_iteration_temps temporaries index(fst(rows index))(snd(rows index)))memory)current) /\
    packet(header_row_bytes bytes(fst(rows index))(snd(rows index)))memory current /\
    gateway_steps backend ge
      (gateway_live(State f_host_exchange header_fields_loop(Kseq header_fields_after Kstop)
        environment(header_iteration_temps temporaries index(fst(rows index))(snd(rows index)))memory)current)suffix
      (gateway_live terminal next).
Proof.
  intros BOUNDARY BOUND FIELDS INDEX LENGTH READY RUN.
  assert(KIND_VALUE:forall memory current,packet bytes memory current->
    expression_value ge environment temporaries memory header_fields_kind_expr(Vint(fst(rows index)))).
  { intros memory current GOOD;eapply gateway_header_current_kind;
      [exact SIZEOF|exact KIND|exact FIELDS|exact INDEX|exact BOUND|exact SPAN|exact CELLS|exact COVER|exact GOOD]. }
  destruct(gateway_memory_prefix_cut backend ge _ _ _ _ before world events
    terminal next
    (actual_header_kind_path backend ge(packet bytes)(packet_closed bytes)environment temporaries before index(fst(rows index))
      BOUND INDEX KIND_VALUE)(gateway_header_boundary_instruction terminal BOUNDARY)READY RUN)
    as(p1 & r1 & m1 & w1 & E1 & Q1 & P1 & R1 & S1).
  cbn[gateway_replace_memory]in P1,S1.
  set(kind_temps:=header_kind_temps temporaries(fst(rows index))).
  assert(KIND_INDEX:kind_temps!_index=Some(Vint(Int.repr(Z.of_nat index)))).
  { unfold kind_temps,header_kind_temps;rewrite PTree.gso by discriminate;exact INDEX. }
  assert(KIND_FIELDS:kind_temps!_fields=Some(Vptr object offset)).
  { unfold kind_temps,header_kind_temps;rewrite PTree.gso by discriminate;exact FIELDS. }
  change(gateway_steps backend ge(gateway_live(State f_host_exchange
    (header_expression_statement(gateway_packet32(fst(rows index)))(header_fields_pointer 16)(Etempvar _t'72 tuint))
    (Kseq header_fields_size header_fields_cont)environment kind_temps m1)w1)r1
    (gateway_live terminal next))in S1.
  assert(POINTER32:forall memory current,packet bytes memory current->expression_value ge environment kind_temps memory
    (header_fields_pointer 16)(Vptr header(Ptrofs.repr(Z.of_nat(length bytes))))).
  { intros memory current GOOD;replace(Z.of_nat(length bytes))with(16+12*Z.of_nat index)by lia.
    apply actual_header_fields_pointer;[exact ARRAY|exact KIND_INDEX|lia|exact BOUND]. }
  destruct(actual_header_expression_before_boundary backend io native stable discipline thread_errno runtime ge mode header held
    readonly reference origin environment kind_temps DISJOINT(Kseq header_fields_size header_fields_cont)
    (gateway_packet32(fst(rows index)))(header_fields_pointer 16)(Etempvar _t'72 tuint)bytes m1 w1 r1 terminal next
    BOUNDARY eq_refl eq_refl LOCAL32 FUNCTION32 POINTER32
    ltac:(intros;apply old_expression_value,value_temp;unfold kind_temps,header_kind_temps;apply PTree.gss)
    ltac:(cbn[gateway_word_width];lia)R1 S1)
    as(p2 & r2 & m2 & w2 & E2 & Q2 & P2 & R2 & S2).
  set(kind_bytes:=bytes++gateway_native_bytes(put32_values(fst(rows index))))in *.
  assert(SIZE_VALUE:forall memory current,packet kind_bytes memory current->
    expression_value ge environment kind_temps memory header_fields_size_expr(Vlong(snd(rows index)))).
  { intros memory current GOOD;eapply gateway_header_current_size;
      [exact SIZEOF|exact SIZE|exact KIND_FIELDS|exact KIND_INDEX|exact BOUND|exact SPAN|exact CELLS|exact COVER|exact GOOD]. }
  destruct(gateway_memory_prefix_cut backend ge _ _ _ _ m2 w2 r2
    terminal next
    (actual_header_size_path backend ge(packet kind_bytes)(packet_closed kind_bytes)environment kind_temps m2
      (snd(rows index))SIZE_VALUE)(gateway_header_boundary_instruction terminal BOUNDARY)R2 S2)
    as(p3 & r3 & m3 & w3 & E3 & Q3 & P3 & R3 & S3).
  cbn[gateway_replace_memory]in P3,S3.
  set(size_temps:=header_size_temps kind_temps(snd(rows index))).
  assert(SIZE_INDEX:size_temps!_index=Some(Vint(Int.repr(Z.of_nat index)))).
  { unfold size_temps,header_size_temps;rewrite PTree.gso by discriminate;exact KIND_INDEX. }
  assert(KIND_LENGTH:length kind_bytes=(20+12*index)%nat).
  { unfold kind_bytes,gateway_native_bytes,put32_values;rewrite length_app,length_map,length_map;cbn[length];lia. }
  change(gateway_steps backend ge(gateway_live(State f_host_exchange
    (header_expression_statement(gateway_packet64(snd(rows index)))(header_fields_pointer 20)(Etempvar _t'71 tulong))
    header_fields_cont environment size_temps m3)w3)r3
    (gateway_live terminal next))in S3.
  assert(POINTER64:forall memory current,packet kind_bytes memory current->expression_value ge environment size_temps memory
    (header_fields_pointer 20)(Vptr header(Ptrofs.repr(Z.of_nat(length kind_bytes))))).
  { intros memory current GOOD;replace(Z.of_nat(length kind_bytes))with(20+12*Z.of_nat index)by lia.
    apply actual_header_fields_pointer;[exact ARRAY|exact SIZE_INDEX|lia|exact BOUND]. }
  destruct(actual_header_expression_before_boundary backend io native stable discipline thread_errno runtime ge mode header held
    readonly reference origin environment size_temps DISJOINT header_fields_cont
    (gateway_packet64(snd(rows index)))(header_fields_pointer 20)(Etempvar _t'71 tulong)kind_bytes m3 w3 r3 terminal next
    BOUNDARY eq_refl eq_refl LOCAL64 FUNCTION64 POINTER64
    ltac:(intros;apply old_expression_value,value_temp;unfold size_temps,header_size_temps;apply PTree.gss)
    ltac:(cbn[gateway_word_width];lia)R3 S3)
    as(p4 & r4 & m4 & w4 & E4 & Q4 & P4 & R4 & S4).
  set(final_bytes:=kind_bytes++gateway_native_bytes(put64_values(snd(rows index)))).
  change(packet final_bytes m4 w4)in R4.
  destruct(gateway_memory_prefix_cut backend ge _ _ _ _ m4 w4 r4
    terminal next
    (actual_header_increment_path backend ge(packet final_bytes)(packet_closed final_bytes)environment size_temps m4 index BOUND SIZE_INDEX)
    (gateway_header_boundary_instruction terminal BOUNDARY)R4 S4)as(p5 & suffix & memory & current & E5 & Q5 & P5 & FINAL & SUFFIX).
  cbn[gateway_replace_memory]in P5,SUFFIX.
  exists(p1++p2++p3++p4++p5),suffix,memory,current.
  split;[rewrite E1,E2,E3,E4,E5;repeat rewrite<-app_assoc;reflexivity|]. split.
  - apply Forall_app;split;[exact Q1|]. apply Forall_app;split;[exact Q2|].
    apply Forall_app;split;[exact Q3|]. apply Forall_app;split;assumption.
  - split.
    + eapply gateway_steps_append;[exact P1|]. eapply gateway_steps_append;[exact P2|].
      eapply gateway_steps_append;[exact P3|]. eapply gateway_steps_append;[exact P4|exact P5].
    + split;[unfold header_row_bytes;rewrite app_assoc;exact FINAL|exact SUFFIX].
Qed.

Theorem actual_header_fields_iteration temporaries index bytes before world events arguments continuation after next:
  (index<8)%nat->temporaries!_fields=Some(Vptr object offset)->
  temporaries!_index=Some(Vint(Int.repr(Z.of_nat index)))->length bytes=(16+12*index)%nat->
  packet bytes before world->
  gateway_steps backend ge
    (gateway_live(State f_host_exchange header_fields_loop(Kseq header_fields_after Kstop)environment temporaries before)world)events
    (gateway_live(Callstate(Internal f_host_transfer)arguments continuation after)next)->
  exists prefix suffix memory current,
    events=prefix++suffix /\Forall gateway_quiet_event prefix /\
    gateway_steps backend ge
      (gateway_live(State f_host_exchange header_fields_loop(Kseq header_fields_after Kstop)environment temporaries before)world)prefix
      (gateway_live(State f_host_exchange header_fields_loop(Kseq header_fields_after Kstop)
        environment(header_iteration_temps temporaries index(fst(rows index))(snd(rows index)))memory)current) /\
    packet(header_row_bytes bytes(fst(rows index))(snd(rows index)))memory current /\
    gateway_steps backend ge
      (gateway_live(State f_host_exchange header_fields_loop(Kseq header_fields_after Kstop)
        environment(header_iteration_temps temporaries index(fst(rows index))(snd(rows index)))memory)current)suffix
      (gateway_live(Callstate(Internal f_host_transfer)arguments continuation after)next).
Proof. intros;eapply actual_header_fields_boundary_iteration;try eassumption;reflexivity. Qed.
End Iteration.
