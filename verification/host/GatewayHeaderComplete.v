(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The maintained exchange constructs its exact complete request header. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Ctypes Ctypesdefs Clight.
Require Import Machine Writers WriteBytes.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewayReadonly GatewayThreadRuntime
  GatewayStreamInterface GatewayMemoryPrefixes GatewayFramedRuntime GatewayFieldStores GatewayLayout GatewayExchangeSetup
  GatewayHeaderInitialization GatewayHeaderSource GatewayHeaderRuntime GatewayHeaderPacket GatewayHeaderCommands
  GatewayHeaderFields GatewayHeaderLoopPaths GatewayHeaderFieldMemory GatewayHeaderIteration GatewayHeaderLoop GatewayWordReceipt GatewayHeaderBoundary.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Definition gateway_complete_header command fault rows:=gateway_header_rows rows 0 8(gateway_request_prefix command fault).

Lemma gateway_header_rows_length rows remaining:
  forall index bytes,length(gateway_header_rows rows index remaining bytes)=(length bytes+12*remaining)%nat.
Proof.
  induction remaining as[|remaining IH];intros index bytes;[cbn;lia|].
  cbn[gateway_header_rows];rewrite IH.
  unfold header_row_bytes,gateway_native_bytes,put32_values,put64_values;
    rewrite !length_app,!length_map;cbn[length];lia.
Qed.

Theorem gateway_complete_header_length command fault rows:length(gateway_complete_header command fault rows)=112%nat.
Proof.
  unfold gateway_complete_header;rewrite gateway_header_rows_length.
  unfold gateway_request_prefix,gateway_native_bytes,put32_values;rewrite !length_app,!length_map;reflexivity.
Qed.

Theorem actual_header_functions:
  gateway_function_binding(Clight.globalenv prog)_host_put32(Internal f_host_put32) /\
  gateway_function_binding(Clight.globalenv prog)_host_put64(Internal f_host_put64).
Proof. split;apply gateway_actual_function_binding;vm_compute;reflexivity. Qed.

Theorem actual_header_field_size:sizeof(genv_cenv(Clight.globalenv prog))(Tstruct _host_field noattr)=40.
Proof. vm_compute;reflexivity. Qed.

Theorem actual_exchange_header_boundary_bytes {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    mode header held readonly reference origin allocation_before allocated environment temporaries
    object offset rows command fault before world events terminal next:
  gateway_header_boundary terminal->alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  environment!_header=Some(header,tarray tuchar 112)->temporaries!_fields=Some(Vptr object offset)->
  temporaries!_command=Some(Vint command)->temporaries!_fault=Some(Vint fault)->
  Ptrofs.unsigned offset+320<=Ptrofs.modulus->gateway_header_field_cells reference object offset rows->
  (forall position,Ptrofs.unsigned offset<=position<Ptrofs.unsigned offset+320->readonly object position)->
  (forall position,0<=position<112->~readonly header position)->
  gateway_header_resources native stable discipline mode header held readonly reference origin before world->
  Mem.range_perm before header 0 112 Cur Writable->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_exchange header_source_start Kstop environment temporaries before)world)events
    (gateway_live terminal next)->
  exists prefix suffix memory current final_temps,
    events=prefix++suffix /\Forall gateway_quiet_event prefix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange header_source_start Kstop environment temporaries before)world)prefix
      (gateway_live(State f_host_exchange header_fields_after Kstop environment final_temps memory)current) /\
    gateway_header_packet native stable discipline mode header held readonly reference origin
      (gateway_complete_header command fault rows)memory current /\
    Mem.loadbytes memory header 0 112=Some(inj_bytes(gateway_complete_header command fault rows)) /\
    (forall identifier,identifier<>_index->identifier<>_t'72->identifier<>_t'71->final_temps!identifier=temporaries!identifier) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange header_fields_after Kstop environment final_temps memory)current)suffix
      (gateway_live terminal next).
Proof.
  intros BOUNDARY ALLOC ARRAY FIELDS COMMAND FAULT SPAN CELLS COVER DISJOINT RESOURCES WRITABLE RUN.
  assert(LOCAL32:environment!_host_put32=None).
  { eapply actual_exchange_setup_unshadowed;[exact ALLOC|cbn;intuition discriminate]. }
  assert(LOCAL64:environment!_host_put64=None).
  { eapply actual_exchange_setup_unshadowed;[exact ALLOC|cbn;intuition discriminate]. }
  destruct actual_header_functions as[FUNCTION32 FUNCTION64].
  destruct actual_field_layout as[KIND[SIZE REST]].
  destruct(actual_header_initialization_before_boundary backend io native stable discipline thread_errno runtime(Clight.globalenv prog)
    mode header held readonly reference origin environment temporaries ARRAY DISJOINT before world events
    terminal next(gateway_header_boundary_instruction terminal BOUNDARY)RESOURCES WRITABLE RUN)
    as(p1 & r1 & m1 & w1 & E1 & Q1 & P1 & R1 & B1 & S1).
  assert(PACKET1:gateway_header_packet native stable discipline mode header held readonly reference origin gateway_request_magic m1 w1).
  { constructor;[exact R1| |cbn;lia|apply gateway_initialized_header_magic;exact B1].
    intros position RANGE;apply(gateway_header_permissions _ _ _ _ _ _ _ _ _ _ _ R1).
    apply(gateway_header_permissions _ _ _ _ _ _ _ _ _ _ _ RESOURCES);apply WRITABLE;exact RANGE. }
  destruct(actual_header_commands_before_boundary backend io native stable discipline thread_errno runtime(Clight.globalenv prog)
    mode header held readonly reference origin environment temporaries command fault m1 w1 r1 terminal next
    BOUNDARY ARRAY LOCAL32 FUNCTION32 COMMAND FAULT DISJOINT PACKET1 S1)
    as(p2 & r2 & m2 & w2 & E2 & Q2 & P2 & R2 & S2).
  set(prefix_bytes:=gateway_request_prefix command fault).
  set(packet:=gateway_header_packet native stable discipline mode header held readonly reference origin prefix_bytes).
  assert(CLOSED:gateway_ambient_closed backend packet).
  { apply gateway_header_packet_ambient with(io:=io)(thread_errno:=thread_errno);exact runtime. }
  destruct(gateway_memory_prefix_cut backend(Clight.globalenv prog)_ _ _ _ m2 w2 r2
    terminal next
    (actual_header_fields_enter backend(Clight.globalenv prog)packet CLOSED environment temporaries m2)(gateway_header_boundary_instruction terminal BOUNDARY)R2 S2)
    as(p3 & r3 & m3 & w3 & E3 & Q3 & P3 & R3 & S3).
  cbn[gateway_replace_memory]in P3,S3.
  set(loop_temps:=PTree.set _index(Vint Int.zero)temporaries).
  assert(LOOP_FIELDS:loop_temps!_fields=Some(Vptr object offset)).
  { unfold loop_temps;rewrite PTree.gso by discriminate;exact FIELDS. }
  assert(LOOP_INDEX:loop_temps!_index=Some(Vint(Int.repr(Z.of_nat 0)))).
  { unfold loop_temps;apply PTree.gss. }
  assert(PREFIX_LENGTH:length prefix_bytes=16%nat).
  { unfold prefix_bytes,gateway_request_prefix,gateway_native_bytes,put32_values;
      rewrite !length_app,!length_map;reflexivity. }
  destruct(actual_header_loop_boundary_bounded backend io native stable discipline thread_errno runtime(Clight.globalenv prog)
    mode header held readonly reference origin environment object offset rows ARRAY LOCAL32 LOCAL64 FUNCTION32 FUNCTION64
    actual_header_field_size KIND SIZE SPAN CELLS COVER DISJOINT 8 loop_temps 0 prefix_bytes m3 w3 r3
    terminal next BOUNDARY eq_refl LOOP_FIELDS LOOP_INDEX PREFIX_LENGTH R3 S3)
    as(p4 & suffix & memory & current & final_temps & E4 & Q4 & P4 & FINAL & FRAME & SUFFIX).
  exists(p1++p2++p3++p4),suffix,memory,current,final_temps.
  split;[rewrite E1,E2,E3,E4;repeat rewrite<-app_assoc;reflexivity|]. split.
  - apply Forall_app;split;[exact Q1|]. apply Forall_app;split;[exact Q2|]. apply Forall_app;split;assumption.
  - split.
    + eapply gateway_steps_append;[exact P1|]. eapply gateway_steps_append;[exact P2|].
      eapply gateway_steps_append;[exact P3|exact P4].
    + split;[exact FINAL|]. split.
      * pose proof(@gateway_packet_bytes World native stable discipline mode header held readonly reference origin _ memory current FINAL)as BYTES.
        change(Mem.loadbytes memory header 0(Z.of_nat(length(gateway_complete_header command fault rows)))=
          Some(inj_bytes(gateway_complete_header command fault rows)))in BYTES.
        rewrite gateway_complete_header_length in BYTES;exact BYTES.
      * split;[|exact SUFFIX]. intros identifier INDEX_NE KIND_NE SIZE_NE.
        rewrite(FRAME identifier INDEX_NE KIND_NE SIZE_NE);unfold loop_temps;rewrite PTree.gso by congruence;reflexivity.
Qed.

Theorem actual_exchange_header_bytes {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
    mode header held readonly reference origin allocation_before allocated environment temporaries
    object offset rows command fault before world events arguments continuation after next:
  alloc_variables(Clight.globalenv prog)empty_env allocation_before(fn_vars f_host_exchange)environment allocated->
  environment!_header=Some(header,tarray tuchar 112)->temporaries!_fields=Some(Vptr object offset)->
  temporaries!_command=Some(Vint command)->temporaries!_fault=Some(Vint fault)->
  Ptrofs.unsigned offset+320<=Ptrofs.modulus->gateway_header_field_cells reference object offset rows->
  (forall position,Ptrofs.unsigned offset<=position<Ptrofs.unsigned offset+320->readonly object position)->
  (forall position,0<=position<112->~readonly header position)->
  gateway_header_resources native stable discipline mode header held readonly reference origin before world->
  Mem.range_perm before header 0 112 Cur Writable->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_exchange header_source_start Kstop environment temporaries before)world)events
    (gateway_live(Callstate(Internal f_host_transfer)arguments continuation after)next)->
  exists prefix suffix memory current final_temps,
    events=prefix++suffix /\Forall gateway_quiet_event prefix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange header_source_start Kstop environment temporaries before)world)prefix
      (gateway_live(State f_host_exchange header_fields_after Kstop environment final_temps memory)current) /\
    gateway_header_packet native stable discipline mode header held readonly reference origin
      (gateway_complete_header command fault rows)memory current /\
    Mem.loadbytes memory header 0 112=Some(inj_bytes(gateway_complete_header command fault rows)) /\
    (forall identifier,identifier<>_index->identifier<>_t'72->identifier<>_t'71->final_temps!identifier=temporaries!identifier) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange header_fields_after Kstop environment final_temps memory)current)suffix
      (gateway_live(Callstate(Internal f_host_transfer)arguments continuation after)next).
Proof.
  intros;eapply actual_exchange_header_boundary_bytes with(io:=io)(thread_errno:=thread_errno);try eassumption;reflexivity.
Qed.
