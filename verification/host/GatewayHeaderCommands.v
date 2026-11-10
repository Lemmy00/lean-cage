(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual request command and fault extend the fixed magic bytes. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Maps Integers AST Values Memory Memdata Events Ctypes Ctypesdefs Clight.
Require Import WriteBytes Writers.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewayReadonly GatewayThreadRuntime
  GatewayStreamInterface GatewayHeaderInitialization GatewayHeaderRuntime GatewayHeaderPacket GatewayHeaderMarshal
  GatewayWordReceipt GatewayHeaderBoundary.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Definition gateway_request_magic:=map Byte.repr[76;67;72;82;69;81;49;0].
Definition gateway_request_prefix command fault:=gateway_request_magic++gateway_native_bytes(put32_values command)++
  gateway_native_bytes(put32_values fault).

Theorem actual_header_command_shapes:
  header_source_after 112=Ssequence(header_word32_statement 8 _command)(header_source_after 113) /\
  header_source_after 113=Ssequence(header_word32_statement 12 _fault)(header_source_after 114).
Proof. split;reflexivity. Qed.

Lemma gateway_initialized_header_magic memory object:
  Mem.loadbytes memory object 0 112=Some(map byte_encoding header_initial_values)->
  Mem.loadbytes memory object 0 8=Some(inj_bytes gateway_request_magic).
Proof.
  intro INITIAL.
  destruct(Mem.loadbytes_split memory object 0 8 104 _ INITIAL ltac:(lia)ltac:(lia))
    as[first[rest[FIRST[REST BYTES]]]].
  pose proof(Mem.loadbytes_length _ _ _ _ _ FIRST)as LENGTH;change(length first=8%nat)in LENGTH.
  apply(f_equal(firstn 8))in BYTES.
  rewrite firstn_app,LENGTH,Nat.sub_diag,firstn_O,app_nil_r in BYTES.
  assert(TAKE:firstn 8 first=first)by(apply firstn_all2;lia).
  rewrite TAKE in BYTES.
  change(inj_bytes gateway_request_magic=first)in BYTES;rewrite BYTES;exact FIRST.
Qed.

Theorem actual_header_commands_before_boundary {World Event}(backend:gateway_backend World Event)
    io native stable discipline thread_errno
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)ge
    mode object held readonly reference owner environment temporaries command fault before world events
    terminal next:
  gateway_header_boundary terminal->environment!_header=Some(object,tarray tuchar 112)->environment!_host_put32=None->
  gateway_function_binding ge _host_put32(Internal f_host_put32)->
  temporaries!_command=Some(Vint command)->temporaries!_fault=Some(Vint fault)->
  (forall position,0<=position<112->~readonly object position)->
  gateway_header_packet native stable discipline mode object held readonly reference owner gateway_request_magic before world->
  gateway_steps backend ge
    (gateway_live(State f_host_exchange(header_source_after 112)Kstop environment temporaries before)world)events
    (gateway_live terminal next)->
  exists prefix suffix memory current,
    events=prefix++suffix /\Forall gateway_quiet_event prefix /\
    gateway_steps backend ge
      (gateway_live(State f_host_exchange(header_source_after 112)Kstop environment temporaries before)world)prefix
      (gateway_live(State f_host_exchange(header_source_after 114)Kstop environment temporaries memory)current) /\
    gateway_header_packet native stable discipline mode object held readonly reference owner
      (gateway_request_prefix command fault)memory current /\
    gateway_steps backend ge
      (gateway_live(State f_host_exchange(header_source_after 114)Kstop environment temporaries memory)current)suffix
      (gateway_live terminal next).
Proof.
  intros BOUNDARY ARRAY LOCAL FUNCTION COMMAND FAULT DISJOINT PACKET RUN.
  rewrite(proj1 actual_header_command_shapes)in RUN.
  destruct(actual_header_put32_before_boundary backend io native stable discipline thread_errno runtime ge mode object held
    readonly reference owner environment temporaries ARRAY DISJOINT(header_source_after 113)_command command gateway_request_magic
    before world events terminal next BOUNDARY LOCAL FUNCTION COMMAND ltac:(cbn;lia)PACKET RUN)
    as(first & rest & middle & middle_world & EVENTS1 & QUIET1 & FIRST & MIDDLE & REST).
  rewrite(proj2 actual_header_command_shapes)in REST.
  change 12 with(Z.of_nat(length(gateway_request_magic++gateway_native_bytes(put32_values command))))in REST.
  destruct(actual_header_put32_before_boundary backend io native stable discipline thread_errno runtime ge mode object held
    readonly reference owner environment temporaries ARRAY DISJOINT(header_source_after 114)_fault fault
    (gateway_request_magic++gateway_native_bytes(put32_values command))middle middle_world rest
    terminal next BOUNDARY LOCAL FUNCTION FAULT ltac:(cbn;lia)MIDDLE REST)
    as(second & suffix & memory & current & EVENTS2 & QUIET2 & SECOND & FINAL & SUFFIX).
  exists(first++second),suffix,memory,current;split;[rewrite EVENTS1,EVENTS2,app_assoc;reflexivity|].
  split;[apply Forall_app;split;assumption|]. split.
  - rewrite(proj1 actual_header_command_shapes).
    eapply gateway_steps_append;[exact FIRST|].
    rewrite(proj2 actual_header_command_shapes);exact SECOND.
  - split;[unfold gateway_request_prefix;rewrite app_assoc;exact FINAL|exact SUFFIX].
Qed.

Theorem actual_header_commands_before_transfer {World Event}(backend:gateway_backend World Event)
    io native stable discipline thread_errno
    (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)ge
    mode object held readonly reference owner environment temporaries command fault before world events
    arguments continuation after next:
  environment!_header=Some(object,tarray tuchar 112)->environment!_host_put32=None->
  gateway_function_binding ge _host_put32(Internal f_host_put32)->
  temporaries!_command=Some(Vint command)->temporaries!_fault=Some(Vint fault)->
  (forall position,0<=position<112->~readonly object position)->
  gateway_header_packet native stable discipline mode object held readonly reference owner gateway_request_magic before world->
  gateway_steps backend ge
    (gateway_live(State f_host_exchange(header_source_after 112)Kstop environment temporaries before)world)events
    (gateway_live(Callstate(Internal f_host_transfer)arguments continuation after)next)->
  exists prefix suffix memory current,
    events=prefix++suffix /\Forall gateway_quiet_event prefix /\
    gateway_steps backend ge
      (gateway_live(State f_host_exchange(header_source_after 112)Kstop environment temporaries before)world)prefix
      (gateway_live(State f_host_exchange(header_source_after 114)Kstop environment temporaries memory)current) /\
    gateway_header_packet native stable discipline mode object held readonly reference owner
      (gateway_request_prefix command fault)memory current /\
    gateway_steps backend ge
      (gateway_live(State f_host_exchange(header_source_after 114)Kstop environment temporaries memory)current)suffix
      (gateway_live(Callstate(Internal f_host_transfer)arguments continuation after)next).
Proof. intros;eapply actual_header_commands_before_boundary;try eassumption;reflexivity. Qed.
