(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Exact source byte assignments precede header word encoding. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteBytes.
From HostGateway Require Import GatewaySource GatewayMachine GatewayMemoryPrefixes GatewayFramedRuntime GatewayReadonly
  GatewayHeaderRuntime GatewayHeaderInitialization GatewayThreadRuntime GatewayStreamInterface GatewayWordsMemory.
Import ListNotations.
Open Scope Z_scope.

Section Initialization.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
  (native:World->block->Prop)(stable:World->block->Z->Prop)
  (discipline:option val->mem->World->Prop)(thread_errno:World->int).
Context(runtime:gateway_thread_runtime backend io native stable discipline thread_errno).
Variable ge:Clight.genv.
Variables(mode:option val)(object:Values.block)(held:list Values.block)(readonly:Values.block->Z->Prop)
  (reference:mem)(owner:World)(environment:env)(temporaries:temp_env).
Hypothesis ARRAY:environment!_header=Some(object,tarray tuchar 112).
Hypothesis DISJOINT:forall position,0<=position<112->~readonly object position.
Local Definition stage index:=gateway_header_stage native stable discipline mode object held readonly reference owner
  0 112(header_initial_prefix index).
Local Lemma stage_closed index:gateway_ambient_closed backend(stage index).
Proof. apply gateway_header_stage_ambient with(io:=io)(thread_errno:=thread_errno);exact runtime. Qed.

Lemma actual_header_initialization_script_bounded remaining:
  forall index memory,(index+remaining=112)%nat->
  gateway_memory_prefix backend ge(State f_host_exchange(header_source_after 112)Kstop environment temporaries memory)
    (stage 112)(stage index)(State f_host_exchange(header_source_after index)Kstop environment temporaries memory).
Proof.
  induction remaining as[|remaining IH];intros index memory LENGTH.
  - assert(SAME:index=112%nat)by lia;subst index;apply gateway_memory_identity.
  - assert(INDEX:(index<112)%nat)by lia.
    destruct((proj1(Forall_forall _ _))actual_header_initialization_table index ltac:(apply in_seq;lia))
      as(SEQUENCE & ASSIGNMENT & EXTEND & WRITTEN & BYTE).
    rewrite(actual_header_source_tail index INDEX),ASSIGNMENT.
    eapply gateway_memory_same with(following:=State f_host_exchange
      (Sassign(header_source_cell index)(Econst_int(header_initial_byte index)tint))
      (Kseq(header_source_after(S index))Kstop)environment temporaries memory);
      [apply stage_closed|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|].
    eapply gateway_memory_next with(following:=State f_host_exchange Sskip
      (Kseq(header_source_after(S index))Kstop)environment temporaries memory)(middle:=stage(S index)).
    + apply stage_closed.
    + cbn;tauto.
    + intros available current READY.
      destruct(gateway_header_stage_store backend io native stable discipline thread_errno runtime mode object held readonly reference owner
        0 112(header_initial_prefix index)available current(header_initial_byte index)
        ltac:(cbn;exact DISJOINT)READY ltac:(rewrite WRITTEN;exact INDEX)BYTE)
        as(changed & STORE & NEXT).
      exists changed;split.
      * cbn[gateway_replace_memory].
        eapply assignment_source_edge with(b:=object)(ofs:=Ptrofs.repr(Z.of_nat index))
          (v:=Vint(header_initial_byte index))(w:=Vint(header_initial_byte index)).
        -- apply actual_header_source_cell;assumption.
        -- apply old_expression_value;constructor.
        -- change(Some(Vint(Int.zero_ext 8(header_initial_byte index)))=Some(Vint(header_initial_byte index))).
           rewrite BYTE;reflexivity.
        -- eapply assign_loc_value;[reflexivity|]. unfold Mem.storev.
           rewrite Ptrofs.unsigned_repr by(change Ptrofs.max_unsigned with 18446744073709551615;lia).
           rewrite zle_true by(change Ptrofs.modulus with 18446744073709551616;cbn[size_chunk];lia).
           rewrite WRITTEN in STORE;change(0+Z.of_nat index)with(Z.of_nat index)in STORE;exact STORE.
      * unfold stage;rewrite EXTEND;exact NEXT.
    + eapply gateway_memory_same with(following:=State f_host_exchange(header_source_after(S index))Kstop
        environment temporaries memory);
        [apply stage_closed|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
      apply IH;lia.
Qed.

Theorem actual_header_initialization_before_boundary before world events terminal next:
  gateway_instruction_boundary terminal->
  gateway_header_resources native stable discipline mode object held readonly reference owner before world->
  Mem.range_perm before object 0 112 Cur Writable->
  gateway_steps backend ge
    (gateway_live(State f_host_exchange header_source_start Kstop environment temporaries before)world)events
    (gateway_live terminal next)->
  exists prefix suffix memory current,
    events=prefix++suffix /\Forall gateway_quiet_event prefix /\
    gateway_steps backend ge
      (gateway_live(State f_host_exchange header_source_start Kstop environment temporaries before)world)prefix
      (gateway_live(State f_host_exchange(header_source_after 112)Kstop environment temporaries memory)current) /\
    gateway_header_resources native stable discipline mode object held readonly reference owner memory current /\
    Mem.loadbytes memory object 0 112=Some(map byte_encoding header_initial_values) /\
    gateway_steps backend ge
      (gateway_live(State f_host_exchange(header_source_after 112)Kstop environment temporaries memory)current)suffix
      (gateway_live terminal next).
Proof.
  intros BOUNDARY RESOURCES PERMISSIONS RUN.
  assert(INITIAL:stage 0 before world).
  { split;[exact RESOURCES|]. apply gateway_bytes_initial;exact PERMISSIONS. }
  destruct(gateway_memory_prefix_cut backend ge _ _ _ _ before world events
    terminal next
    (actual_header_initialization_script_bounded 112 0 before eq_refl)BOUNDARY INITIAL RUN)
    as(prefix & suffix & memory & current & EVENTS & QUIET & PREFIX & [FINAL BYTES] & SUFFIX).
  cbn[gateway_replace_memory]in PREFIX,SUFFIX.
  exists prefix,suffix,memory,current;split;[exact EVENTS|]. split;[exact QUIET|]. split;[exact PREFIX|].
  split;[exact FINAL|]. split;[|exact SUFFIX].
  change(Mem.loadbytes memory object 0(Z.of_nat 112)=Some(map byte_encoding header_initial_values)).
  eapply gateway_bytes_complete;[change(gateway_bytes_ready object 0 112 header_initial_values memory)in BYTES;exact BYTES
    |exact actual_header_initialization_length].
Qed.

Theorem actual_header_initialization_before_call before world events definition arguments continuation after next:
  gateway_header_resources native stable discipline mode object held readonly reference owner before world->
  Mem.range_perm before object 0 112 Cur Writable->
  gateway_steps backend ge
    (gateway_live(State f_host_exchange header_source_start Kstop environment temporaries before)world)events
    (gateway_live(Callstate definition arguments continuation after)next)->
  exists prefix suffix memory current,
    events=prefix++suffix /\Forall gateway_quiet_event prefix /\
    gateway_steps backend ge
      (gateway_live(State f_host_exchange header_source_start Kstop environment temporaries before)world)prefix
      (gateway_live(State f_host_exchange(header_source_after 112)Kstop environment temporaries memory)current) /\
    gateway_header_resources native stable discipline mode object held readonly reference owner memory current /\
    Mem.loadbytes memory object 0 112=Some(map byte_encoding header_initial_values) /\
    gateway_steps backend ge
      (gateway_live(State f_host_exchange(header_source_after 112)Kstop environment temporaries memory)current)suffix
      (gateway_live(Callstate definition arguments continuation after)next).
Proof. intros;eapply actual_header_initialization_before_boundary;try eassumption;exact I. Qed.
End Initialization.
