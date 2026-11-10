(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The real stream initializer produces the subsequent header caller inputs. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers Floats AST Values Memory Memdata Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayReadonly GatewayThreadRuntime GatewayStreamInterface
  GatewaySpawnResources GatewaySpawnRuntime GatewaySpawnActions GatewayPostSpawnContext GatewayPostSpawnCleanup GatewayPostSpawnSource
  GatewayStreamInitialization GatewayStreamSetupSource GatewayStreamSetupPaths GatewayStreamSetupContext GatewayPairContext
  GatewayMemoryPrefixes GatewayFramedRuntime GatewayHeaderInitialization.
Import ListNotations.
Open Scope Z_scope.

Lemma stream_setup_access values index:
  (index<8)%nat->access_mode(stream_setup_type index)=By_value(stream_initial_chunk(stream_initial_cell values index)).
Proof. intro BOUND;do 8(destruct index as[|index];[reflexivity|]);lia. Qed.

Section Setup.
Context {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno resources ipc builders genuine footprint
  (runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
  (descriptors:gateway_spawn_descriptor_runtime backend io native stable discipline resources ipc)
  (sdk:gateway_spawn_builder_runtime backend io native stable discipline resources builders genuine footprint).
Variables(readonly:Values.block->Z->Prop)(selected:Values.block->Prop)(reference:mem)(owner:World)
  (data control stream:Values.block)(data_left data_right control_left control_right:Z)(leases:list(Z*gateway_resource_descriptor))
  (environment:env)(temporaries:temp_env)(cli:int)(cancellation:val)(began:float).
Hypotheses(DATA_SELECTED:selected data)(CONTROL_SELECTED:selected control)(STREAM_SELECTED:selected stream)
  (STREAM_DATA:stream<>data)(STREAM_CONTROL:stream<>control)(STREAM_READONLY:forall position,~readonly stream position)
  (STREAM_RANGE:Mem.range_perm reference stream 0 48 Cur Freeable)
  (DATA:environment!_pair=Some(data,tarray tint 2))(CONTROL:environment!_control=Some(control,tarray tint 2))
  (STREAM:environment!_stream=Some(stream,Tstruct _host_stream noattr))
  (CLI:temporaries!_cli=Some(Vint cli))(CANCELLATION:temporaries!_cancellation=Some cancellation)(BEGAN:temporaries!_began=Some(Vfloat began))
  (POINTER:(exists object offset,cancellation=Vptr object offset)\/(exists word,cancellation=Vlong word)).
Local Definition values:=gateway_initial_stream data_left control_left cli cancellation began.
Local Definition stage:=gateway_stream_setup_stage native stable discipline resources builders genuine readonly selected reference owner
  data control stream data_left data_right control_left control_right leases values.
Local Definition context:=gateway_postspawn_context native stable discipline resources builders genuine readonly selected reference owner
  data control data_left data_right control_left control_right postspawn_empty_builders leases.
Local Lemma stage_closed index:(index<=8)%nat->gateway_ambient_closed backend(stage index).
Proof.
  intro BOUND;eapply gateway_stream_setup_ambient;[exact runtime|exact descriptors|exact sdk
    |exact DATA_SELECTED|exact CONTROL_SELECTED|exact STREAM_SELECTED|exact BOUND].
Qed.

Lemma actual_stream_setup_assignment index before world after:
  (index<8)%nat->stage index before world->
  Mem.store(stream_initial_chunk(stream_initial_cell values index))before stream
    (stream_initial_offset(stream_initial_cell values index))(stream_initial_value(stream_initial_cell values index))=Some after->
  store_edge(Clight.globalenv prog)
    (State f_host_exchange(stream_setup_assignment index)(Kseq(postspawn_after(6+index))Kstop)environment
      (stream_setup_temps data_left control_left(S index)temporaries)before)
    (State f_host_exchange Sskip(Kseq(postspawn_after(6+index))Kstop)environment
      (stream_setup_temps data_left control_left(S index)temporaries)after).
Proof.
  intros BOUND READY STORE;rewrite(actual_stream_setup_source index BOUND).
  destruct(stream_setup_expression_value(Clight.globalenv prog)environment
    (stream_setup_temps data_left control_left(S index)temporaries)before data_left control_left cli cancellation began index
    BOUND POINTER ltac:(intro SAME;subst index;apply PTree.gss)ltac:(intro SAME;subst index;apply PTree.gss)
    ltac:(rewrite stream_setup_temps_keeps by discriminate;exact CLI)
    ltac:(rewrite stream_setup_temps_keeps by discriminate;exact CANCELLATION)
    ltac:(rewrite stream_setup_temps_keeps by discriminate;exact BEGAN))as[EXPRESSION CAST].
  destruct(stream_initial_cell_bounds values index BOUND)as[LOW[HIGH ALIGN]].
  pose proof(size_chunk_pos(stream_initial_chunk(stream_initial_cell values index)))as POSITIVE.
  eapply assignment_source_edge with(b:=stream)(ofs:=Ptrofs.repr(stream_initial_offset(stream_initial_cell values index)))
    (v:=stream_setup_raw_value values index)(w:=stream_initial_value(stream_initial_cell values index)).
  - eapply stream_setup_location;[exact STREAM|apply stream_setup_member_layout;exact BOUND].
  - exact EXPRESSION.
  - exact CAST.
  - apply assign_loc_value with(chunk:=stream_initial_chunk(stream_initial_cell values index));[apply stream_setup_access;exact BOUND|].
    unfold Mem.storev;rewrite Ptrofs.unsigned_repr by(change Ptrofs.max_unsigned with 18446744073709551615;lia).
    rewrite zle_true by(change Ptrofs.modulus with 18446744073709551616;lia);exact STORE.
Qed.

Theorem actual_stream_setup_script_bounded remaining:
  forall index memory,(index+remaining=8)%nat->
  gateway_memory_prefix backend(Clight.globalenv prog)
    (State f_host_exchange header_source_start Kstop environment(stream_setup_temps data_left control_left 8 temporaries)memory)
    (stage 8)(stage index)
    (State f_host_exchange(postspawn_after(5+index))Kstop environment(stream_setup_temps data_left control_left index temporaries)memory).
Proof.
  induction remaining as[|remaining IH];intros index memory COUNT.
  - assert(index=8)%nat by lia;subst index;rewrite<-actual_stream_setup_header_tail;apply gateway_memory_identity.
  - assert(BOUND:(index<8)%nat)by lia.
    eapply gateway_memory_prefix_compose.
    + apply actual_stream_setup_field_prefix with(data:=data)(control:=control)(data_right:=data_right)(control_right:=control_right);
        [apply stage_closed;lia|exact DATA|exact CONTROL| |exact BOUND].
      intros before world[READY PREFIX];destruct READY as[SIDE VALID GENUINE BUILDERS FAMILY DATA_CELLS CONTROL_CELLS LEASES];split;assumption.
    + eapply gateway_memory_next with(following:=State f_host_exchange Sskip(Kseq(postspawn_after(6+index))Kstop)environment
        (stream_setup_temps data_left control_left(S index)temporaries)memory)(middle:=stage(S index)).
      * apply stage_closed;lia.
      * rewrite(actual_stream_setup_source index BOUND);cbn;tauto.
      * intros before world READY.
        destruct(gateway_stream_setup_next backend io native stable discipline thread_errno resources builders genuine footprint runtime sdk
          readonly selected reference owner data control stream data_left data_right control_left control_right leases values
          STREAM_SELECTED STREAM_DATA STREAM_CONTROL STREAM_READONLY STREAM_RANGE index before world BOUND POINTER READY)
          as[after[STORE NEXT]].
        exists after;split;[cbn[gateway_replace_memory];exact(actual_stream_setup_assignment index before world after BOUND READY STORE)|exact NEXT].
      * eapply gateway_memory_same with(following:=State f_host_exchange(postspawn_after(6+index))Kstop environment
          (stream_setup_temps data_left control_left(S index)temporaries)memory);
          [apply stage_closed;lia|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|].
        apply IH;lia.
Qed.

Theorem actual_stream_setup before world events terminal next:
  gateway_instruction_boundary terminal->context before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_exchange(postspawn_after 5)Kstop environment temporaries before)world)events(gateway_live terminal next)->
  exists prefix suffix memory current,
    events=prefix++suffix /\Forall gateway_quiet_event prefix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange(postspawn_after 5)Kstop environment temporaries before)world)prefix
      (gateway_live(State f_host_exchange header_source_start Kstop environment
        (stream_setup_temps data_left control_left 8 temporaries)memory)current) /\
    context memory current /\gateway_stream_memory memory stream Ptrofs.zero values /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_exchange header_source_start Kstop environment
        (stream_setup_temps data_left control_left 8 temporaries)memory)current)suffix(gateway_live terminal next).
Proof.
  intros BOUNDARY READY RUN.
  assert(INITIAL:stage 0 before world).
  { split;[exact READY|intros index ABSENT;lia]. }
  destruct(gateway_memory_prefix_cut backend(Clight.globalenv prog)_ _ _ _ before world events terminal next
    (actual_stream_setup_script_bounded 8 0 before eq_refl)BOUNDARY INITIAL RUN)
    as(prefix & suffix & memory & current & EVENTS & QUIET & PREFIX & [FINAL CELLS] & SUFFIX).
  cbn[gateway_replace_memory]in PREFIX,SUFFIX.
  exists prefix,suffix,memory,current;split;[exact EVENTS|]. split;[exact QUIET|]. split;[exact PREFIX|]. split;[exact FINAL|].
  split;[apply gateway_stream_prefix_complete;exact CELLS|exact SUFFIX].
Qed.
End Setup.
