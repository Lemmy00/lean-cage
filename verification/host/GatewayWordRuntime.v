(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Actual word stores/free preserve coupled runtime ownership. *)
From Stdlib Require Import ZArith Lia List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayFrames GatewayPure
  GatewayStreamInterface GatewayStreamWord GatewayFramedRuntime GatewayThreadRuntime.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Section WordRuntime.
Context {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
  (io:Event->option gateway_native_io)(native_private:World->block->Prop)
  (stable_readonly:World->block->Z->Prop)(discipline:option Values.val->Memory.mem->World->Prop)
  (thread_errno:World->int).
Context(runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno).

Definition gateway_word_readonly_owned(readonly:block->Z->Prop)memory world :Prop:=
  forall object position,readonly object position ->Mem.perm memory object position Cur Readable /\
    (native_private world object \/stable_readonly world object position).

Definition gateway_word_resources mode buffer output held readonly original memory world :Prop:=
  discipline mode memory world /\native_private world buffer /\native_private world output /\
  Mem.valid_block memory buffer /\Mem.valid_block memory output /\
  (forall object,In object held->Mem.valid_block memory object /\native_private world object) /\
  gateway_word_readonly_owned readonly memory world /\Mem.unchanged_on readonly original memory.

Definition gateway_word_stage mode buffer output held readonly original property memory world :Prop:=
  gateway_word_resources mode buffer output held readonly original memory world /\property memory.

Definition gateway_word_protected buffer output offset readonly object position :Prop:=
  gateway_word_store_region buffer output offset object position \/readonly object position.

Lemma gateway_word_resources_ambient mode buffer output held readonly original before world after next :
  gateway_word_resources mode buffer output held readonly original before world ->
  gateway_interference backend before world after next ->
  gateway_word_resources mode buffer output held readonly original after next /\
  gateway_native_frame native_private stable_readonly gateway_native_no_output world before after.
Proof.
  intros[SIDE[BUFFER[OUTPUT[BUFFER_LIVE[OUTPUT_LIVE[HELD[READONLY FRAME]]]]]]]INTERFERENCE.
  destruct(gateway_thread_ambient _ _ _ _ _ _ runtime mode _ _ _ _ SIDE INTERFERENCE)
    as[NEXT_SIDE[[RETAIN_NATIVE RETAIN_STABLE]STEP_FRAME]].
  assert(READ_FRAME:Mem.unchanged_on readonly before after).
  { eapply gateway_native_frame_restrict;[exact STEP_FRAME| |intros;unfold gateway_native_no_output;tauto].
    intros object position READ;exact(proj2(READONLY object position READ)). }
  split;[|exact STEP_FRAME]. unfold gateway_word_resources.
  split;[exact NEXT_SIDE|]. split;[apply RETAIN_NATIVE;assumption|].
  split;[apply RETAIN_NATIVE;assumption|].
  split;[eapply Mem.valid_block_unchanged_on;eassumption|].
  split;[eapply Mem.valid_block_unchanged_on;eassumption|].
  split.
  - intros object MEMBER;destruct(HELD object MEMBER)as[LIVE PRIVATE];split.
    + eapply Mem.valid_block_unchanged_on;eassumption.
    + apply RETAIN_NATIVE;assumption.
  - split;[|eapply Mem.unchanged_on_trans;eassumption].
    intros object position READ;destruct(READONLY object position READ)as[READABLE CAPABILITY];split.
    + eapply Mem.perm_unchanged_on;[exact READ_FRAME|exact READ|exact READABLE].
    + destruct CAPABILITY as[NATIVE|STABLE].
      * left;apply RETAIN_NATIVE;[eapply Mem.perm_valid_block;exact READABLE|exact NATIVE].
      * right;apply RETAIN_STABLE;assumption.
Qed.

Lemma gateway_word_stage_ambient mode buffer output held offset readonly original property :
  gateway_region_closed(gateway_word_protected buffer output offset readonly)property ->
  gateway_ambient_closed backend(gateway_word_stage mode buffer output held readonly original property).
Proof.
  intros CLOSED before world after next[RESOURCES PROPERTY]INTERFERENCE.
  destruct(gateway_word_resources_ambient _ _ _ _ _ _ _ _ _ _ RESOURCES INTERFERENCE)as[NEXT FRAME].
  split;[exact NEXT|]. eapply CLOSED;[exact PROPERTY|].
  eapply gateway_native_frame_restrict;[exact FRAME| |intros;unfold gateway_native_no_output;tauto].
  intros object position[REGION|READ].
  - destruct RESOURCES as[_[BUFFER[OUTPUT _]]]. destruct REGION as[[SAME RANGE]|[SAME RANGE]];
      subst object;left;assumption.
  - destruct RESOURCES as[_[_[_[_[_[_[READONLY _]]]]]]].
    exact(proj2(READONLY object position READ)).
Qed.

Lemma gateway_word_stage_region_closed buffer output offset readonly property :
  gateway_region_closed(gateway_word_store_region buffer output offset)property ->
  gateway_region_closed(gateway_word_protected buffer output offset readonly)property.
Proof.
  intros CLOSED before after GOOD FRAME;apply(CLOSED before after GOOD).
  eapply Mem.unchanged_on_implies;[exact FRAME|intros;left;assumption].
Qed.

Lemma gateway_word_resources_store mode buffer output held readonly original before world stored offset value :
  gateway_word_resources mode buffer output held readonly original before world ->
  (forall position,offset<=position<offset+8->~readonly output position) ->
  Mem.store Mint64 before output offset(Vlong value)=Some stored ->
  gateway_word_resources mode buffer output held readonly original stored world.
Proof.
  intros[SIDE[BUFFER[OUTPUT[BUFFER_LIVE[OUTPUT_LIVE[HELD[READONLY FRAME]]]]]]]DISJOINT STORE.
  assert(STORE_FRAME:Mem.unchanged_on readonly before stored).
  { eapply Mem.store_unchanged_on;[exact STORE|]. intros position RANGE;apply DISJOINT;exact RANGE. }
  split;[eapply gateway_thread_native_store;[exact runtime|exact SIDE|exact OUTPUT|exact STORE]|].
  split;[exact BUFFER|]. split;[exact OUTPUT|].
  split;[eapply Mem.store_valid_block_1;eassumption|].
  split;[eapply Mem.store_valid_block_1;eassumption|].
  split.
  - intros object MEMBER;destruct(HELD object MEMBER)as[LIVE PRIVATE];split;
      [eapply Mem.store_valid_block_1;eassumption|exact PRIVATE].
  - split;[|eapply Mem.unchanged_on_trans;eassumption].
    intros object position READ;destruct(READONLY object position READ)as[READABLE CAPABILITY];split.
    + eapply Mem.perm_store_1;eassumption.
    + exact CAPABILITY.
Qed.

Lemma gateway_word_resources_free mode buffer output held readonly original before world freed :
  gateway_word_resources mode buffer output held readonly original before world ->
  (forall position,~readonly buffer position) ->Mem.free before buffer 0 8=Some freed ->
  gateway_word_resources mode buffer output held readonly original freed world.
Proof.
  intros[SIDE[BUFFER[OUTPUT[BUFFER_LIVE[OUTPUT_LIVE[HELD[READONLY FRAME]]]]]]]DISJOINT FREE.
  assert(FREE_FRAME:Mem.unchanged_on readonly before freed).
  { eapply Mem.free_unchanged_on;[exact FREE|]. intros position RANGE;apply DISJOINT. }
  split;[eapply gateway_thread_native_free;[exact runtime|exact SIDE|exact BUFFER|exact FREE]|].
  split;[exact BUFFER|]. split;[exact OUTPUT|].
  split;[eapply Mem.valid_block_free_1;eassumption|].
  split;[eapply Mem.valid_block_free_1;eassumption|].
  split.
  - intros object MEMBER;destruct(HELD object MEMBER)as[LIVE PRIVATE];split;
      [eapply Mem.valid_block_free_1;eassumption|exact PRIVATE].
  - split;[|eapply Mem.unchanged_on_trans;eassumption].
    intros object position READ;destruct(READONLY object position READ)as[READABLE CAPABILITY];split.
    + eapply Mem.perm_unchanged_on;[exact FREE_FRAME|exact READ|exact READABLE].
    + exact CAPABILITY.
Qed.

Lemma gateway_word_runtime_store_path mode buffer arguments output ofs value held original readonly memory :
  word_output arguments=Vptr output ofs ->output<>buffer ->Ptrofs.unsigned ofs+8<=Ptrofs.modulus ->
  (forall position,Ptrofs.unsigned ofs<=position<Ptrofs.unsigned ofs+8->~readonly output position) ->
  (forall position,~readonly buffer position) ->
  gateway_runtime_path backend ge
    (gateway_word_stage mode buffer output held readonly original
      (gateway_word_store_ready buffer output(Ptrofs.unsigned ofs)))
    (Returnstate(Vlong value)(gateway_word_get_cont buffer arguments)memory)(Vint Int.zero)
    (gateway_word_stage mode buffer output held readonly original
      (fun after=>Mem.load Mint64 after output(Ptrofs.unsigned ofs)=Some(Vlong value))).
Proof.
  intros OUTPUT SEPARATE BOUND OUTSIDE AVOIDS.
  eapply gateway_runtime_same with(next:=State f_host_word Sskip
    (Kseq gateway_word_assignment(Kseq gateway_word_return Kstop))(gateway_word_environment buffer)
    (PTree.set _t'3(Vlong value)(gateway_word_after_read_parameters arguments))memory).
  - eapply gateway_word_stage_ambient with(offset:=Ptrofs.unsigned ofs).
    apply gateway_word_stage_region_closed,gateway_word_store_ready_closed.
  - cbn;tauto.
  - intros another world GOOD;apply unchanged_store_edge,edge_returnstate.
  - eapply gateway_runtime_same with(next:=State f_host_word gateway_word_assignment
      (Kseq gateway_word_return Kstop)(gateway_word_environment buffer)
      (PTree.set _t'3(Vlong value)(gateway_word_after_read_parameters arguments))memory).
    + eapply gateway_word_stage_ambient with(offset:=Ptrofs.unsigned ofs).
      apply gateway_word_stage_region_closed,gateway_word_store_ready_closed.
    + cbn;tauto.
    + intros another world GOOD;apply unchanged_store_edge,edge_skip_seq.
    + eapply gateway_runtime_next with(next:=State f_host_word Sskip
        (Kseq gateway_word_return Kstop)(gateway_word_environment buffer)
        (PTree.set _t'3(Vlong value)(gateway_word_after_read_parameters arguments))memory)
        (middle:=gateway_word_stage mode buffer output held readonly original
          (gateway_word_stored buffer output(Ptrofs.unsigned ofs)value)).
      * eapply gateway_word_stage_ambient with(offset:=Ptrofs.unsigned ofs).
        apply gateway_word_stage_region_closed,gateway_word_store_ready_closed.
      * cbn;tauto.
      * intros another world[RESOURCES[BUFFER OWN]].
        destruct(Mem.valid_access_store another Mint64 output(Ptrofs.unsigned ofs)(Vlong value)OWN)
          as[stored STORE].
        exists stored;split.
        -- eapply assignment_source_edge with(b:=output)(ofs:=ofs)(v:=Vlong value)(w:=Vlong value).
           ++ apply pointer_location_value,old_expression_value,value_temp.
              change(Some(word_output arguments)=Some(Vptr output ofs));rewrite OUTPUT;reflexivity.
           ++ apply old_expression_value,value_temp;apply PTree.gss.
           ++ reflexivity.
           ++ apply assign_loc_value with(chunk:=Mint64);[reflexivity|].
              unfold Mem.storev;rewrite zle_true by exact BOUND;exact STORE.
        -- split.
           ++ eapply gateway_word_resources_store;eassumption.
           ++ split.
              ** intros position RANGE;eapply Mem.perm_store_1;[exact STORE|apply BUFFER;exact RANGE].
              ** exact(Mem.load_store_same _ _ _ _ _ _ STORE).
      * eapply gateway_runtime_same with(next:=State f_host_word gateway_word_return Kstop
          (gateway_word_environment buffer)
          (PTree.set _t'3(Vlong value)(gateway_word_after_read_parameters arguments))memory).
        -- eapply gateway_word_stage_ambient with(offset:=Ptrofs.unsigned ofs).
           apply gateway_word_stage_region_closed,gateway_word_stored_closed.
        -- cbn;tauto.
        -- intros another world GOOD;apply unchanged_store_edge,edge_skip_seq.
        -- eapply gateway_runtime_next with(next:=Returnstate(Vint Int.zero)Kstop memory)
             (middle:=gateway_word_stage mode buffer output held readonly original
               (fun after=>Mem.load Mint64 after output(Ptrofs.unsigned ofs)=Some(Vlong value))).
           ++ eapply gateway_word_stage_ambient with(offset:=Ptrofs.unsigned ofs).
              apply gateway_word_stage_region_closed,gateway_word_stored_closed.
           ++ cbn;tauto.
           ++ intros another world[RESOURCES[BUFFER LOAD]].
              destruct(Mem.range_perm_free another buffer 0 8 BUFFER)as[freed FREE].
              exists freed;split.
              ** eapply certified_local_return_edge with(v:=Vint Int.zero)(w:=Vint Int.zero).
                 --- apply old_expression_value;constructor.
                 --- reflexivity.
                 --- change(Mem.free_list another[(buffer,0,8)]=Some freed).
                     cbn;rewrite FREE;reflexivity.
              ** split;[eapply gateway_word_resources_free;eassumption|].
                 rewrite(Mem.load_free _ _ _ _ _ FREE Mint64 output(Ptrofs.unsigned ofs));
                   [exact LOAD|left;exact SEPARATE].
           ++ apply gateway_runtime_return.
              ** eapply gateway_word_stage_ambient with(offset:=Ptrofs.unsigned ofs).
                 apply gateway_word_stage_region_closed,gateway_word_output_closed.
              ** auto.
Qed.

(* §FS-host-boundary.caller: The final native word cell is stored and its actual
   scratch allocation is freed in the same source/runtime execution. *)
Theorem gateway_actual_word_stores_decoder_runtime mode buffer arguments output ofs value held
    original readonly before world events after next :
  word_output arguments=Vptr output ofs ->output<>buffer ->Ptrofs.unsigned ofs+8<=Ptrofs.modulus ->
  (forall position,Ptrofs.unsigned ofs<=position<Ptrofs.unsigned ofs+8->~readonly output position) ->
  (forall position,~readonly buffer position) ->
  gateway_word_resources mode buffer output held readonly original before world ->
  gateway_word_store_ready buffer output(Ptrofs.unsigned ofs)before ->
  gateway_steps backend ge
    (gateway_live(Returnstate(Vlong value)(gateway_word_get_cont buffer arguments)before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next) ->
  gateway_word_resources mode buffer output held readonly original after next /\
    Mem.loadv Mint64 after(Vptr output ofs)=Some(Vlong value).
Proof.
  intros OUTPUT SEPARATE BOUND OUTSIDE AVOIDS RESOURCES READY RUN.
  destruct(gateway_runtime_path_return_exact backend ge
    (gateway_word_stage mode buffer output held readonly original
      (gateway_word_store_ready buffer output(Ptrofs.unsigned ofs)))
    (Returnstate(Vlong value)(gateway_word_get_cont buffer arguments)before)(Vint Int.zero)
    (gateway_word_stage mode buffer output held readonly original
      (fun after=>Mem.load Mint64 after output(Ptrofs.unsigned ofs)=Some(Vlong value)))
    before world events(Vint Int.zero)after next ltac:(split;assumption)
    (gateway_word_runtime_store_path mode buffer arguments output ofs value held original readonly before
      OUTPUT SEPARATE BOUND OUTSIDE AVOIDS)RUN)as[_[FINAL LOAD]].
  split;[exact FINAL|]. unfold Mem.loadv;rewrite zle_true by exact BOUND;exact LOAD.
Qed.

End WordRuntime.
