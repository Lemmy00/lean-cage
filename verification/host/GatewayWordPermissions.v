(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A successful word store retains the caller cell's write permission. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayFrames GatewayPure GatewayStreamWord GatewayWordRuntime
  GatewayFramedRuntime GatewayThreadRuntime GatewayStreamInterface.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Definition gateway_word_stored_writable buffer output offset value memory :Prop:=
  gateway_word_stored buffer output offset value memory /\Mem.valid_access memory Mint64 output offset Writable.
Definition gateway_word_output_writable output offset value memory :Prop:=
  Mem.load Mint64 memory output offset=Some(Vlong value) /\Mem.valid_access memory Mint64 output offset Writable.

Lemma gateway_word_output_access_closed buffer output offset :
  gateway_region_closed(gateway_word_store_region buffer output offset)
    (fun memory=>Mem.valid_access memory Mint64 output offset Writable).
Proof.
  intros before after[PERMS ALIGNMENT]FRAME;split;[|exact ALIGNMENT].
  intros position RANGE;eapply Mem.perm_unchanged_on;[exact FRAME| |apply PERMS;exact RANGE].
  right;split;[reflexivity|exact RANGE].
Qed.

Lemma gateway_word_stored_writable_closed buffer output offset value :
  gateway_region_closed(gateway_word_store_region buffer output offset)
    (gateway_word_stored_writable buffer output offset value).
Proof.
  intros before after[STORED ACCESS]FRAME;split.
  - eapply gateway_word_stored_closed;eassumption.
  - eapply gateway_word_output_access_closed;eassumption.
Qed.

Lemma gateway_word_output_writable_closed buffer output offset value :
  gateway_region_closed(gateway_word_store_region buffer output offset)
    (gateway_word_output_writable output offset value).
Proof.
  intros before after[LOAD ACCESS]FRAME;split.
  - eapply gateway_word_output_closed;eassumption.
  - eapply gateway_word_output_access_closed;eassumption.
Qed.

Section WordPermissions.
Context {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
  (io:Event->option gateway_native_io)(native:World->block->Prop)(stable:World->block->Z->Prop)
  (discipline:option val->mem->World->Prop)(thread_errno:World->int).
Context(runtime:gateway_thread_runtime backend io native stable discipline thread_errno).

Lemma gateway_word_runtime_store_writable_path mode buffer arguments output ofs value held original readonly memory :
  word_output arguments=Vptr output ofs ->output<>buffer ->Ptrofs.unsigned ofs+8<=Ptrofs.modulus ->
  (forall position,Ptrofs.unsigned ofs<=position<Ptrofs.unsigned ofs+8->~readonly output position) ->
  (forall position,~readonly buffer position) ->
  gateway_runtime_path backend ge
    (gateway_word_stage native stable discipline mode buffer output held readonly original
      (gateway_word_store_ready buffer output(Ptrofs.unsigned ofs)))
    (Returnstate(Vlong value)(gateway_word_get_cont buffer arguments)memory)(Vint Int.zero)
    (gateway_word_stage native stable discipline mode buffer output held readonly original
      (gateway_word_output_writable output(Ptrofs.unsigned ofs)value)).
Proof.
  intros OUTPUT SEPARATE BOUND OUTSIDE AVOIDS.
  eapply gateway_runtime_same with(next:=State f_host_word Sskip
    (Kseq gateway_word_assignment(Kseq gateway_word_return Kstop))(gateway_word_environment buffer)
    (PTree.set _t'3(Vlong value)(gateway_word_after_read_parameters arguments))memory).
  - eapply gateway_word_stage_ambient with(offset:=Ptrofs.unsigned ofs);[exact runtime|].
    apply gateway_word_stage_region_closed,gateway_word_store_ready_closed.
  - cbn;tauto.
  - intros another world GOOD;apply unchanged_store_edge,edge_returnstate.
  - eapply gateway_runtime_same with(next:=State f_host_word gateway_word_assignment
      (Kseq gateway_word_return Kstop)(gateway_word_environment buffer)
      (PTree.set _t'3(Vlong value)(gateway_word_after_read_parameters arguments))memory).
    + eapply gateway_word_stage_ambient with(offset:=Ptrofs.unsigned ofs);[exact runtime|].
      apply gateway_word_stage_region_closed,gateway_word_store_ready_closed.
    + cbn;tauto.
    + intros another world GOOD;apply unchanged_store_edge,edge_skip_seq.
    + eapply gateway_runtime_next with(next:=State f_host_word Sskip
        (Kseq gateway_word_return Kstop)(gateway_word_environment buffer)
        (PTree.set _t'3(Vlong value)(gateway_word_after_read_parameters arguments))memory)
        (middle:=gateway_word_stage native stable discipline mode buffer output held readonly original
          (gateway_word_stored_writable buffer output(Ptrofs.unsigned ofs)value)).
      * eapply gateway_word_stage_ambient with(offset:=Ptrofs.unsigned ofs);[exact runtime|].
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
           ++ eapply gateway_word_resources_store;[exact runtime|exact RESOURCES|exact OUTSIDE|exact STORE].
           ++ split.
              ** split.
                 --- intros position RANGE;eapply Mem.perm_store_1;[exact STORE|apply BUFFER;exact RANGE].
                 --- exact(Mem.load_store_same _ _ _ _ _ _ STORE).
              ** eapply Mem.store_valid_access_1;eassumption.
      * eapply gateway_runtime_same with(next:=State f_host_word gateway_word_return Kstop
          (gateway_word_environment buffer)
          (PTree.set _t'3(Vlong value)(gateway_word_after_read_parameters arguments))memory).
        -- eapply gateway_word_stage_ambient with(offset:=Ptrofs.unsigned ofs);[exact runtime|].
           apply gateway_word_stage_region_closed,gateway_word_stored_writable_closed.
        -- cbn;tauto.
        -- intros another world GOOD;apply unchanged_store_edge,edge_skip_seq.
        -- eapply gateway_runtime_next with(next:=Returnstate(Vint Int.zero)Kstop memory)
             (middle:=gateway_word_stage native stable discipline mode buffer output held readonly original
               (gateway_word_output_writable output(Ptrofs.unsigned ofs)value)).
           ++ eapply gateway_word_stage_ambient with(offset:=Ptrofs.unsigned ofs);[exact runtime|].
              apply gateway_word_stage_region_closed,gateway_word_stored_writable_closed.
           ++ cbn;tauto.
           ++ intros another world[RESOURCES[[BUFFER LOAD]ACCESS]].
              destruct(Mem.range_perm_free another buffer 0 8 BUFFER)as[freed FREE].
              exists freed;split.
              ** eapply certified_local_return_edge with(v:=Vint Int.zero)(w:=Vint Int.zero).
                 --- apply old_expression_value;constructor.
                 --- reflexivity.
                 --- change(Mem.free_list another[(buffer,0,8)]=Some freed).
                     cbn;rewrite FREE;reflexivity.
              ** split;[eapply gateway_word_resources_free;[exact runtime|exact RESOURCES|exact AVOIDS|exact FREE]|].
                 split.
                 --- rewrite(Mem.load_free _ _ _ _ _ FREE Mint64 output(Ptrofs.unsigned ofs));
                       [exact LOAD|left;exact SEPARATE].
                 --- eapply Mem.valid_access_free_1;[exact FREE|exact ACCESS|left;exact SEPARATE].
           ++ apply gateway_runtime_return.
              ** eapply gateway_word_stage_ambient with(offset:=Ptrofs.unsigned ofs);[exact runtime|].
                 apply gateway_word_stage_region_closed,gateway_word_output_writable_closed.
              ** auto.
Qed.

Theorem gateway_actual_word_store_writable mode buffer arguments output ofs value held original readonly
    before world events after next :
  word_output arguments=Vptr output ofs ->output<>buffer ->Ptrofs.unsigned ofs+8<=Ptrofs.modulus ->
  (forall position,Ptrofs.unsigned ofs<=position<Ptrofs.unsigned ofs+8->~readonly output position) ->
  (forall position,~readonly buffer position) ->
  gateway_word_resources native stable discipline mode buffer output held readonly original before world ->
  gateway_word_store_ready buffer output(Ptrofs.unsigned ofs)before ->
  gateway_steps backend ge(gateway_live(Returnstate(Vlong value)(gateway_word_get_cont buffer arguments)before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next) ->
  gateway_word_resources native stable discipline mode buffer output held readonly original after next /\
    gateway_word_output_writable output(Ptrofs.unsigned ofs)value after.
Proof.
  intros OUTPUT SEPARATE BOUND OUTSIDE AVOIDS RESOURCES READY RUN.
  destruct(gateway_runtime_path_return_exact backend ge
    (gateway_word_stage native stable discipline mode buffer output held readonly original
      (gateway_word_store_ready buffer output(Ptrofs.unsigned ofs)))
    (Returnstate(Vlong value)(gateway_word_get_cont buffer arguments)before)(Vint Int.zero)
    (gateway_word_stage native stable discipline mode buffer output held readonly original
      (gateway_word_output_writable output(Ptrofs.unsigned ofs)value))before world events(Vint Int.zero)after next
    ltac:(split;[exact RESOURCES|exact READY])
    (gateway_word_runtime_store_writable_path mode buffer arguments output ofs value held original readonly before
      OUTPUT SEPARATE BOUND OUTSIDE AVOIDS)RUN)as[_RESULT POST];exact POST.
Qed.

End WordPermissions.
