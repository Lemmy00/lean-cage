(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: The maintained loop establishes both safe child-ABI descriptor bounds. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewaySpawnABI GatewaySpawnResources GatewaySpawnRuntime
  GatewayPairContext GatewayPairMemory GatewayPairStatements GatewayPairDuplicate GatewayPairLoopControl
  GatewayThreadRuntime GatewayFramedRuntime GatewaySetupPaths GatewayOperations GatewayFrames GatewayStreamInterface GatewayPairBuffers.
Import ListNotations.
Open Scope Z_scope.

Definition pair_progress index left right:Prop:=(1<=index->4<=left) /\(2<=index->4<=right).
Lemma pair_progress_replacement index left right moved:
  0<=index<2->pair_progress index left right->4<=moved->
  pair_progress(index+1)(pair_slot_left index moved left)(pair_slot_right index moved right).
Proof.
  intros RANGE[LEFT RIGHT]MOVED;assert(index=0\/index=1)by lia;destruct H;subst index.
  - change((1<=1->4<=moved)/\(2<=1->4<=right));split;intros;lia.
  - change((1<=2->4<=left)/\(2<=2->4<=moved));split;intros;[apply LEFT;lia|exact MOVED].
Qed.
Lemma pair_progress_unchanged index left right:
  0<=index<2->pair_progress index left right->4<=pair_slot_value index left right->pair_progress(index+1)left right.
Proof.
  intros RANGE[LEFT RIGHT]SELECTED;assert(index=0\/index=1)by lia;destruct H;subst index.
  - change(4<=left)in SELECTED;change((1<=1->4<=left)/\(2<=1->4<=right));split;intros;lia.
  - change(4<=right)in SELECTED;change((1<=2->4<=left)/\(2<=2->4<=right));split;intros;[apply LEFT;lia|exact SELECTED].
Qed.

Section PairLoop.
Context {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
  (native_private:World->block->Prop)(stable_readonly:World->block->Z->Prop)
  (discipline:option val->mem->World->Prop)(thread_errno:World->int)
  (resources:World->gateway_resource_state)(ipc:nat->Prop).
Context(runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno)
  (descriptors:gateway_spawn_descriptor_runtime backend io native_private stable_readonly discipline resources ipc).
Variable ge:Clight.genv.
Variable identity:gateway_pair_identity ipc.
Variable object:block.
Variable offset:ptrofs.
Variable history:mem->World->Prop.
Context(buffers:gateway_pair_buffer_laws backend native_private stable_readonly discipline object offset history).
Variables duplicate_symbol close_symbol:block.
Hypotheses(DUPLICATE_SYMBOL:Genv.find_symbol ge _leancage_host_fcntl=Some duplicate_symbol)
  (DUPLICATE_FUNCTION:Genv.find_funct_ptr ge duplicate_symbol=Some(gateway_spawn_signature gateway_fcntl_api))
  (CLOSE_SYMBOL:Genv.find_symbol ge _close=Some close_symbol)
  (CLOSE_FUNCTION:Genv.find_funct_ptr ge close_symbol=Some(gateway_spawn_signature gateway_close_api)).
Local Definition pair_context left right:=gateway_pair_full_context native_private discipline resources ipc identity object offset left right history.
Definition gateway_pair_normalized(memory:mem)(world:World):Prop:=
  exists left right,4<=left /\4<=right /\pair_context left right memory world.
Local Lemma pair_context_closed left right:gateway_ambient_closed backend(pair_context left right).
Proof. apply gateway_pair_full_context_ambient with(io:=io)(stable_readonly:=stable_readonly)(thread_errno:=thread_errno);assumption. Qed.
Variable result:mem->World->Prop.
Hypothesis FINAL:forall left right memory world,4<=left->4<=right->pair_context left right memory world->result memory world.
Local Ltac pair_same target:=eapply gateway_setup_same with(next:=target);
  [apply pair_context_closed|cbn;tauto|intros available current GOOD|].

Theorem actual_pair_loop_script remaining:
  forall index left right temporaries memory,
  0<=index<=2->index+Z.of_nat remaining=2->pair_progress index left right->
  temporaries!_pair=Some(Vptr object offset)->temporaries!_index=Some(Vint(Int.repr index))->
  gateway_setup_path backend ge result(pair_context left right)
    (State f_host_private_pair pair_loop(Kseq pair_return Kstop)empty_env temporaries memory).
Proof.
  induction remaining as[|remaining IH];intros index left right temporaries memory RANGE COUNT PROGRESS POINTER INDEX.
  - cbn in COUNT;assert(index=2)by lia;subst index.
    apply actual_pair_loop_end;[apply pair_context_closed|exact INDEX|].
    intros available current GOOD;destruct PROGRESS as[LEFT RIGHT];eapply FINAL;[apply LEFT;lia|apply RIGHT;lia|exact GOOD].
  - assert(ITERATION:0<=index<2)by(rewrite Nat2Z.inj_succ in COUNT;lia).
    assert(ADVANCE:forall current_left current_right changed available,
      pair_progress(index+1)current_left current_right->changed!_pair=Some(Vptr object offset)->
      changed!_index=Some(Vint(Int.repr index))->
      gateway_setup_path backend ge result(pair_context current_left current_right)
        (State f_host_private_pair Sskip pair_loop_cont empty_env changed available)).
    { intros current_left current_right changed available NEXT_PROGRESS NEXT_POINTER NEXT_INDEX.
      eapply actual_pair_loop_advance;[apply pair_context_closed|exact NEXT_INDEX|exact ITERATION|].
      apply IH with(index:=index+1).
      - lia.
      - rewrite Nat2Z.inj_succ in COUNT;lia.
      - exact NEXT_PROGRESS.
      - rewrite PTree.gso by discriminate;exact NEXT_POINTER.
      - rewrite PTree.gss;reflexivity. }
    pair_same(State f_host_private_pair pair_iteration pair_loop_cont empty_env temporaries memory).
    { apply unchanged_store_edge,edge_loop. }
    pair_same(State f_host_private_pair pair_limit(Kseq pair_work pair_loop_cont)empty_env temporaries memory).
    { apply unchanged_store_edge,edge_seq. }
    pair_same(State f_host_private_pair Sskip(Kseq pair_work pair_loop_cont)empty_env temporaries memory).
    { apply certified_if_edge with(v:=Vint Int.one)(b:=true).
      - pose proof(actual_pair_limit ge temporaries available index INDEX RANGE)as VALUE.
        destruct(zlt index 2);[exact VALUE|lia].
      - reflexivity. }
    pair_same(State f_host_private_pair pair_work pair_loop_cont empty_env temporaries memory).
    { apply unchanged_store_edge,edge_skip_seq. }
    pair_same(State f_host_private_pair pair_load(Kseq pair_low_guard pair_loop_cont)empty_env temporaries memory).
    { apply unchanged_store_edge,edge_seq. }
    set(selected:=pair_slot_value index left right).
    set(loaded_temps:=PTree.set _t'5(Vint(Int.repr selected))temporaries).
    pair_same(State f_host_private_pair Sskip(Kseq pair_low_guard pair_loop_cont)empty_env loaded_temps memory).
    { destruct GOOD as[[SIDE[PRIVATE[CELLS RESOURCES]]]HISTORY].
      apply certified_set_edge;eapply actual_pair_element_read;[exact POINTER|exact INDEX|exact ITERATION| |].
      - exact(proj1(proj2(proj1(proj1 CELLS)))).
      - eapply gateway_pair_selected_load;eassumption. }
    pair_same(State f_host_private_pair pair_low_guard pair_loop_cont empty_env loaded_temps memory).
    { apply unchanged_store_edge,edge_skip_seq. }
    destruct(zlt selected 4)as[LOW|HIGH].
    + pair_same(State f_host_private_pair pair_low_body pair_loop_cont empty_env loaded_temps memory).
      { apply certified_if_edge with(v:=Vint Int.one)(b:=true).
        - pose proof(proj1(gateway_pair_slot_resources ipc identity left right index(resources current)
            (proj2(proj2(proj2(proj1 GOOD))))ITERATION))as WIDTH.
          pose proof(actual_pair_low ge loaded_temps available selected ltac:(apply PTree.gss)WIDTH)as VALUE.
          destruct(zlt selected 4);[exact VALUE|lia].
        - reflexivity. }
      eapply actual_pair_duplicate_script with(duplicate_symbol:=duplicate_symbol)(close_symbol:=close_symbol);
        try eassumption.
      * unfold loaded_temps;rewrite PTree.gso by discriminate;exact POINTER.
      * unfold loaded_temps;rewrite PTree.gso by discriminate;exact INDEX.
      * intros moved changed available MINIMUM NEXT_POINTER NEXT_INDEX.
        apply ADVANCE;[apply pair_progress_replacement;assumption|exact NEXT_POINTER|exact NEXT_INDEX].
    + pair_same(State f_host_private_pair Sskip pair_loop_cont empty_env loaded_temps memory).
      { apply certified_if_edge with(v:=Vint Int.zero)(b:=false).
        - pose proof(proj1(gateway_pair_slot_resources ipc identity left right index(resources current)
            (proj2(proj2(proj2(proj1 GOOD))))ITERATION))as WIDTH.
          pose proof(actual_pair_low ge loaded_temps available selected ltac:(apply PTree.gss)WIDTH)as VALUE.
          destruct(zlt selected 4);[lia|exact VALUE].
        - reflexivity. }
      apply ADVANCE.
      * apply pair_progress_unchanged;try assumption;unfold selected in HIGH;lia.
      * unfold loaded_temps;rewrite PTree.gso by discriminate;exact POINTER.
      * unfold loaded_temps;rewrite PTree.gso by discriminate;exact INDEX.
Qed.
End PairLoop.
