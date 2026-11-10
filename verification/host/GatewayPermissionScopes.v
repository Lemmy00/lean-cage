(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual source stack allocation/free preserves pre-existing caller
   permission cells; ordinary source stores may change bytes without changing Cur/Max authority. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Cop Clight.
Require Import Machine.
From HostGateway Require Import GatewayMachine GatewayScopedMemory.
Import ListNotations.

Record gateway_permission_frame(protected:block->Z->Prop)(before after:mem):Prop:={
  gateway_permission_live:forall object,Mem.valid_block before object->Mem.valid_block after object;
  gateway_permission_cells:forall object position kind permission,protected object position->Mem.valid_block before object->
    (Mem.perm before object position kind permission<->Mem.perm after object position kind permission)
}.

Lemma gateway_permission_refl protected memory:gateway_permission_frame protected memory memory.
Proof. split;intros;tauto. Qed.
Lemma gateway_permission_trans protected before middle after:
  gateway_permission_frame protected before middle->gateway_permission_frame protected middle after->
  gateway_permission_frame protected before after.
Proof.
  intros[BEFORE FIRST][AFTER SECOND];split.
  - intros object LIVE;apply AFTER,BEFORE;exact LIVE.
  - intros object position kind permission MEMBER LIVE;
      exact(iff_trans(FIRST object position kind permission MEMBER LIVE)
        (SECOND object position kind permission MEMBER(BEFORE object LIVE))).
Qed.
Lemma gateway_permission_unchanged protected before after:
  Mem.unchanged_on protected before after->gateway_permission_frame protected before after.
Proof.
  intro FRAME;split;[intros;eapply Mem.valid_block_unchanged_on;eassumption|].
  intros object position kind permission MEMBER LIVE;exact(Mem.unchanged_on_perm _ _ _ FRAME object position kind permission MEMBER LIVE).
Qed.
Lemma gateway_permission_store protected before after chunk object offset value:
  Mem.store chunk before object offset value=Some after->gateway_permission_frame protected before after.
Proof.
  intro STORE;split.
  - intros candidate LIVE;unfold Mem.valid_block in *;rewrite(Mem.nextblock_store _ _ _ _ _ _ STORE);exact LIVE.
  - intros;split;[eapply Mem.perm_store_1|eapply Mem.perm_store_2];eassumption.
Qed.
Lemma gateway_permission_storebytes protected before after object offset bytes:
  Mem.storebytes before object offset bytes=Some after->gateway_permission_frame protected before after.
Proof.
  intro STORE;split.
  - intros candidate LIVE;unfold Mem.valid_block in *;rewrite(Mem.nextblock_storebytes _ _ _ _ _ STORE);exact LIVE.
  - intros;split;[eapply Mem.perm_storebytes_1|eapply Mem.perm_storebytes_2];eassumption.
Qed.

Fixpoint gateway_permission_cont(protected:block->Z->Prop)(continuation:cont):Prop:=
  match continuation with
  |Kstop=>True
  |Kseq _ rest|Kloop1 _ _ rest|Kloop2 _ _ rest|Kswitch rest=>gateway_permission_cont protected rest
  |Kcall _ _ environment _ rest=>gateway_environment_avoids protected environment /\gateway_permission_cont protected rest
  end.
Definition gateway_permission_source(protected:block->Z->Prop)(source:Clight.state):Prop:=
  match source with
  |State _ _ continuation environment _ _=>gateway_environment_avoids protected environment /\gateway_permission_cont protected continuation
  |Callstate _ _ continuation _|Returnstate _ continuation _=>gateway_permission_cont protected continuation
  end.

Lemma gateway_permission_call_cont protected continuation:
  gateway_permission_cont protected continuation->gateway_permission_cont protected(call_cont continuation).
Proof. induction continuation;cbn;intuition. Qed.
Lemma gateway_permission_source_replace protected source memory:
  gateway_permission_source protected source->gateway_permission_source protected(gateway_replace_memory source memory).
Proof. destruct source;cbn;auto. Qed.

Lemma gateway_permission_find_label protected label body continuation found rest:
  find_label label body continuation=Some(found,rest)->
  gateway_permission_cont protected continuation->gateway_permission_cont protected rest
with gateway_permission_find_label_branches protected label branches continuation found rest:
  find_label_ls label branches continuation=Some(found,rest)->
  gateway_permission_cont protected continuation->gateway_permission_cont protected rest.
Proof.
  - destruct body;cbn;intros FOUND SAFE;try discriminate.
    + destruct(find_label label body1(Kseq body2 continuation))as[[statement next]|]eqn:FIRST;
        [inversion FOUND;subst;eapply gateway_permission_find_label;[exact FIRST|exact SAFE]|
         eapply gateway_permission_find_label;[exact FOUND|exact SAFE]].
    + destruct(find_label label body1 continuation)as[[statement next]|]eqn:FIRST;
        [inversion FOUND;subst;eapply gateway_permission_find_label;[exact FIRST|exact SAFE]|
         eapply gateway_permission_find_label;[exact FOUND|exact SAFE]].
    + destruct(find_label label body1(Kloop1 body1 body2 continuation))as[[statement next]|]eqn:FIRST;
        [inversion FOUND;subst;eapply gateway_permission_find_label;[exact FIRST|exact SAFE]|
         eapply gateway_permission_find_label;[exact FOUND|exact SAFE]].
    + eapply gateway_permission_find_label_branches;[exact FOUND|exact SAFE].
    + destruct(ident_eq label l);[inversion FOUND;subst;exact SAFE|
        eapply gateway_permission_find_label;[exact FOUND|exact SAFE]].
  - destruct branches;cbn;intros FOUND SAFE;try discriminate.
    destruct(find_label label s(Kseq(seq_of_labeled_statement branches)continuation))as[[statement next]|]eqn:FIRST;
      [inversion FOUND;subst;eapply gateway_permission_find_label;[exact FIRST|exact SAFE]|
       eapply gateway_permission_find_label_branches;[exact FOUND|exact SAFE]].
Qed.

Lemma gateway_assignment_permission protected ce ty before object offset bitfield value after:
  assign_loc ce ty before object offset bitfield value after->gateway_permission_frame protected before after.
Proof.
  intro ASSIGN;inversion ASSIGN;subst.
  - match goal with STORE:Mem.storev _ _ _ _=Some _|-_=>
      unfold Mem.storev in STORE;destruct(zle _ _);[eapply gateway_permission_store;exact STORE|discriminate]end.
  - eapply gateway_permission_storebytes;eassumption.
  - match goal with STORE:store_bitfield _ _ _ _ _ _ _ _ _ _|-_=>inversion STORE;subst end.
    match goal with STORE:Mem.storev _ _ _ _=Some _|-_=>
      unfold Mem.storev in STORE;destruct(zle _ _);[eapply gateway_permission_store;exact STORE|discriminate]end.
Qed.

Theorem gateway_internal_permission_scope ge protected source trace after:
  gateway_permission_source protected source->gateway_region_live protected(memory_of source)->
  internal_state source->step2 ge source trace after->
  gateway_permission_source protected after /\gateway_permission_frame protected(memory_of source)(memory_of after).
Proof.
  destruct source as[function body continuation environment temporaries memory|definition arguments continuation memory|value continuation memory];
    cbn[gateway_permission_source memory_of internal_state];intros SAFE LIVE INTERNAL STEP.
  - destruct SAFE as[AVOIDS CONT].
    inversion STEP;subst;cbn[gateway_permission_source gateway_permission_cont memory_of]in *.
    all:try contradiction.
    all:try solve[split;[intuition|apply gateway_permission_refl]].
    + split;[split;assumption|eapply gateway_assignment_permission;eassumption].
    + split;[apply gateway_permission_call_cont;exact CONT|].
      apply gateway_permission_unchanged;eapply gateway_environment_avoids_free;eassumption.
    + split;[apply gateway_permission_call_cont;exact CONT|].
      apply gateway_permission_unchanged;eapply gateway_environment_avoids_free;eassumption.
    + split;[exact CONT|]. apply gateway_permission_unchanged;eapply gateway_environment_avoids_free;eassumption.
    + split;[split;[exact AVOIDS|]|apply gateway_permission_refl].
      eapply gateway_permission_find_label;[eassumption|apply gateway_permission_call_cont;exact CONT].
  - destruct definition;[|contradiction].
    inversion STEP;subst.
    match goal with ENTRY:function_entry2 _ _ _ _ _ _ _|-_=>inversion ENTRY;subst end.
    match goal with ALLOC:alloc_variables ge empty_env memory _ _ _|-_=>
      destruct(gateway_scope_allocation ge protected _ _ _ _ _ ALLOC LIVE(gateway_environment_empty_avoids protected))as[AVOIDS FRAME]end.
    split;[cbn[gateway_permission_source];split;assumption|apply gateway_permission_unchanged;exact FRAME].
  - inversion STEP;subst;cbn[gateway_permission_cont]in SAFE.
    split;[exact SAFE|apply gateway_permission_refl].
Qed.
