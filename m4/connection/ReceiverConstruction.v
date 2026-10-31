(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-receiver.memory: Independent ownership constructs the entire receiver result and free path. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Clight.
Require Import Slice Machine StoreSteps CallPaths SourcePaths ResultLayout ResultSource ResultSafety
  ResultOwnership ReceiverSource ReceiverAllocation ReceiverPreparation
  ReceiverChoice ReceiverSelectionSource ReceiverCopyMemory ReceiverMemory
  ReceiverFree ReceiverTailSource.
Import ListNotations.
Open Scope Z_scope.
Lemma store_path_final_invariant : forall ge P s count final,
  store_path ge P s count final -> P(memory_of final).
Proof. intros ge P s count final PATH;induction PATH;assumption. Qed.
Lemma receiver_choice_member : forall b choice,
  In(receiver_choice_block b choice,144)(receiver_objects b).
Proof. intros;unfold receiver_choice_block,receiver_objects;destruct(rc_branch choice);cbn;tauto. Qed.
Lemma receiver_choice_result_distinct : forall base b m choice,
  receiver_slots_owned base b m -> receiver_choice_block b choice<>rb_result b.
Proof.
  intros base b m choice [DISTINCT OWN];unfold receiver_objects in DISTINCT;cbn in DISTINCT.
  repeat match goal with H : NoDup(_::_) |- _=>inversion H;subst;clear H end.
  unfold receiver_choice_block;destruct(rc_branch choice);cbn in *;intuition congruence.
Qed.
Definition receiver_choice_result output ofs choice uid run b value after :=
  value=Vundef /\ result_contents after output ofs(rc_kind choice)(rc_stage choice)(rc_detail choice)(rc_entry choice)uid run /\
    receiver_freed b after.
Theorem receiver_construction_source : forall cell base b choice le before output ofs uid run,
  receiver_preserved cell base output ofs before -> receiver_slots_owned base b before ->
  result_input before output ofs run uid -> Mem.valid_block base output ->
  le!__res=Some(Vptr output(Ptrofs.repr ofs)) ->
  source_returns result_ge(receiver_preserved cell base output ofs)
    (receiver_choice_result output ofs choice uid run b)
    (receiver_choice_call b choice le Kstop before).
Proof.
  intros cell base b choice le before output ofs uid run PRE SLOTS [DEST GLOBALS] VALID OUT.
  pose proof(receiver_choice_member b choice)as MEMBER.
  destruct(receiver_slot _ _ _ _ _ SLOTS MEMBER)as[FRESH CFREE].
  assert(INPUT : result_input before(receiver_choice_block b choice)0 run uid).
  { split;[eapply receiver_local_destination;[exact SLOTS|exact MEMBER]|exact GLOBALS]. }
  destruct(result_owned_execution before(receiver_choice_block b choice)0
    (rc_kind choice)(rc_stage choice)(rc_detail choice)(rc_entry choice)uid run
    (receiver_choice_cont b choice le Kstop)INPUT)as[built[PATH[CONTENT LOCALFREE]]].
  pose proof(store_path_final_invariant _ _ _ _ _ PATH)as BUILT.
  change(result_owned_preserved before(receiver_choice_block b choice)0 built)in BUILT.
  assert(LIFT : forall after,result_owned_preserved before(receiver_choice_block b choice)0 after ->
    receiver_preserved cell base output ofs after).
  { intros after [KEPT PERMS];eapply receiver_fresh_result_preserved;[exact FRESH|exact PRE|exact KEPT]. }
  pose proof(receiver_slots_permissions _ _ _ _ SLOTS(proj2 BUILT))as SB.
  assert(READ : Mem.range_perm built(receiver_choice_block b choice)0 144 Cur Readable).
  { intros pos RANGE;eapply Mem.perm_implies;[apply(proj2 BUILT);apply CFREE;exact RANGE|constructor]. }
  assert(RDEST : result_destination built(rb_result b)0).
  { eapply receiver_local_destination;[exact SB|unfold receiver_objects;cbn;tauto]. }
  destruct(receiver_result_copy built(receiver_choice_block b choice)(rb_result b)0
    (rc_kind choice)(rc_stage choice)(rc_detail choice)(rc_entry choice)uid run CONTENT READ RDEST
    (receiver_choice_result_distinct _ _ _ _ SLOTS))as[middle[values1[LOAD1[STORE1[ASSIGN1[CONTENT1 KEEP1]]]]]].
  pose proof(receiver_copy_slots _ _ _ _ _ _ _ SB STORE1)as SM.
  assert(PM : receiver_preserved cell base output ofs middle).
  { eapply receiver_copy_preserved;[apply LIFT;exact BUILT|exact KEEP1|].
    intros object pos [VB REST];left;intro EQ;subst object.
    destruct(receiver_slot base b before (rb_result b)144 SLOTS ltac:(unfold receiver_objects;cbn;tauto))as[FR _].
    exact(FR VB). }
  assert(DESTB : result_destination built output ofs).
  { eapply receiver_destination_permissions;[exact DEST|exact(proj2 BUILT)]. }
  assert(DESTM : result_destination middle output ofs).
  { eapply receiver_destination_permissions;[exact DESTB|]. intros object pos pk permission PERM.
    eapply Mem.perm_storebytes_1;[exact STORE1|exact PERM]. }
  assert(READ1 : Mem.range_perm middle(rb_result b)0 144 Cur Readable).
  { destruct(receiver_slot base b middle (rb_result b)144 SM ltac:(unfold receiver_objects;cbn;tauto))as[_ PERMS].
    intros pos RANGE;eapply Mem.perm_implies;[apply PERMS;exact RANGE|constructor]. }
  assert(NE : rb_result b<>output).
  { intro EQ;rewrite <-EQ in VALID.
    destruct(receiver_slot base b before (rb_result b)144 SLOTS ltac:(unfold receiver_objects;cbn;tauto))as[FR _].
    exact(FR VALID). }
  destruct(receiver_result_copy middle(rb_result b)output ofs
    (rc_kind choice)(rc_stage choice)(rc_detail choice)(rc_entry choice)uid run CONTENT1 READ1 DESTM NE)
    as[copied[values2[LOAD2[STORE2[ASSIGN2[CONTENT2 KEEP2]]]]]].
  pose proof(receiver_copy_slots _ _ _ _ _ _ _ SM STORE2)as SC.
  assert(PC : receiver_preserved cell base output ofs copied).
  { eapply receiver_copy_preserved;[exact PM|exact KEEP2|]. intros object pos [VB[OT OX]];exact OX. }
  destruct(receiver_free_exists _ _ _ SC)as[final[FREE KEEPF]].
  assert(PF : receiver_preserved cell base output ofs final).
  { eapply Mem.unchanged_on_trans;[exact PC|].
    eapply Mem.unchanged_on_implies;[exact KEEPF|]. intros object pos [VB REST] VC;exact VB. }
  assert(CONTENTF : result_contents final output ofs(rc_kind choice)(rc_stage choice)(rc_detail choice)(rc_entry choice)uid run).
  { intros field IN;eapply Mem.load_unchanged_on;[exact KEEPF|intros;exact VALID|apply CONTENT2;exact IN]. }
  destruct(receiver_tail_source(receiver_preserved cell base output ofs)b choice le Kstop built middle copied final output ofs
    OUT ASSIGN1 ASSIGN2 FREE(LIFT _ BUILT)PM PC PF)as[count TAIL].
  eapply source_returns_path.
  - eapply store_path_consequence;[exact PATH|exact LIFT].
  - eapply source_returns_path;[exact TAIL|]. apply source_returns_done;[exact PF|].
    split;[reflexivity|]. split;[exact CONTENTF|eapply receiver_free_permissions;exact FREE].
Qed.
