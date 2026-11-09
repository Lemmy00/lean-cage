(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Returning primitive effects preserve independently owned arguments and descriptor slots. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ErrorNumber ProcessEffects FreshMemory ScalarMemory.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffArguments
  NativeHandoffAllocation NativeHandoffInput NativeHandoffNumeric NativeHandoffInitial NativeHandoffPrefix.
From LeanCageMainNumber Require Import NumberMemory NumberStorage.
Import ListNotations.
Open Scope Z_scope.
Local Opaque handoff_symbol handoff_ge.

Definition handoff_local_owned b m :=
  Forall (fun object=>Mem.range_perm m (fst object) 0 (snd object) Cur Freeable) (handoff_objects b).
Definition handoff_private_layout cell input b :=
  NoDup (map fst (handoff_objects b)) /\
  Forall (fun object=>fst object<>tls_block cell /\
    ~In (fst object) (handoff_borrowed_blocks input)) (handoff_objects b).
Definition handoff_handle_data handles words m := forall index, 0<=index<4 ->
  Mem.loadv Mint32 m (Vptr handles (Ptrofs.repr (4*index)))=Some (Vint (words index)).
Record handoff_live_data cell input b words m : Prop := {
  handoff_live_borrowed : handoff_borrowed_input cell m input;
  handoff_live_owned : handoff_local_owned b m;
  handoff_live_handles : handoff_handle_data (handoff_handles b) words m
}.

Lemma handoff_tls_valid cell m : entry_errno_ready cell m -> Mem.valid_block m (tls_block cell).
Proof.
  intros [error [_ [_ [ACCESS LOAD]]]].
  eapply Mem.perm_valid_block with (ofs:=tls_offset cell); eapply (proj1 ACCESS); cbn; lia.
Qed.

Theorem handoff_layout_allocated cell input before b after :
  handoff_borrowed_input cell before input -> handoff_allocations before b after ->
  handoff_private_layout cell input b /\ handoff_local_owned b after.
Proof.
  intros INPUT ALLOC.
  destruct (handoff_allocation_ownership _ _ _ ALLOC) as [OLD [DISTINCT OBJECTS]].
  assert (TLS:Mem.valid_block before (tls_block cell))
    by (apply handoff_tls_valid; exact (handoff_borrowed_errno _ _ _ INPUT)).
  pose proof (handoff_borrowed_objects_valid _ _ _ INPUT) as SHARED.
  split.
  - split; [exact DISTINCT|]. rewrite Forall_forall in OBJECTS,SHARED |- *.
    intros object MEMBER; destruct (OBJECTS _ MEMBER) as [FRESH OWN]; split.
    + intros SAME; apply FRESH; rewrite SAME; exact TLS.
    + intros SHAREDOBJECT; apply FRESH; apply SHARED; exact SHAREDOBJECT.
  - unfold handoff_local_owned; rewrite Forall_forall in OBJECTS |- *.
    intros object MEMBER; exact (proj2 (OBJECTS _ MEMBER)).
Qed.

Lemma handoff_private_object cell input b object size : handoff_private_layout cell input b ->
  In (object,size) (handoff_objects b) ->
  object<>tls_block cell /\ ~In object (handoff_borrowed_blocks input).
Proof. intros [_ PRIVATE] MEMBER; rewrite Forall_forall in PRIVATE; exact (PRIVATE _ MEMBER). Qed.

Lemma handoff_local_object b m object size : handoff_local_owned b m ->
  In (object,size) (handoff_objects b) -> Mem.range_perm m object 0 size Cur Freeable.
Proof. intros OWN MEMBER; unfold handoff_local_owned in OWN; rewrite Forall_forall in OWN; exact (OWN _ MEMBER). Qed.

Lemma handoff_local_owned_preserved b before after : handoff_local_owned b before ->
  (forall object pos kind permission, Mem.perm before object pos kind permission -> Mem.perm after object pos kind permission) ->
  handoff_local_owned b after.
Proof.
  intros OWN PERMS; unfold handoff_local_owned in OWN |- *; rewrite Forall_forall in OWN |- *; intros object MEMBER pos RANGE.
  apply PERMS; exact (OWN _ MEMBER _ RANGE).
Qed.

Lemma handoff_live_preserved cell input b words before after :
  handoff_live_data cell input b words before ->
  handoff_borrowed_frame input before after ->
  (forall object pos kind permission, Mem.perm before object pos kind permission -> Mem.perm after object pos kind permission) ->
  entry_errno_ready cell after ->
  Mem.unchanged_on (fun object _=>object=handoff_handles b) before after ->
  handoff_live_data cell input b words after.
Proof.
  intros [INPUT OWN HANDLES] SHARED PERMS ERRNO FRAME; constructor.
  - eapply handoff_borrowed_input_preserved; eassumption.
  - eapply handoff_local_owned_preserved; eassumption.
  - intros index BOUND; specialize (HANDLES _ BOUND); unfold Mem.loadv in *.
    destruct (zle _ _); [|discriminate].
    eapply Mem.load_unchanged_on; [exact FRAME|intros; reflexivity|exact HANDLES].
Qed.

Lemma handoff_local_handles_other b output :
  NoDup (map fst (handoff_objects b)) ->
  (output=handoff_uid b \/ output=handoff_numbers b \/ output=handoff_encoded b \/
    output=handoff_arguments b \/ output=handoff_environment b) ->
  handoff_handles b<>output.
Proof.
  intros DISTINCT OUTPUT; cbn [handoff_objects map fst] in DISTINCT.
  inversion DISTINCT; subst; cbn in *; intuition congruence.
Qed.

Theorem handoff_live_formatted cell input b words before after output offset returned :
  handoff_private_layout cell input b -> handoff_live_data cell input b words before ->
  (output=handoff_uid b \/ output=handoff_numbers b) ->
  entry_format_result cell before output offset returned after ->
  handoff_live_data cell input b words after.
Proof.
  intros LAYOUT LIVE OUTPUT RESULT.
  assert (PRIVATE:output<>tls_block cell /\ ~In output (handoff_borrowed_blocks input)).
  { destruct OUTPUT as [UID|NUMBERS]; subst output.
    - eapply handoff_private_object with (size:=32); [exact LAYOUT|unfold handoff_objects; cbn; auto 8].
    - eapply handoff_private_object with (size:=128); [exact LAYOUT|unfold handoff_objects; cbn; auto 8]. }
  destruct PRIVATE as [OUTPUTTLS OUTPUTSHARED].
  pose proof (handoff_borrowed_tls_separate _ _ _ (handoff_live_borrowed _ _ _ _ _ LIVE)) as SEPARATE.
  rewrite Forall_forall in SEPARATE.
  assert (HANDLETLS:handoff_handles b<>tls_block cell).
  { exact (proj1 (handoff_private_object cell input b (handoff_handles b) 16 LAYOUT ltac:(unfold handoff_objects; cbn; auto))). }
  assert (HANDLEOUTPUT:handoff_handles b<>output)
    by (apply handoff_local_handles_other; [exact (proj1 LAYOUT)|tauto]).
  eapply handoff_live_preserved; [exact LIVE| | |exact (entry_format_errno _ _ _ _ _ _ RESULT)|].
  - eapply Mem.unchanged_on_implies; [exact (entry_format_frame _ _ _ _ _ _ RESULT)|].
    intros object pos SHARED VALID; split.
    + left; intros SAME; apply OUTPUTSHARED; rewrite <- SAME; exact SHARED.
    + left; apply SEPARATE; exact SHARED.
  - intros; apply (proj2 (entry_format_permissions _ _ _ _ _ _ RESULT _ _ _ _)); assumption.
  - eapply Mem.unchanged_on_implies; [exact (entry_format_frame _ _ _ _ _ _ RESULT)|].
    intros object pos SAME VALID; subst object; split; left; assumption.
Qed.

Theorem handoff_live_errno_returned cell input b words before after :
  handoff_private_layout cell input b -> handoff_live_data cell input b words before ->
  entry_errno_frame cell before after -> entry_errno_ready cell after ->
  handoff_live_data cell input b words after.
Proof.
  intros LAYOUT [INPUT OWN HANDLES] FRAME ERRNO; constructor.
  - eapply handoff_borrowed_input_framed; [exact INPUT| |exact ERRNO].
    eapply Mem.unchanged_on_implies; [exact FRAME|].
    pose proof (handoff_borrowed_tls_separate _ _ _ INPUT) as SEPARATE.
    rewrite Forall_forall in SEPARATE.
    intros object pos SHARED VALID; left; apply SEPARATE; exact SHARED.
  - unfold handoff_local_owned in OWN |- *; rewrite Forall_forall in OWN |- *.
    intros [object size] MEMBER pos RANGE; cbn in *.
    eapply Mem.perm_unchanged_on; [exact FRAME| |exact (OWN _ MEMBER _ RANGE)].
    left; exact (proj1 (handoff_private_object _ _ _ _ _ LAYOUT MEMBER)).
  - intros index BOUND; specialize (HANDLES _ BOUND); unfold Mem.loadv in *.
    destruct (zle _ _); [|discriminate].
    eapply Mem.load_unchanged_on; [exact FRAME| |exact HANDLES].
    intros pos RANGE; left; exact (proj1 (handoff_private_object cell input b (handoff_handles b) 16 LAYOUT
      ltac:(unfold handoff_objects;cbn;auto))).
Qed.

Lemma handoff_errno_store cell before after chunk output offset value :
  entry_errno_ready cell before -> output<>tls_block cell ->
  Mem.store chunk before output offset value=Some after -> entry_errno_ready cell after.
Proof.
  intros [error [LOW [HIGH [ACCESS LOAD]]]] DIFFERENT STORE; exists error.
  split; [exact LOW|]. split; [exact HIGH|]. split.
  - eapply Mem.store_valid_access_1; eassumption.
  - rewrite (Mem.load_store_other _ _ _ _ _ _ STORE) by (left;congruence); exact LOAD.
Qed.

Theorem handoff_live_number cell input b words before after parsed :
  handoff_private_layout cell input b -> handoff_live_data cell input b words before ->
  number_post before (handoff_encoded b) Ptrofs.zero parsed after ->
  handoff_live_data cell input b words after.
Proof.
  intros LAYOUT LIVE POST; destruct parsed as [value|]; cbn [number_post] in POST; [|subst;exact LIVE].
  change (Mem.store Mint64 before (handoff_encoded b) 0 (Vlong (Int64.repr value))=Some after) in POST.
  destruct (handoff_private_object cell input b (handoff_encoded b) 8 LAYOUT
    ltac:(unfold handoff_objects;cbn;auto 8)) as [ENCODEDTLS ENCODEDSHARED].
  eapply handoff_live_preserved; [exact LIVE| | | |].
  - eapply Mem.store_unchanged_on; [exact POST|]. intros pos RANGE SHARED; contradiction.
  - intros; eapply Mem.perm_store_1; eassumption.
  - eapply handoff_errno_store; [exact (handoff_borrowed_errno _ _ _ (handoff_live_borrowed _ _ _ _ _ LIVE))|exact ENCODEDTLS|exact POST].
  - eapply Mem.store_unchanged_on; [exact POST|].
    intros pos RANGE SAME; apply (handoff_local_handles_other b (handoff_encoded b) (proj1 LAYOUT) ltac:(tauto)); congruence.
Qed.

Lemma handoff_uid_owned b m : handoff_local_owned b m ->
  entry_format_owned m (handoff_uid b) Ptrofs.zero.
Proof.
  intros OWN; split; [change (32<=18446744073709551616);lia|].
  intros pos RANGE; eapply Mem.perm_implies.
  - eapply handoff_local_object; [exact OWN|unfold handoff_objects;cbn;auto 8|exact RANGE].
  - constructor.
Qed.

Lemma handoff_numbers_owned b m index : handoff_local_owned b m -> 0<=index<4 ->
  entry_format_owned m (handoff_numbers b) (Ptrofs.repr (32*index)).
Proof.
  intros OWN INDEX; unfold entry_format_owned.
  rewrite Ptrofs.unsigned_repr by (change Ptrofs.max_unsigned with 18446744073709551615;lia).
  split; [change Ptrofs.modulus with 18446744073709551616;lia|].
  intros pos RANGE; eapply Mem.perm_implies.
  - eapply handoff_local_object with (size:=128); [exact OWN|unfold handoff_objects;cbn;auto 8|lia].
  - constructor.
Qed.

Lemma handoff_encoded_owned b m : handoff_local_owned b m ->
  number_output m (handoff_encoded b) Ptrofs.zero.
Proof.
  intros OWN; split; [change (8<=18446744073709551616);lia|]. split.
  - intros pos RANGE; eapply Mem.perm_implies.
    + eapply handoff_local_object with (size:=8); [exact OWN|unfold handoff_objects;cbn;auto 8|exact RANGE].
    + constructor.
  - change (8|0); apply Z.divide_0_r.
Qed.

Definition handoff_encoding_outside cell b output offset object pos :=
  entry_outside cell output (Ptrofs.unsigned offset) 32 object pos /\
  (object<>handoff_encoded b \/ pos<0 \/ 8<=pos).
Definition handoff_encoding_frame cell b output offset before after :=
  Mem.unchanged_on (handoff_encoding_outside cell b output offset) before after.

Lemma handoff_encoding_frame_refl cell b output offset m :
  handoff_encoding_frame cell b output offset m m.
Proof. apply Mem.unchanged_on_refl. Qed.
Lemma handoff_encoding_frame_trans cell b output offset first middle last :
  handoff_encoding_frame cell b output offset first middle ->
  handoff_encoding_frame cell b output offset middle last ->
  handoff_encoding_frame cell b output offset first last.
Proof. apply Mem.unchanged_on_trans. Qed.
Lemma handoff_encoding_formatted cell b output offset before returned after :
  entry_format_result cell before output offset returned after ->
  handoff_encoding_frame cell b output offset before after.
Proof.
  intros RESULT; eapply Mem.unchanged_on_implies; [exact(entry_format_frame _ _ _ _ _ _ RESULT)|].
  intros object pos [OUTSIDE ENCODED] VALID; exact OUTSIDE.
Qed.
Lemma handoff_encoding_number cell b output offset before parsed after :
  number_post before (handoff_encoded b) Ptrofs.zero parsed after ->
  handoff_encoding_frame cell b output offset before after.
Proof.
  destruct parsed as [value|];cbn [number_post];intros POST;[|subst;apply handoff_encoding_frame_refl].
  change (Mem.store Mint64 before (handoff_encoded b) 0 (Vlong(Int64.repr value))=Some after) in POST.
  eapply Mem.store_unchanged_on;[exact POST|].
  intros pos RANGE [_ [OTHER|[LOW|HIGH]]];cbn in RANGE;congruence || lia.
Qed.
Lemma handoff_encoding_errno cell b output offset before after :
  entry_errno_frame cell before after -> handoff_encoding_frame cell b output offset before after.
Proof.
  intros FRAME; eapply Mem.unchanged_on_implies;[exact FRAME|].
  intros object pos [[OUTPUT TLS] ENCODED] VALID;exact TLS.
Qed.

Lemma handoff_encoding_preserves_input cell b output offset before after input input_offset bytes :
  handoff_encoding_frame cell b output offset before after ->
  number_input before input input_offset bytes ->
  (forall pos, Ptrofs.unsigned input_offset<=pos<Ptrofs.unsigned input_offset+Z.of_nat(length(bytes++[Byte.zero])) ->
    handoff_encoding_outside cell b output offset input pos) ->
  number_input after input input_offset bytes.
Proof.
  intros FRAME [BOUND [NONZERO LOAD]] OUTSIDE;split;[exact BOUND|];split;[exact NONZERO|].
  eapply Mem.loadbytes_unchanged_on;[exact FRAME|exact OUTSIDE|exact LOAD].
Qed.

Lemma handoff_uid_numbers_separate b : NoDup(map fst(handoff_objects b)) ->
  handoff_uid b<>handoff_numbers b /\ handoff_uid b<>handoff_encoded b /\
  handoff_numbers b<>handoff_encoded b.
Proof.
  intros DISTINCT;cbn[handoff_objects map fst] in DISTINCT.
  repeat match goal with N:NoDup(_::_)|-_=>inversion N;clear N;subst end;cbn in *;intuition congruence.
Qed.

Lemma handoff_encoding_preserves_uid cell input b before after index bytes :
  handoff_private_layout cell input b ->
  handoff_encoding_frame cell b (handoff_numbers b) (Ptrofs.repr(32*index)) before after ->
  number_input before (handoff_uid b) Ptrofs.zero bytes ->
  number_input after (handoff_uid b) Ptrofs.zero bytes.
Proof.
  intros LAYOUT FRAME TEXT.
  destruct(handoff_uid_numbers_separate b (proj1 LAYOUT)) as [UIDNUM [UIDENC NUMENC]].
  pose proof(proj1(handoff_private_object cell input b (handoff_uid b) 32 LAYOUT
    ltac:(unfold handoff_objects;cbn;auto 8))) as UIDTLS.
  eapply handoff_encoding_preserves_input;[exact FRAME|exact TEXT|].
  intros pos RANGE;split;[split;left;assumption|left;exact UIDENC].
Qed.

Lemma handoff_encoding_preserves_previous cell input b before after index previous bytes :
  handoff_private_layout cell input b -> 0<=previous<index -> index<4 -> (length bytes<32)%nat ->
  handoff_encoding_frame cell b (handoff_numbers b) (Ptrofs.repr(32*index)) before after ->
  number_input before (handoff_numbers b) (Ptrofs.repr(32*previous)) bytes ->
  number_input after (handoff_numbers b) (Ptrofs.repr(32*previous)) bytes.
Proof.
  intros LAYOUT ORDER HIGH LENGTH FRAME TEXT.
  pose proof(proj2(proj2(handoff_uid_numbers_separate b (proj1 LAYOUT)))) as NUMENC.
  pose proof(proj1(handoff_private_object cell input b (handoff_numbers b) 128 LAYOUT
    ltac:(unfold handoff_objects;cbn;auto 8))) as NUMTLS.
  eapply handoff_encoding_preserves_input;[exact FRAME|exact TEXT|].
  intros pos RANGE;unfold handoff_encoding_outside,entry_outside.
  rewrite !Ptrofs.unsigned_repr in RANGE |- * by
    (change Ptrofs.max_unsigned with 18446744073709551615;lia).
  split;[split|left;exact NUMENC].
  - right;left;rewrite length_app, Nat2Z.inj_add in RANGE;
    change (32*previous<=pos<32*previous+(Z.of_nat(length bytes)+1)) in RANGE;lia.
  - left;exact NUMTLS.
Qed.

Lemma handoff_errno_preserves_input cell before after input offset bytes :
  entry_errno_frame cell before after -> input<>tls_block cell ->
  number_input before input offset bytes -> number_input after input offset bytes.
Proof.
  intros FRAME DIFFERENT [BOUND [NONZERO LOAD]].
  split;[exact BOUND|]. split;[exact NONZERO|].
  eapply Mem.loadbytes_unchanged_on;[exact FRAME|intros;left;exact DIFFERENT|exact LOAD].
Qed.

Lemma handoff_errno_unchanged cell before after :
  Mem.unchanged_on(fun object _=>object=tls_block cell)before after ->
  entry_errno_ready cell before -> entry_errno_ready cell after.
Proof.
  intros FRAME [error[LOW[HIGH[ACCESS LOAD]]]];exists error.
  split;[exact LOW|]. split;[exact HIGH|]. split.
  - destruct ACCESS as[PERM ALIGN];split;[|exact ALIGN].
    intros pos RANGE;eapply Mem.perm_unchanged_on;[exact FRAME|reflexivity|apply PERM;exact RANGE].
  - eapply Mem.load_unchanged_on;[exact FRAME|intros;reflexivity|exact LOAD].
Qed.

Theorem handoff_borrowed_allocated cell input before b after :
  handoff_borrowed_input cell before input -> handoff_allocations before b after ->
  handoff_borrowed_input cell after input.
Proof.
  intros INPUT ALLOC;pose proof(proj1(handoff_allocation_ownership _ _ _ ALLOC))as OLD.
  eapply handoff_borrowed_input_framed;[exact INPUT| |].
  - eapply Mem.unchanged_on_implies;[exact OLD|intros object pos MEMBER VALID;exact VALID].
  - eapply handoff_errno_unchanged;[|exact(handoff_borrowed_errno _ _ _ INPUT)].
    eapply Mem.unchanged_on_implies;[exact OLD|intros object pos SAME VALID;exact VALID].
Qed.

Definition handoff_original_words (input output errors failure:int) index :=
  if index=?0 then input else if index=?1 then output else if index=?2 then errors else failure.

Theorem handoff_live_initialized cell input b before after input_fd output_fd errors_fd failure :
  handoff_private_layout cell input b -> handoff_borrowed_input cell before input ->
  handoff_local_owned b before ->
  handoff_handle_stores b before input_fd output_fd errors_fd failure after ->
  handoff_live_data cell input b (handoff_original_words input_fd output_fd errors_fd failure) after.
Proof.
  intros LAYOUT INPUT OWN STORES.
  destruct(handoff_private_object cell input b(handoff_handles b)16 LAYOUT
    ltac:(unfold handoff_objects;cbn;auto))as[HANDLETLS HANDLESHARED].
  pose proof(handoff_handle_stores_frame _ _ _ _ _ _ _ STORES)as FRAME.
  assert(ERRNO:entry_errno_ready cell after).
  { eapply handoff_errno_unchanged;[|exact(handoff_borrowed_errno _ _ _ INPUT)].
    eapply Mem.unchanged_on_implies;[exact FRAME|].
    intros object pos SAME VALID;subst object;congruence. }
  constructor.
  - eapply handoff_borrowed_input_framed;[exact INPUT| |exact ERRNO].
    eapply Mem.unchanged_on_implies;[exact FRAME|].
    intros object pos MEMBER VALID SAME;subst object;contradiction.
  - eapply handoff_local_owned_preserved;[exact OWN|].
    intros object pos kind permission PERM.
    apply(proj2(handoff_handle_stores_permissions _ _ _ _ _ _ _ STORES _ _ _ _));exact PERM.
  - pose proof(handoff_handle_initialization_values _ _ _ _ _ _ _ STORES)as[INPUTLOAD[OUTPUTLOAD[ERRORLOAD FAILURELOAD]]].
    intros index BOUND;assert(CASES:index=0 \/ index=1 \/ index=2 \/ index=3)by lia.
    destruct CASES as[SAME|[SAME|[SAME|SAME]]];subst index.
    + change(Mem.load Mint32 after(handoff_handles b)0=Some(Vint input_fd));exact INPUTLOAD.
    + change(Mem.load Mint32 after(handoff_handles b)4=Some(Vint output_fd));exact OUTPUTLOAD.
    + change(Mem.load Mint32 after(handoff_handles b)8=Some(Vint errors_fd));exact ERRORLOAD.
    + change(Mem.load Mint32 after(handoff_handles b)12=Some(Vint failure));exact FAILURELOAD.
Qed.

Definition handoff_tables_frame b before after :=
  Mem.unchanged_on(fun object _=>object<>handoff_arguments b /\ object<>handoff_environment b)before after.
Lemma handoff_scalar_frame output before cells after : scalar_stores output before cells after ->
  Mem.unchanged_on(fun object _=>object<>output)before after.
Proof.
  intros STORES;induction STORES;[apply Mem.unchanged_on_refl|].
  eapply Mem.unchanged_on_trans;[|exact IHSTORES].
  eapply Mem.store_unchanged_on;[exact H|]. intros pos RANGE DIFFERENT;apply DIFFERENT;reflexivity.
Qed.
Lemma handoff_tables_frame_refl b m : handoff_tables_frame b m m.
Proof. apply Mem.unchanged_on_refl. Qed.
Lemma handoff_tables_frame_trans b first middle last :
  handoff_tables_frame b first middle -> handoff_tables_frame b middle last -> handoff_tables_frame b first last.
Proof. apply Mem.unchanged_on_trans. Qed.
Lemma handoff_tables_scalar b output before cells after :
  (output=handoff_arguments b \/ output=handoff_environment b) -> scalar_stores output before cells after ->
  handoff_tables_frame b before after.
Proof.
  intros OUTPUT STORES;eapply Mem.unchanged_on_implies;[eapply handoff_scalar_frame;exact STORES|].
  intros object pos [ARGS ENV] VALID;destruct OUTPUT;congruence.
Qed.

Theorem handoff_live_table_stores cell input b words output before cells after :
  handoff_private_layout cell input b -> handoff_live_data cell input b words before ->
  (output=handoff_arguments b \/ output=handoff_environment b) -> scalar_stores output before cells after ->
  handoff_live_data cell input b words after.
Proof.
  intros LAYOUT LIVE OUTPUT STORES.
  assert(PRIVATE:output<>tls_block cell /\ ~In output(handoff_borrowed_blocks input)).
  { destruct OUTPUT as[ARGS|ENV];subst output.
    - eapply handoff_private_object with(size:=592);[exact LAYOUT|unfold handoff_objects;cbn;auto 8].
    - eapply handoff_private_object with(size:=16);[exact LAYOUT|unfold handoff_objects;cbn;auto 8]. }
  destruct PRIVATE as[OUTPUTTLS OUTPUTSHARED].
  pose proof(handoff_scalar_frame _ _ _ _ STORES)as FRAME.
  eapply handoff_live_preserved;[exact LIVE| | | |].
  - eapply Mem.unchanged_on_implies;[exact FRAME|].
    intros object pos MEMBER VALID SAME;subst object;contradiction.
  - intros object pos kind permission PERM;apply(proj2(scalar_stores_permissions _ _ _ _ STORES _ _ _ _));exact PERM.
  - eapply handoff_errno_unchanged;[|exact(handoff_borrowed_errno _ _ _ (handoff_live_borrowed _ _ _ _ _ LIVE))].
    eapply Mem.unchanged_on_implies;[exact FRAME|].
    intros object pos SAME VALID;subst object;congruence.
  - eapply Mem.unchanged_on_implies;[exact FRAME|].
    intros object pos SAME VALID;subst object.
    apply handoff_local_handles_other;[exact(proj1 LAYOUT)|tauto].
Qed.

Lemma handoff_tables_preserves_input b before after input offset bytes :
  handoff_tables_frame b before after -> input<>handoff_arguments b -> input<>handoff_environment b ->
  number_input before input offset bytes -> number_input after input offset bytes.
Proof.
  intros FRAME ARGS ENV[BOUND[NONZERO LOAD]]. split;[exact BOUND|]. split;[exact NONZERO|].
  eapply Mem.loadbytes_unchanged_on;[exact FRAME|intros;split;assumption|exact LOAD].
Qed.

Lemma handoff_tables_numbers_separate b : NoDup(map fst(handoff_objects b)) ->
  handoff_uid b<>handoff_arguments b /\ handoff_uid b<>handoff_environment b /\
  handoff_numbers b<>handoff_arguments b /\ handoff_numbers b<>handoff_environment b.
Proof.
  intros DISTINCT;cbn[handoff_objects map fst]in DISTINCT.
  repeat match goal with N:NoDup(_::_)|-_=>inversion N;clear N;subst end;cbn in *;intuition congruence.
Qed.
