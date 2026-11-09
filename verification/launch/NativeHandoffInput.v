(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Borrowed prepared policy bytes are inputs, not assumed descriptor validation. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata.
Require Import Machine Library ErrorNumber ProcessEffects.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffArguments.
Import ListNotations.
Open Scope Z_scope.
Local Opaque handoff_symbol handoff_ge.

Record HandoffBorrowed := {
  handoff_borrowed_uid : int;
  handoff_borrowed_preflight : int;
  handoff_borrowed_mode : address;
  handoff_borrowed_mode_bytes : list Byte.int;
  handoff_borrowed_source : block;
  handoff_borrowed_source_offset : Ptrofs.int;
  handoff_borrowed_arguments : list handoff_argument_pointer;
  handoff_borrowed_argument_bytes : list (list Byte.int);
  handoff_borrowed_root_bytes : list Byte.int
}.

Definition handoff_pointer_address pointer : address :=
  {|address_block:=fst pointer; address_offset:=Ptrofs.unsigned (snd pointer)|}.
Definition handoff_global_address identifier : address :=
  {|address_block:=handoff_symbol identifier;address_offset:=0|}.

Definition handoff_literal_bytes : list (ident * list Byte.int) :=
  [(EntrySource.___stringlit_1,map Byte.repr [110;111;114;109;97;108]);
   (EntrySource.___stringlit_111,map Byte.repr [47;108;101;97;110;99;97;103;101;45;101;110;116;114;121]);
   (EntrySource.___stringlit_112,map Byte.repr [114;117;110]);
   (EntrySource.___stringlit_113,map Byte.repr [99;104;101;99;107]);
   (EntrySource.___stringlit_114,map Byte.repr [76;67;95;65;76;76;61;67])].

Definition handoff_borrowed_blocks (input : HandoffBorrowed) : list block :=
  [handoff_symbol EntrySource._run_uid;handoff_symbol EntrySource._preflight;
   handoff_symbol EntrySource._mode;handoff_symbol EntrySource._policy__1;
   handoff_symbol EntrySource._root_path;address_block (handoff_borrowed_mode input);
   handoff_borrowed_source input] ++
  map (fun literal=>handoff_symbol (fst literal)) handoff_literal_bytes ++
  map fst (handoff_borrowed_arguments input).

Record handoff_borrowed_input cell (m : mem) (input : HandoffBorrowed) : Prop := {
  handoff_borrowed_errno : entry_errno_ready cell m;
  handoff_borrowed_tls_separate : Forall (fun b=>b<>tls_block cell) (handoff_borrowed_blocks input);
  handoff_borrowed_uid_load : Mem.loadv Mint32 m
    (Vptr (handoff_symbol EntrySource._run_uid) Ptrofs.zero) = Some (Vint (handoff_borrowed_uid input));
  handoff_borrowed_preflight_load : Mem.loadv Mint32 m
    (Vptr (handoff_symbol EntrySource._preflight) Ptrofs.zero) = Some (Vint (handoff_borrowed_preflight input));
  handoff_borrowed_mode_load : Mem.loadv Mptr m
    (Vptr (handoff_symbol EntrySource._mode) Ptrofs.zero) = Some (address_value (handoff_borrowed_mode input));
  handoff_borrowed_mode_text : c_string m (handoff_borrowed_mode input) (handoff_borrowed_mode_bytes input);
  handoff_borrowed_root_text : c_string m (handoff_global_address EntrySource._root_path)
    (handoff_borrowed_root_bytes input);
  handoff_borrowed_policy_load : Mem.loadv Mptr m
    (Vptr (handoff_symbol EntrySource._policy__1) (Ptrofs.repr 88)) =
    Some (Vptr (handoff_borrowed_source input) (handoff_borrowed_source_offset input));
  handoff_borrowed_arguments_bound : (length (handoff_borrowed_arguments input)<=64)%nat;
  handoff_borrowed_argument_slots : handoff_copy_inputs m (handoff_borrowed_source input)
    (handoff_borrowed_source_offset input) 0 (handoff_borrowed_arguments input);
  handoff_borrowed_argument_texts : Forall2
    (fun pointer bytes=>c_string m (handoff_pointer_address pointer) bytes)
    (handoff_borrowed_arguments input) (handoff_borrowed_argument_bytes input);
  handoff_borrowed_literals : Forall
    (fun literal=>c_string m (handoff_global_address (fst literal)) (snd literal)) handoff_literal_bytes
}.

Definition handoff_borrowed_frame (input : HandoffBorrowed) before after :=
  Mem.unchanged_on (fun b _=>In b (handoff_borrowed_blocks input)) before after.

Lemma handoff_borrowed_frame_loadv input before after chunk b offset value :
  handoff_borrowed_frame input before after -> In b (handoff_borrowed_blocks input) ->
  Mem.loadv chunk before (Vptr b offset)=Some value ->
  Mem.loadv chunk after (Vptr b offset)=Some value.
Proof.
  intros FRAME MEMBER LOAD; unfold Mem.loadv in *.
  destruct (zle _ _); [|discriminate].
  eapply Mem.load_unchanged_on; [exact FRAME|intros; exact MEMBER|exact LOAD].
Qed.

Lemma handoff_borrowed_frame_string input before after pointer bytes :
  handoff_borrowed_frame input before after ->
  In (address_block pointer) (handoff_borrowed_blocks input) ->
  c_string before pointer bytes -> c_string after pointer bytes.
Proof.
  intros FRAME MEMBER [NONZERO [BOUNDS LOAD]].
  split; [exact NONZERO|]. split; [exact BOUNDS|].
  eapply Mem.loadbytes_unchanged_on; [exact FRAME|intros; exact MEMBER|exact LOAD].
Qed.

Lemma handoff_borrowed_global_member input identifier :
  In identifier [EntrySource._run_uid;EntrySource._preflight;EntrySource._mode;
    EntrySource._policy__1;EntrySource._root_path] ->
  In (handoff_symbol identifier) (handoff_borrowed_blocks input).
Proof.
  intros MEMBER; unfold handoff_borrowed_blocks; apply in_or_app; left.
  cbn in MEMBER |- *; intuition congruence.
Qed.

Lemma handoff_borrowed_literal_member input literal :
  In literal handoff_literal_bytes ->
  In (handoff_symbol (fst literal)) (handoff_borrowed_blocks input).
Proof.
  intros MEMBER; unfold handoff_borrowed_blocks; apply in_or_app; right.
  apply in_or_app; left; apply in_map_iff; exists literal; auto.
Qed.

Lemma handoff_borrowed_source_member input :
  In (handoff_borrowed_source input) (handoff_borrowed_blocks input).
Proof. unfold handoff_borrowed_blocks; apply in_or_app; left; cbn; auto 8. Qed.
Lemma handoff_borrowed_mode_member input :
  In (address_block (handoff_borrowed_mode input)) (handoff_borrowed_blocks input).
Proof. unfold handoff_borrowed_blocks; apply in_or_app; left; cbn; auto 8. Qed.
Lemma handoff_borrowed_argument_member input pointer : In pointer (handoff_borrowed_arguments input) ->
  In (fst pointer) (handoff_borrowed_blocks input).
Proof.
  intros MEMBER; unfold handoff_borrowed_blocks; apply in_or_app; right.
  apply in_or_app; right; apply in_map; exact MEMBER.
Qed.

Lemma handoff_permissions_weak before after :
  (forall b pos kind permission, Mem.perm before b pos kind permission -> Mem.perm after b pos kind permission) ->
  forall b pos, Mem.weak_valid_pointer before b pos=true -> Mem.weak_valid_pointer after b pos=true.
Proof.
  intros PERMS b pos; unfold Mem.weak_valid_pointer; rewrite !orb_true_iff.
  assert (VALID : forall offset, Mem.valid_pointer before b offset=true -> Mem.valid_pointer after b offset=true).
  { intros offset; rewrite !Mem.valid_pointer_nonempty_perm; apply PERMS. }
  intros [LEFT|RIGHT]; [left;apply VALID;exact LEFT|right;apply VALID;exact RIGHT].
Qed.

Lemma handoff_borrowed_frame_slots input before after index arguments :
  handoff_borrowed_frame input before after ->
  (forall b pos kind permission, Mem.perm before b pos kind permission -> Mem.perm after b pos kind permission) ->
  handoff_copy_inputs before (handoff_borrowed_source input) (handoff_borrowed_source_offset input) index arguments ->
  handoff_copy_inputs after (handoff_borrowed_source input) (handoff_borrowed_source_offset input) index arguments.
Proof.
  intros FRAME PERMS; revert index; induction arguments as [|pointer rest IH]; intros index INPUTS;
    cbn [handoff_copy_inputs] in *.
  - eapply handoff_borrowed_frame_loadv; [exact FRAME|apply handoff_borrowed_source_member|exact INPUTS].
  - destruct INPUTS as [LOAD [WEAK REST]]. split.
    + eapply handoff_borrowed_frame_loadv; [exact FRAME|apply handoff_borrowed_source_member|exact LOAD].
    + split; [eapply handoff_permissions_weak; [exact PERMS|exact WEAK]|apply IH; exact REST].
Qed.

Lemma handoff_borrowed_frame_texts input before after pointers texts :
  handoff_borrowed_frame input before after ->
  Forall (fun pointer=>In (fst pointer) (handoff_borrowed_blocks input)) pointers ->
  Forall2 (fun pointer bytes=>c_string before (handoff_pointer_address pointer) bytes) pointers texts ->
  Forall2 (fun pointer bytes=>c_string after (handoff_pointer_address pointer) bytes) pointers texts.
Proof.
  intros FRAME MEMBERS TEXTS; induction TEXTS; [constructor|].
  inversion MEMBERS; subst; constructor.
  - eapply handoff_borrowed_frame_string; eassumption.
  - apply IHTEXTS; assumption.
Qed.

Theorem handoff_borrowed_input_preserved cell input before after :
  handoff_borrowed_input cell before input -> handoff_borrowed_frame input before after ->
  (forall b pos kind permission, Mem.perm before b pos kind permission -> Mem.perm after b pos kind permission) ->
  entry_errno_ready cell after -> handoff_borrowed_input cell after input.
Proof.
  intros INPUT FRAME PERMS ERRNO; destruct INPUT as
    [OLDERRNO SEPARATE UID PREFLIGHT MODE MODETEXT ROOTTEXT POLICY BOUND SLOTS TEXTS LITERALS].
  constructor; try assumption.
  - eapply handoff_borrowed_frame_loadv; [exact FRAME|apply handoff_borrowed_global_member; cbn; auto 8|exact UID].
  - eapply handoff_borrowed_frame_loadv; [exact FRAME|apply handoff_borrowed_global_member; cbn; auto 8|exact PREFLIGHT].
  - eapply handoff_borrowed_frame_loadv; [exact FRAME|apply handoff_borrowed_global_member; cbn; auto 8|exact MODE].
  - eapply handoff_borrowed_frame_string; [exact FRAME|apply handoff_borrowed_mode_member|exact MODETEXT].
  - eapply handoff_borrowed_frame_string; [exact FRAME|apply handoff_borrowed_global_member; cbn; auto 8|exact ROOTTEXT].
  - eapply handoff_borrowed_frame_loadv; [exact FRAME|apply handoff_borrowed_global_member; cbn; auto 8|exact POLICY].
  - eapply handoff_borrowed_frame_slots; [exact FRAME|exact PERMS|exact SLOTS].
  - eapply handoff_borrowed_frame_texts; [exact FRAME| |exact TEXTS].
    rewrite Forall_forall; intros pointer MEMBER; apply handoff_borrowed_argument_member; exact MEMBER.
  - rewrite Forall_forall in LITERALS |- *; intros literal MEMBER.
    eapply handoff_borrowed_frame_string; [exact FRAME|apply handoff_borrowed_literal_member; exact MEMBER|apply LITERALS; exact MEMBER].
Qed.

Lemma handoff_loadv_valid m chunk b offset value :
  Mem.loadv chunk m (Vptr b offset)=Some value -> Mem.valid_block m b.
Proof.
  unfold Mem.loadv; destruct (zle _ _); [|discriminate].
  intros LOAD; eapply Mem.valid_access_valid_block; eapply Mem.valid_access_implies;
    [eapply Mem.load_valid_access; exact LOAD|constructor].
Qed.

Lemma handoff_string_valid m pointer bytes : c_string m pointer bytes ->
  Mem.valid_block m (address_block pointer).
Proof.
  intros [_ [BOUNDS LOAD]]. eapply Mem.perm_valid_block with (ofs:=address_offset pointer).
  eapply Mem.loadbytes_range_perm; [exact LOAD|].
  rewrite length_app; cbn; pose proof (Nat2Z.is_nonneg (length bytes)); lia.
Qed.

Theorem handoff_borrowed_objects_valid cell m input : handoff_borrowed_input cell m input ->
  Forall (Mem.valid_block m) (handoff_borrowed_blocks input).
Proof.
  intros INPUT; unfold handoff_borrowed_blocks; apply Forall_app; split.
  - repeat constructor.
    + eapply handoff_loadv_valid; exact (handoff_borrowed_uid_load _ _ _ INPUT).
    + eapply handoff_loadv_valid; exact (handoff_borrowed_preflight_load _ _ _ INPUT).
    + eapply handoff_loadv_valid; exact (handoff_borrowed_mode_load _ _ _ INPUT).
    + eapply handoff_loadv_valid; exact (handoff_borrowed_policy_load _ _ _ INPUT).
    + exact (handoff_string_valid _ _ _ (handoff_borrowed_root_text _ _ _ INPUT)).
    + exact (handoff_string_valid _ _ _ (handoff_borrowed_mode_text _ _ _ INPUT)).
    + pose proof (handoff_borrowed_argument_slots _ _ _ INPUT) as SLOTS.
      destruct (handoff_borrowed_arguments input); cbn [handoff_copy_inputs] in SLOTS.
      * eapply handoff_loadv_valid; exact SLOTS.
      * eapply handoff_loadv_valid; exact (proj1 SLOTS).
  - apply Forall_app; split.
    + rewrite Forall_forall; intros b MEMBER; apply in_map_iff in MEMBER.
      destruct MEMBER as [literal [SAME MEMBER]]; subst b.
      pose proof (handoff_borrowed_literals _ _ _ INPUT) as LITERALS.
      rewrite Forall_forall in LITERALS; specialize (LITERALS _ MEMBER).
      exact (handoff_string_valid _ _ _ LITERALS).
    + pose proof (handoff_borrowed_argument_texts _ _ _ INPUT) as TEXTS.
      induction TEXTS; cbn; constructor; auto.
      exact (handoff_string_valid _ _ _ H).
Qed.

Lemma handoff_borrowed_frame_weak input before after b offset :
  handoff_borrowed_frame input before after -> In b (handoff_borrowed_blocks input) ->
  Mem.weak_valid_pointer before b offset=true -> Mem.weak_valid_pointer after b offset=true.
Proof.
  intros FRAME MEMBER; unfold Mem.weak_valid_pointer; rewrite !orb_true_iff.
  assert (VALID:forall pos, Mem.valid_pointer before b pos=true -> Mem.valid_pointer after b pos=true).
  { intros pos; rewrite !Mem.valid_pointer_nonempty_perm.
    intros PERM; eapply Mem.perm_unchanged_on; [exact FRAME|exact MEMBER|exact PERM]. }
  intros [LEFT|RIGHT]; [left;apply VALID;exact LEFT|right;apply VALID;exact RIGHT].
Qed.

Lemma handoff_borrowed_frame_all_slots input before after index arguments :
  handoff_borrowed_frame input before after ->
  (forall pointer, In pointer arguments -> In (fst pointer) (handoff_borrowed_blocks input)) ->
  handoff_copy_inputs before (handoff_borrowed_source input) (handoff_borrowed_source_offset input) index arguments ->
  handoff_copy_inputs after (handoff_borrowed_source input) (handoff_borrowed_source_offset input) index arguments.
Proof.
  intros FRAME; revert index; induction arguments as [|pointer rest IH]; intros index MEMBERS INPUTS;
    cbn [handoff_copy_inputs] in *.
  - eapply handoff_borrowed_frame_loadv; [exact FRAME|apply handoff_borrowed_source_member|exact INPUTS].
  - destruct INPUTS as [LOAD [WEAK REST]]. split.
    + eapply handoff_borrowed_frame_loadv; [exact FRAME|apply handoff_borrowed_source_member|exact LOAD].
    + split.
      * eapply handoff_borrowed_frame_weak; [exact FRAME|apply MEMBERS; cbn; auto|exact WEAK].
      * apply IH; [intros p MEMBER; apply MEMBERS; cbn; auto|exact REST].
Qed.

Theorem handoff_borrowed_input_framed cell input before after :
  handoff_borrowed_input cell before input -> handoff_borrowed_frame input before after ->
  entry_errno_ready cell after -> handoff_borrowed_input cell after input.
Proof.
  intros INPUT FRAME ERRNO; destruct INPUT as
    [OLDERRNO SEPARATE UID PREFLIGHT MODE MODETEXT ROOTTEXT POLICY BOUND SLOTS TEXTS LITERALS].
  constructor; try assumption.
  - eapply handoff_borrowed_frame_loadv; [exact FRAME|apply handoff_borrowed_global_member; cbn; auto 8|exact UID].
  - eapply handoff_borrowed_frame_loadv; [exact FRAME|apply handoff_borrowed_global_member; cbn; auto 8|exact PREFLIGHT].
  - eapply handoff_borrowed_frame_loadv; [exact FRAME|apply handoff_borrowed_global_member; cbn; auto 8|exact MODE].
  - eapply handoff_borrowed_frame_string; [exact FRAME|apply handoff_borrowed_mode_member|exact MODETEXT].
  - eapply handoff_borrowed_frame_string; [exact FRAME|apply handoff_borrowed_global_member; cbn; auto 8|exact ROOTTEXT].
  - eapply handoff_borrowed_frame_loadv; [exact FRAME|apply handoff_borrowed_global_member; cbn; auto 8|exact POLICY].
  - eapply handoff_borrowed_frame_all_slots; [exact FRAME| |exact SLOTS].
    intros pointer MEMBER; apply handoff_borrowed_argument_member; exact MEMBER.
  - eapply handoff_borrowed_frame_texts; [exact FRAME| |exact TEXTS].
    rewrite Forall_forall; intros pointer MEMBER; apply handoff_borrowed_argument_member; exact MEMBER.
  - rewrite Forall_forall in LITERALS |- *; intros literal MEMBER.
    eapply handoff_borrowed_frame_string; [exact FRAME|apply handoff_borrowed_literal_member; exact MEMBER|apply LITERALS; exact MEMBER].
Qed.
