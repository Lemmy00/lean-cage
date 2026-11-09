(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.acceptance: Actual loader globals supply readable useful report selectors. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Ctypes Clight.
Require Import Machine Library ScalarMemory FrameRecord FrameAllocation DecoderValidity ErrorNumber WriteBytes.
From EntryNamespace Require Import NamespaceParentFrame.
Import ListNotations.
Open Scope Z_scope.

From compcert Require Import Globalenvs.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffArguments NativeHandoffInput NativeHandoffInitial
  NativeHandoffInputWitness.
From EntryReporting Require Import ResultLayout ResultSource SenderSelectors.
Require Import FrameBytes.

Definition namespace_constant_names:=
  [_run_id;_run_uid;_mode;___stringlit_1;___stringlit_2;___stringlit_3;___stringlit_4;
    ___stringlit_5;___stringlit_6;___stringlit_7].
Definition namespace_constant_object object:=In object(map handoff_symbol namespace_constant_names).
Definition namespace_constant_frame before after:=
  Mem.unchanged_on(fun object _=>namespace_constant_object object)before after.

Record namespace_parent_constants memory run uid:Prop:={
  namespace_constant_result:result_globals memory(handoff_symbol _run_id)(handoff_symbol _run_uid)run uid;
  namespace_constant_mode:Mem.load Mint64 memory(handoff_symbol _mode)0=
    Some(address_value(handoff_global_address ___stringlit_1));
  namespace_constant_mode_text:c_string memory(handoff_global_address ___stringlit_1)handoff_normal_bytes;
  namespace_constant_reports:forall tag,
    c_string memory(handoff_global_address(report_literal tag))(report_name tag);
  namespace_constant_magic:readable_bytes memory(handoff_global_address ___stringlit_2)frame_magic
}.

Lemma namespace_constant_member id:In id namespace_constant_names ->namespace_constant_object(handoff_symbol id).
Proof. intro MEMBER;apply in_map;exact MEMBER. Qed.

Theorem namespace_constants_preserved before after run uid:
  namespace_parent_constants before run uid ->namespace_constant_frame before after ->
  namespace_parent_constants after run uid.
Proof.
  intros[RESULT MODE MODETEXT REPORTS MAGIC]FRAME;constructor.
  - destruct RESULT as[RUN UID];split;eapply Mem.load_unchanged_on;
      [exact FRAME|intros;apply namespace_constant_member;cbn;auto 12|exact RUN|
       exact FRAME|intros;apply namespace_constant_member;cbn;auto 12|exact UID].
  - eapply Mem.load_unchanged_on;[exact FRAME|intros;apply namespace_constant_member;cbn;auto 12|exact MODE].
  - eapply handoff_fixture_string_frame;[exact FRAME| |exact MODETEXT].
    intros;apply namespace_constant_member;cbn;auto 12.
  - intro tag;eapply handoff_fixture_string_frame;[exact FRAME| |apply REPORTS].
    intros;apply namespace_constant_member;destruct tag;cbn;auto 12.
  - destruct MAGIC as[BOUNDS LOAD];split;[exact BOUNDS|].
    eapply Mem.loadbytes_unchanged_on;[exact FRAME| |exact LOAD].
    intros;apply namespace_constant_member;cbn;auto 12.
Qed.

Theorem namespace_constants_selectors cell memory run uid:
  namespace_parent_constants memory run uid ->entry_errno_ready cell memory ->
  (forall object,namespace_constant_object object ->object<>tls_block cell) ->
  sender_selectors cell memory(handoff_global_address ___stringlit_1)handoff_normal_bytes
    (fun tag=>handoff_symbol(report_literal tag)).
Proof.
  intros[RESULT MODE MODETEXT REPORTS MAGIC]READY SEPARATE.
  assert(OUTSIDE:forall id,In id namespace_constant_names ->forall position,
    outside_bytes(tls_block cell)(tls_offset cell)4(handoff_symbol id)position).
  { intros id MEMBER position;left;apply SEPARATE,namespace_constant_member;exact MEMBER. }
  split;[apply entry_errno_ready_tls;exact READY|]. split.
  - exists(handoff_symbol _mode);split;[unfold result_ge,handoff_ge,handoff_symbol;vm_compute;reflexivity|].
    split;[exact MODE|intros position RANGE;apply OUTSIDE;cbn;auto 12].
  - split.
    + split;[exact MODETEXT|intros position RANGE;apply OUTSIDE;cbn;auto 12].
    + intro tag;split.
      * destruct tag;unfold result_ge,handoff_ge,handoff_symbol;vm_compute;reflexivity.
      * split;[apply REPORTS|]. intros position RANGE;apply OUTSIDE;destruct tag;cbn;auto 12.
Qed.

Definition namespace_report_location tag:=handoff_symbol(report_literal tag).

Theorem namespace_initial_report_literals initial:
  Genv.init_mem EntrySource.prog=Some initial ->
  forall tag,c_string initial(handoff_global_address(report_literal tag))(report_name tag).
Proof.
  intro INITIAL;intro tag;destruct tag;cbn[report_literal report_name];
    first[handoff_initial_literal EntrySource.v___stringlit_3|
      handoff_initial_literal EntrySource.v___stringlit_4|
      handoff_initial_literal EntrySource.v___stringlit_5|
      handoff_initial_literal EntrySource.v___stringlit_6|
      handoff_initial_literal EntrySource.v___stringlit_7].
Qed.

Theorem namespace_initial_report_magic initial:
  Genv.init_mem EntrySource.prog=Some initial ->
  readable_bytes initial(handoff_global_address ___stringlit_2)frame_magic.
Proof.
  intro INITIAL.
  assert(STRING:c_string initial(handoff_global_address ___stringlit_2)frame_magic).
  { handoff_initial_literal EntrySource.v___stringlit_2. }
  destruct STRING as[NONZERO READ].
  pose proof(readable_subspan _ _ _ 0 4 READ ltac:(cbn;lia)ltac:(cbn;lia))as PREFIX.
  cbn[offset_address address_block address_offset]in PREFIX.
  change(readable_bytes initial
    {|address_block:=handoff_symbol ___stringlit_2;address_offset:=0|}frame_magic)in PREFIX;exact PREFIX.
Qed.

Theorem namespace_initial_cgroup_access initial:
  Genv.init_mem EntrySource.prog=Some initial ->
  Mem.valid_access initial Mint32(handoff_symbol _admission_cgroup)0 Writable.
Proof.
  intro INITIAL.
  assert(INFO:Genv.find_var_info(Clight.genv_genv handoff_ge)(handoff_symbol _admission_cgroup)=Some v_admission_cgroup)
    by(unfold handoff_ge,handoff_symbol;vm_compute;reflexivity).
  rewrite handoff_loader_ge in INFO.
  pose proof(proj1(Genv.init_mem_characterization _ _ INFO INITIAL))as PERMISSION.
  change(Mem.range_perm initial(handoff_symbol _admission_cgroup)0 4 Cur Writable)in PERMISSION.
  split;[exact PERMISSION|apply Z.divide_0_r].
Qed.

Theorem namespace_initial_run_access initial:
  Genv.init_mem EntrySource.prog=Some initial ->
  Mem.valid_access initial Mint64(handoff_symbol _run_id)0 Writable.
Proof.
  intro INITIAL.
  assert(INFO:Genv.find_var_info(Clight.genv_genv handoff_ge)(handoff_symbol _run_id)=Some v_run_id)
    by(unfold handoff_ge,handoff_symbol;vm_compute;reflexivity).
  rewrite handoff_loader_ge in INFO.
  pose proof(proj1(Genv.init_mem_characterization _ _ INFO INITIAL))as PERMISSION.
  change(Mem.range_perm initial(handoff_symbol _run_id)0 8 Cur Writable)in PERMISSION.
  split;[exact PERMISSION|apply Z.divide_0_r].
Qed.

Theorem namespace_constants_valid memory run uid:
  namespace_parent_constants memory run uid ->
  forall object,namespace_constant_object object ->Mem.valid_block memory object.
Proof.
  intros[RESULT MODE MODETEXT REPORTS[BOUNDS MAGIC]]object MEMBER.
  unfold namespace_constant_object,namespace_constant_names in MEMBER;
    cbn[map]in MEMBER;repeat destruct MEMBER as[MEMBER|MEMBER];try contradiction;subst object.
  - eapply Mem.valid_access_valid_block;destruct RESULT as[RUN UID].
    eapply Mem.valid_access_implies;[eapply Mem.load_valid_access;exact RUN|constructor].
  - eapply Mem.valid_access_valid_block;destruct RESULT as[RUN UID].
    eapply Mem.valid_access_implies;[eapply Mem.load_valid_access;exact UID|constructor].
  - eapply Mem.valid_access_valid_block.
    eapply Mem.valid_access_implies;[eapply Mem.load_valid_access;exact MODE|constructor].
  - exact(handoff_string_valid _ _ _ MODETEXT).
  - eapply Mem.perm_valid_block with(ofs:=0);eapply Mem.loadbytes_range_perm;
      [exact MAGIC|change(0<=0<4);lia].
  - exact(handoff_string_valid _ _ _(REPORTS wrong_sequence)).
  - exact(handoff_string_valid _ _ _(REPORTS bad_reserved)).
  - exact(handoff_string_valid _ _ _(REPORTS duplicate_frame)).
  - exact(handoff_string_valid _ _ _(REPORTS short_frame)).
  - exact(handoff_string_valid _ _ _(REPORTS drop_frame)).
Qed.

Definition namespace_parent_global_names:=namespace_constant_names++[_admission_cgroup;_preflight;_root_path;_policy__1].
Lemma namespace_parent_global_symbols:
  Forall(fun id=>Genv.find_symbol handoff_ge id=Some(handoff_symbol id))namespace_parent_global_names.
Proof.
  unfold namespace_parent_global_names,namespace_constant_names;
    repeat constructor;unfold handoff_ge,handoff_symbol;vm_compute;reflexivity.
Qed.
Lemma namespace_parent_global_valid initial id:
  Genv.init_mem EntrySource.prog=Some initial ->In id namespace_parent_global_names ->
  Mem.valid_block initial(handoff_symbol id).
Proof.
  intros INITIAL MEMBER;pose proof namespace_parent_global_symbols as SYMBOLS;rewrite Forall_forall in SYMBOLS.
  pose proof(SYMBOLS id MEMBER)as SYMBOL;rewrite handoff_loader_ge in SYMBOL.
  exact(@Genv.find_symbol_not_fresh Clight.fundef type EntrySource.prog id(handoff_symbol id)initial INITIAL SYMBOL).
Qed.
Local Opaque handoff_ge handoff_symbol.
Lemma namespace_parent_globals_distinct left right:
  In left namespace_parent_global_names ->In right namespace_parent_global_names ->left<>right ->
  handoff_symbol left<>handoff_symbol right.
Proof.
  intros LEFT RIGHT DIFFERENT SAME;apply DIFFERENT.
  pose proof namespace_parent_global_symbols as SYMBOLS;rewrite Forall_forall in SYMBOLS.
  eapply Genv.genv_vars_inj;[apply SYMBOLS;exact LEFT|rewrite SAME;apply SYMBOLS;exact RIGHT].
Qed.
Lemma namespace_constant_foreign id object:
  In id namespace_parent_global_names ->~In id namespace_constant_names ->
  namespace_constant_object object ->object<>handoff_symbol id.
Proof.
  intros GLOBAL OUTSIDE MEMBER;apply in_map_iff in MEMBER;destruct MEMBER as[other[SAME MEMBER]];subst object.
  apply namespace_parent_globals_distinct.
  - unfold namespace_parent_global_names;apply in_or_app;left;exact MEMBER.
  - exact GLOBAL.
  - intro SAME;subst other;contradiction.
Qed.

Local Transparent handoff_ge handoff_symbol.
Theorem namespace_initial_run_value initial:
  Genv.init_mem EntrySource.prog=Some initial ->
  Mem.load Mint64 initial(handoff_symbol _run_id)0=Some(Vlong Int64.zero).
Proof.
  intro INITIAL.
  assert(INFO:Genv.find_var_info(Clight.genv_genv handoff_ge)(handoff_symbol _run_id)=Some v_run_id)
    by(unfold handoff_ge,handoff_symbol;vm_compute;reflexivity).
  rewrite handoff_loader_ge in INFO.
  destruct(Genv.init_mem_characterization _ _ INFO INITIAL)as[PERM[ONLY[DATA BYTES]]].
  specialize(BYTES eq_refl).
  change(Mem.loadbytes initial(handoff_symbol _run_id)0 8=
    Some(encode_val Mint64(Vlong Int64.zero)))in BYTES.
  pose proof(Mem.loadbytes_load Mint64 _ _ _ _(BYTES)ltac:(apply Z.divide_0_r))as LOAD.
  change(decode_val Mint64(encode_val Mint64(Vlong Int64.zero)))with(Vlong Int64.zero)in LOAD;exact LOAD.
Qed.
Theorem namespace_initial_uid_value initial:
  Genv.init_mem EntrySource.prog=Some initial ->
  Mem.load Mint32 initial(handoff_symbol _run_uid)0=Some(Vint Int.zero).
Proof.
  intro INITIAL;pose proof handoff_initial_uid_info as INFO;rewrite handoff_loader_ge in INFO.
  destruct(Genv.init_mem_characterization _ _ INFO INITIAL)as[PERM[ONLY[DATA BYTES]]].
  specialize(BYTES eq_refl).
  change(Mem.loadbytes initial(handoff_symbol _run_uid)0 4=
    Some(encode_val Mint32(Vint Int.zero)))in BYTES.
  pose proof(Mem.loadbytes_load Mint32 _ _ _ _(BYTES)ltac:(apply Z.divide_0_r))as LOAD.
  change(decode_val Mint32(encode_val Mint32(Vint Int.zero)))with(Vint Int.zero)in LOAD;exact LOAD.
Qed.

Theorem namespace_initial_constants initial:
  Genv.init_mem EntrySource.prog=Some initial ->namespace_parent_constants initial Int64.zero Int.zero.
Proof.
  intro INITIAL;constructor.
  - split;[apply namespace_initial_run_value|apply namespace_initial_uid_value];exact INITIAL.
  - exact(handoff_initial_mode_value _ INITIAL).
  - pose proof(handoff_initial_literals _ INITIAL)as LITERALS;inversion LITERALS;subst;exact H1.
  - apply namespace_initial_report_literals;exact INITIAL.
  - apply namespace_initial_report_magic;exact INITIAL.
Qed.

Theorem namespace_constants_uid_store before after run old_uid uid:
  namespace_parent_constants before run old_uid ->
  Mem.store Mint32 before(handoff_symbol _run_uid)0(Vint uid)=Some after ->
  namespace_parent_constants after run uid.
Proof.
  intros[GLOBALS MODE MODETEXT REPORTS MAGIC]STORE.
  assert(DIFFERENT:forall id,In id namespace_constant_names ->id<>_run_uid ->
    handoff_symbol id<>handoff_symbol _run_uid).
  { intros id MEMBER OTHER;apply namespace_parent_globals_distinct;
      [unfold namespace_parent_global_names;apply in_or_app;left;exact MEMBER|
       unfold namespace_parent_global_names,namespace_constant_names;cbn;auto 14|exact OTHER]. }
  pose proof(handoff_fixture_store_frame _ _ _ _ _ _ STORE)as FRAME;constructor.
  - destruct GLOBALS as[RUN UID];split.
    + erewrite Mem.load_store_other;[exact RUN|exact STORE|left;apply DIFFERENT;[cbn;auto 12|discriminate]].
    + erewrite Mem.load_store_same by exact STORE;reflexivity.
  - eapply handoff_fixture_load_frame;[exact FRAME| |exact MODE].
    intros;apply DIFFERENT;[cbn;auto 12|discriminate].
  - eapply handoff_fixture_string_frame;[exact FRAME| |exact MODETEXT].
    intros;apply DIFFERENT;[cbn;auto 12|discriminate].
  - intro tag;eapply handoff_fixture_string_frame;[exact FRAME| |apply REPORTS].
    intros;apply DIFFERENT;destruct tag;cbn;auto 12;discriminate.
  - destruct MAGIC as[BOUNDS BYTES];split;[exact BOUNDS|].
    eapply Mem.loadbytes_unchanged_on;[exact FRAME| |exact BYTES].
    intros;apply DIFFERENT;[cbn;auto 12|discriminate].
Qed.

Theorem namespace_constants_run_store before after old_run run uid:
  namespace_parent_constants before old_run uid ->
  Mem.store Mint64 before(handoff_symbol _run_id)0(Vlong run)=Some after ->
  namespace_parent_constants after run uid.
Proof.
  intros[GLOBALS MODE MODETEXT REPORTS MAGIC]STORE.
  assert(DIFFERENT:forall id,In id namespace_constant_names ->id<>_run_id ->
    handoff_symbol id<>handoff_symbol _run_id).
  { intros id MEMBER OTHER;apply namespace_parent_globals_distinct;
      [unfold namespace_parent_global_names;apply in_or_app;left;exact MEMBER|
       unfold namespace_parent_global_names,namespace_constant_names;cbn;auto 14|exact OTHER]. }
  pose proof(handoff_fixture_store_frame _ _ _ _ _ _ STORE)as FRAME;constructor.
  - destruct GLOBALS as[RUN UID];split.
    + erewrite Mem.load_store_same by exact STORE;reflexivity.
    + erewrite Mem.load_store_other;[exact UID|exact STORE|left;apply DIFFERENT;[cbn;auto 12|discriminate]].
  - eapply handoff_fixture_load_frame;[exact FRAME| |exact MODE].
    intros;apply DIFFERENT;[cbn;auto 12|discriminate].
  - eapply handoff_fixture_string_frame;[exact FRAME| |exact MODETEXT].
    intros;apply DIFFERENT;[cbn;auto 12|discriminate].
  - intro tag;eapply handoff_fixture_string_frame;[exact FRAME| |apply REPORTS].
    intros;apply DIFFERENT;destruct tag;cbn;auto 12;discriminate.
  - destruct MAGIC as[BOUNDS BYTES];split;[exact BOUNDS|].
    eapply Mem.loadbytes_unchanged_on;[exact FRAME| |exact BYTES].
    intros;apply DIFFERENT;[cbn;auto 12|discriminate].
Qed.

Theorem namespace_constants_store_foreign before after run uid id chunk offset value:
  In id namespace_parent_global_names ->~In id namespace_constant_names ->
  namespace_parent_constants before run uid ->
  Mem.store chunk before(handoff_symbol id)offset value=Some after ->
  namespace_parent_constants after run uid.
Proof.
  intros GLOBAL OUTSIDE CONSTANTS STORE;eapply namespace_constants_preserved;[exact CONSTANTS|].
  eapply Mem.store_unchanged_on;[exact STORE|].
  intros position RANGE MEMBER;exact(namespace_constant_foreign _ _ GLOBAL OUTSIDE MEMBER eq_refl).
Qed.
Theorem namespace_constants_bytes_foreign before after run uid id offset values:
  In id namespace_parent_global_names ->~In id namespace_constant_names ->
  namespace_parent_constants before run uid ->
  Mem.storebytes before(handoff_symbol id)offset values=Some after ->
  namespace_parent_constants after run uid.
Proof.
  intros GLOBAL OUTSIDE CONSTANTS STORE;eapply namespace_constants_preserved;[exact CONSTANTS|].
  eapply Mem.storebytes_unchanged_on;[exact STORE|].
  intros position RANGE MEMBER;exact(namespace_constant_foreign _ _ GLOBAL OUTSIDE MEMBER eq_refl).
Qed.
