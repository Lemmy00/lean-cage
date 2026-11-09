(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.acceptance: Useful executions reach image replacement through all real source guards. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess Library LibraryMachine WriteAll.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffStructure NativeHandoffArguments
  NativeHandoffAllocation NativeHandoffInput NativeHandoffInitial NativeHandoffMemory NativeHandoffEncoding
  NativeHandoffDescriptors NativeHandoffLoop NativeHandoffFlags NativeHandoffExec NativeHandoffSuccess
  NativeHandoffTables NativeHandoffGuest NativeHandoffStdout NativeHandoffSuffix.
From LeanCageMainNumber Require Import NumberMemory NumberMath.
Import ListNotations.
Open Scope Z_scope.
Local Opaque handoff_ge handoff_symbol.

Definition handoff_useful_encoding words encode := forall index,0<=index<4 ->
  (1<=length(encode index)<32)%nat /\ Forall(fun byte=>byte<>Byte.zero)(encode index) /\
  decimal_number(encode index)=Some(Int.signed(words index)).

Fixpoint handoff_encoding_range(encode:Z->list Byte.int)index slots:=match slots with
  |O=>[]|S rest=>encode index::handoff_encoding_range encode(index+1)rest end.

Theorem handoff_useful_iterations_exact cell input b words encode : forall slots index texts before le k failure uidbytes,
  handoff_private_layout cell input b -> handoff_live_data cell input b words before ->
  0<=index -> index+Z.of_nat slots=4 -> length texts=Z.to_nat index ->
  le!EntrySource._i=Some(Vint(Int.repr index)) -> le!EntrySource._failure=Some(Vint failure) ->
  number_input before(handoff_uid b)Ptrofs.zero uidbytes -> handoff_fd_history b words before 0 texts ->
  handoff_descriptors_checked words 4 -> handoff_useful_encoding words encode ->
  exists after final completed events,
    handoff_live_data cell input b words after /\ final!EntrySource._failure=Some(Vint failure) /\
    number_input after(handoff_uid b)Ptrofs.zero uidbytes /\ handoff_fd_history b words after 0 completed /\
    length completed=4%nat /\
    completed=texts++handoff_encoding_range encode index slots /\
    entry_handoff_steps handoff_ge cell
      (live(State EntrySource.f_guest handoff_descriptor_iterations k(handoff_locals_env b)le before))events
      (live(State EntrySource.f_guest Sskip k(handoff_locals_env b)final after)).
Proof.
  induction slots as[|slots IH];intros index texts before le k failure uidbytes LAYOUT LIVE LOW END LENGTH
    INDEX FAILURE UIDTEXT HISTORY CHECKED ENCODE.
  - cbn[Z.of_nat]in END;assert(index=4)by lia;subst index.
    exists before,le,texts;eexists;split;[exact LIVE|]. split;[exact FAILURE|]. split;[exact UIDTEXT|].
    split;[exact HISTORY|]. split;[exact LENGTH|]. split;[rewrite app_nil_r;reflexivity|].
    eapply handoff_success_path;[apply handoff_descriptor_exit_source;exact INDEX|constructor].
  - assert(INDEXBOUND:0<=index<4)by(rewrite Nat2Z.inj_succ in END;lia).
    destruct(CHECKED index INDEXBOUND)as[POSITIVE DISTINCT].
    set(loopk:=Kloop1 handoff_descriptor_body handoff_descriptor_increment k).
    destruct(handoff_validation_success(handoff_locals_env b)le before loopk(handoff_handles b)words index
      ltac:(unfold handoff_locals_env;WriteAll.lookup)INDEX INDEXBOUND
      (handoff_live_handles _ _ _ _ _ LIVE)POSITIVE DISTINCT)as[count[validated[FRAME VALIDATION]]].
    assert(VALIDINDEX:validated!EntrySource._i=Some(Vint(Int.repr index)))by(rewrite FRAME by discriminate;exact INDEX).
    assert(VALIDFAILURE:validated!EntrySource._failure=Some(Vint failure))by(rewrite FRAME by discriminate;exact FAILURE).
    destruct(ENCODE index INDEXBOUND)as[BYTES[NONZERO PARSED]].
    destruct(handoff_fd_success cell input b words before validated loopk failure index(encode index)
      LAYOUT LIVE INDEXBOUND POSITIVE VALIDINDEX VALIDFAILURE BYTES NONZERO PARSED)
      as[middle[encoded[ENCODEDEVENTS[MIDDLE[ENCODEDINDEX[ENCODEDFAILURE[TEXT[ENCODEFRAME ENCODING]]]]]]]].
    assert(MIDDLEUID:number_input middle(handoff_uid b)Ptrofs.zero uidbytes)
      by(eapply handoff_encoding_preserves_uid;[exact LAYOUT|exact ENCODEFRAME|exact UIDTEXT]).
    assert(MIDDLEHISTORY:handoff_fd_history b words middle 0 texts).
    { eapply handoff_fd_history_preserved;[exact LAYOUT|exact ENCODEFRAME|lia| |lia|exact HISTORY].
      rewrite LENGTH,Z2Nat.id by lia;lia. }
    assert(NEWHISTORY:handoff_fd_history b words middle 0(texts++[encode index])).
    { apply handoff_fd_history_snoc;[exact MIDDLEHISTORY| |exact BYTES|].
      - rewrite LENGTH,Z2Nat.id by lia;replace(0+index)with index by lia;exact TEXT.
      - rewrite LENGTH,Z2Nat.id by lia;replace(0+index)with index by lia;exact PARSED. }
    assert(NEWLENGTH:length(texts++[encode index])=Z.to_nat(index+1)).
    { rewrite length_app;cbn[length];rewrite LENGTH,Z2Nat.inj_add by lia;cbn;lia. }
    set(advanced:=PTree.set EntrySource._i(Vint(Int.repr(index+1)))encoded).
    destruct(IH(index+1)(texts++[encode index])middle advanced k failure uidbytes LAYOUT MIDDLE
      ltac:(lia)ltac:(rewrite Nat2Z.inj_succ in END;lia)NEWLENGTH
      ltac:(unfold advanced;apply PTree.gss)ltac:(unfold advanced;rewrite PTree.gso by discriminate;exact ENCODEDFAILURE)
      MIDDLEUID NEWHISTORY CHECKED ENCODE)
      as[after[final[completed[LOOPEVENTS[AFTER[FINALFAILURE[AFTERUID[AFTERHISTORY[COMPLETED[EXACT_TEXTS LOOP]]]]]]]]]].
    exists after,final,completed;eexists;split;[exact AFTER|]. split;[exact FINALFAILURE|]. split;[exact AFTERUID|].
    split;[exact AFTERHISTORY|]. split;[exact COMPLETED|]. split.
    { rewrite EXACT_TEXTS;cbn[handoff_encoding_range];rewrite <-app_assoc;reflexivity. }
    eapply handoff_success_path.
    + apply handoff_descriptor_iteration_source with(index:=index);assumption.
    + eapply handoff_success_path;[exact VALIDATION|].
      eapply handoff_success_trans;[exact ENCODING|].
      eapply handoff_success_path.
      * apply handoff_descriptor_increment_source with(index:=index);assumption.
      * exact LOOP.
Qed.

Theorem handoff_useful_iterations cell input b words encode : forall slots index texts before le k failure uidbytes,
  handoff_private_layout cell input b -> handoff_live_data cell input b words before ->
  0<=index -> index+Z.of_nat slots=4 -> length texts=Z.to_nat index ->
  le!EntrySource._i=Some(Vint(Int.repr index)) -> le!EntrySource._failure=Some(Vint failure) ->
  number_input before(handoff_uid b)Ptrofs.zero uidbytes -> handoff_fd_history b words before 0 texts ->
  handoff_descriptors_checked words 4 -> handoff_useful_encoding words encode ->
  exists after final completed events,
    handoff_live_data cell input b words after /\ final!EntrySource._failure=Some(Vint failure) /\
    number_input after(handoff_uid b)Ptrofs.zero uidbytes /\ handoff_fd_history b words after 0 completed /\
    length completed=4%nat /\
    entry_handoff_steps handoff_ge cell
      (live(State EntrySource.f_guest handoff_descriptor_iterations k(handoff_locals_env b)le before))events
      (live(State EntrySource.f_guest Sskip k(handoff_locals_env b)final after)).
Proof.
  intros slots index texts before le k failure uidbytes LAYOUT LIVE LOW END LENGTH INDEX FAILURE UIDTEXT HISTORY CHECKED ENCODE.
  destruct(handoff_useful_iterations_exact cell input b words encode slots index texts before le k failure uidbytes
    LAYOUT LIVE LOW END LENGTH INDEX FAILURE UIDTEXT HISTORY CHECKED ENCODE)
    as[after[final[completed[events[AFTER[FINALFAILURE[AFTERUID[AFTERHISTORY[COMPLETED[TEXTS RUN]]]]]]]]]].
  exists after,final,completed,events;split;[exact AFTER|]. split;[exact FINALFAILURE|]. split;[exact AFTERUID|].
  split;[exact AFTERHISTORY|]. split;assumption.
Qed.

Theorem handoff_useful_initial cell input before input_fd output_fd errors_fd failure k :
  handoff_borrowed_input cell before input -> handoff_borrowed_mode_bytes input=handoff_normal_bytes ->
  100000<=Int.unsigned(handoff_borrowed_uid input)<=100999 ->
  exists b after final events,
    handoff_private_layout cell input b /\
    handoff_live_data cell input b(handoff_original_words input_fd output_fd errors_fd failure)after /\
    final!EntrySource._failure=Some(Vint failure) /\
    entry_handoff_steps handoff_ge cell
      (live(Callstate(Internal EntrySource.f_guest)[Vint input_fd;Vint output_fd;Vint errors_fd;Vint failure]k before))events
      (live(State EntrySource.f_guest(guest_tail 6(fn_body EntrySource.f_guest))k(handoff_locals_env b)final after)).
Proof.
  intros INPUT MODE UIDBOUND.
  destruct(handoff_entry_allocates before input_fd output_fd errors_fd failure k)
    as[b[allocated[ENTRY[ALLOC OWN]]]].
  destruct(handoff_layout_allocated cell input before b allocated INPUT ALLOC)as[LAYOUT LOCALOWN].
  pose proof(handoff_borrowed_allocated cell input before b allocated INPUT ALLOC)as BORROWED.
  set(original:=handoff_parameter_env input_fd output_fd errors_fd failure).
  destruct(handoff_parameter_bindings input_fd output_fd errors_fd failure)as[INPUTPARAM[OUTPUTPARAM[ERRORSPARAM FAILUREPARAM]]].
  assert(NORMAL:c_string allocated handoff_normal_address handoff_normal_bytes).
  { pose proof(handoff_borrowed_literals _ _ _ BORROWED)as LITERALS;inversion LITERALS;subst;exact H1. }
  assert(MODETEXT:c_string allocated(handoff_borrowed_mode input)handoff_normal_bytes).
  { rewrite <- MODE;exact(handoff_borrowed_mode_text _ _ _ BORROWED). }
  assert(COMPARE:strcmp_result allocated(handoff_borrowed_mode input)handoff_normal_address Int.zero).
  { exists handoff_normal_bytes,handoff_normal_bytes;split;[exact MODETEXT|]. split;[exact NORMAL|].
    rewrite(proj2(compare_bytes_equal _ _)eq_refl);reflexivity. }
  set(returned:=handoff_mode_returned original(address_block(handoff_borrowed_mode input))
    (Ptrofs.repr(address_offset(handoff_borrowed_mode input)))Int.zero).
  assert(RI:returned!EntrySource._input=Some(Vint input_fd)).
  { unfold returned,handoff_mode_returned,handoff_mode_loaded;rewrite !PTree.gso by discriminate;exact INPUTPARAM. }
  assert(RO:returned!EntrySource._output=Some(Vint output_fd)).
  { unfold returned,handoff_mode_returned,handoff_mode_loaded;rewrite !PTree.gso by discriminate;exact OUTPUTPARAM. }
  assert(RE:returned!EntrySource._errors=Some(Vint errors_fd)).
  { unfold returned,handoff_mode_returned,handoff_mode_loaded;rewrite !PTree.gso by discriminate;exact ERRORSPARAM. }
  assert(RF:returned!EntrySource._failure=Some(Vint failure)).
  { unfold returned,handoff_mode_returned,handoff_mode_loaded;rewrite !PTree.gso by discriminate;exact FAILUREPARAM. }
  destruct(handoff_handle_stores_exist b allocated input_fd output_fd errors_fd failure
    (handoff_local_object b allocated(handoff_handles b)16 LOCALOWN ltac:(unfold handoff_objects;cbn;auto)))
    as[after STORES].
  assert(AFTER:handoff_live_data cell input b(handoff_original_words input_fd output_fd errors_fd failure)after)
    by(eapply handoff_live_initialized;[exact LAYOUT|exact BORROWED|exact LOCALOWN|exact STORES]).
  set(final:=handoff_uid_env returned(handoff_borrowed_uid input)).
  assert(BAD:handoff_uid_bad(handoff_borrowed_uid input)=false)by(apply handoff_uid_checked;exact UIDBOUND).
  pose proof(handoff_uid_guard_source b returned after(handoff_borrowed_uid input)
    (Kseq(guest_tail 6(fn_body EntrySource.f_guest))k)
    (handoff_borrowed_uid_load _ _ _ (handoff_live_borrowed _ _ _ _ _ AFTER)))as GUARDED.
  rewrite BAD in GUARDED.
  exists b,after,final;eexists;split;[exact LAYOUT|]. split;[exact AFTER|]. split.
  - unfold final,returned;rewrite handoff_initial_temps_preserved by(cbn;intuition discriminate);exact FAILUREPARAM.
  - eapply handoff_success_edge;[exact ENTRY|].
    eapply handoff_success_path.
    + apply handoff_mode_source;exact(handoff_borrowed_mode_load _ _ _ BORROWED).
    + econstructor;[apply entry_library_step;apply strcmp_step with(left:=handoff_borrowed_mode input)(right:=handoff_normal_address)(value:=Int.zero);exact COMPARE|].
      eapply handoff_success_path;[apply handoff_mode_return_source with(value:=Int.zero)|].
      handoff_success_route;eapply handoff_success_path.
      * apply handoff_handle_initialization_source with(input:=input_fd)(output:=output_fd)(errors:=errors_fd)(failure:=failure);
          [exact RI|exact RO|exact RE|exact RF|exact STORES].
      * handoff_success_route;eapply handoff_success_path;[exact GUARDED|]. handoff_success_route;constructor.
Qed.

Theorem handoff_useful_stdout cell input b words before le k failure :
  handoff_live_data cell input b words before -> le!EntrySource._failure=Some(Vint failure) ->
  exists final events,
    final!EntrySource._failure=Some(Vint failure) /\
    entry_handoff_steps handoff_ge cell
      (live(State EntrySource.f_guest(guest_tail 10(fn_body EntrySource.f_guest))k(handoff_locals_env b)le before))events
      (live(State EntrySource.f_guest guest_argument_tail k(handoff_locals_env b)final before)).
Proof.
  intros LIVE FAILURE.
  exists(PTree.set EntrySource._t'18(Vint Int.zero)le);eexists;split.
  - rewrite PTree.gso by discriminate;exact FAILURE.
  - rewrite handoff_stdout_tail_actual at 1;handoff_success_route.
    eapply handoff_success_path.
    + apply handoff_stdout_flags_call_source;apply handoff_nonlocal_binding;cbn;intuition discriminate.
    + econstructor.
      * apply entry_flags_step with(returned:=Int.zero);
          [apply Mem.unchanged_on_refl|exact(handoff_borrowed_errno _ _ _ (handoff_live_borrowed _ _ _ _ _ LIVE))].
      * eapply handoff_success_path;[apply handoff_flags_return_source|]. handoff_success_route;constructor.
Qed.

Record handoff_chosen_image_data cell input b words memory uidbytes encode:Prop:={
  handoff_chosen_live:handoff_live_data cell input b words memory;
  handoff_chosen_uid:number_input memory(handoff_uid b)Ptrofs.zero uidbytes;
  handoff_chosen_uid_length:(1<=length uidbytes<32)%nat;
  handoff_chosen_fds:handoff_fd_history b words memory 0(handoff_encoding_range encode 0 4);
  handoff_chosen_argv:handoff_pointer_table memory(handoff_arguments b)(handoff_public_arguments b input);
  handoff_chosen_environment:handoff_pointer_table memory(handoff_environment b)handoff_environment_values
}.

Theorem handoff_useful_image_data cell input before input_fd output_fd errors_fd failure k uidbytes encode :
  handoff_borrowed_input cell before input -> handoff_borrowed_mode_bytes input=handoff_normal_bytes ->
  100000<=Int.unsigned(handoff_borrowed_uid input)<=100999 ->
  handoff_descriptors_checked(handoff_original_words input_fd output_fd errors_fd failure)4 ->
  (1<=length uidbytes<32)%nat -> Forall(fun byte=>byte<>Byte.zero)uidbytes ->
  decimal_number uidbytes=Some(Int.unsigned(handoff_borrowed_uid input)) ->
  handoff_useful_encoding(handoff_original_words input_fd output_fd errors_fd failure)encode ->
  exists b after caller prefix,
    let endpoint:=Callstate entry_exec_definition
      [Vptr(handoff_symbol EntrySource.___stringlit_111)Ptrofs.zero;
       Vptr(handoff_arguments b)Ptrofs.zero;Vptr(handoff_environment b)Ptrofs.zero]
      (handoff_exec_cont(handoff_locals_env b)caller(Kseq(guest_tail 24(fn_body EntrySource.f_guest))k))after in
    handoff_image_snapshot cell input input_fd output_fd errors_fd failure endpoint /\
    handoff_chosen_image_data cell input b(handoff_original_words input_fd output_fd errors_fd failure)after uidbytes encode /\
    entry_handoff_steps handoff_ge cell
      (live(Callstate(Internal EntrySource.f_guest)[Vint input_fd;Vint output_fd;Vint errors_fd;Vint failure]k before))prefix(live endpoint) /\
    entry_handoff_steps handoff_ge cell
      (live(Callstate(Internal EntrySource.f_guest)[Vint input_fd;Vint output_fd;Vint errors_fd;Vint failure]k before))
      (prefix++[entry_image(Vptr(handoff_symbol EntrySource.___stringlit_111)Ptrofs.zero)
        (Vptr(handoff_arguments b)Ptrofs.zero)(Vptr(handoff_environment b)Ptrofs.zero)])(dead after).
Proof.
  intros INPUT MODE UIDBOUND CHECKED UIDLENGTH UIDNONZERO UIDPARSED ENCODE.
  set(words:=handoff_original_words input_fd output_fd errors_fd failure).
  destruct(handoff_useful_initial cell input before input_fd output_fd errors_fd failure k INPUT MODE UIDBOUND)
    as[b[initialized[initialle[INITEVENTS[LAYOUT[INITIAL[INITIALFAILURE INIT]]]]]]].
  destruct(handoff_uid_success cell input b words initialized initialle k failure uidbytes
    LAYOUT INITIAL INITIALFAILURE UIDLENGTH UIDNONZERO UIDPARSED)
    as[uid_after[uidle[UIDEVENTS[UIDLIVE[UIDFAILURE[UIDTEXT UID]]]]]].
  set(started:=PTree.set EntrySource._i(Vint Int.zero)uidle).
  destruct(handoff_useful_iterations_exact cell input b words encode 4%nat 0 [] uid_after started
    (Kseq(guest_tail 10(fn_body EntrySource.f_guest))k)failure uidbytes LAYOUT UIDLIVE
    ltac:(lia)eq_refl eq_refl ltac:(unfold started;apply PTree.gss)
    ltac:(unfold started;rewrite PTree.gso by discriminate;exact UIDFAILURE)UIDTEXT I CHECKED ENCODE)
    as[fd_after[fdle[fdtexts[FDEVENTS[FDLIVE[FDFAILURE[FDUINT[FDHISTORY[FDLENGTH[FDCHOICE FDS]]]]]]]]]].
  destruct(handoff_useful_stdout cell input b words fd_after fdle k failure FDLIVE FDFAILURE)
    as[stdoutle[STDOUTEVENTS[STDOUTFAILURE STDOUT]]].
  destruct(handoff_argument_tables_source cell input b words fd_after stdoutle k failure LAYOUT FDLIVE STDOUTFAILURE)
    as[after[count[copied[COUNTBOUND[AFTER[TABLEFRAME[ARGSTABLE[ENVTABLE[FINALFAILURE TABLEPATH]]]]]]]]].
  set(caller:=handoff_checked_argument_env copied(handoff_borrowed_source input)(handoff_borrowed_source_offset input)).
  assert(SNAPSHOT:handoff_image_snapshot cell input input_fd output_fd errors_fd failure
    (Callstate entry_exec_definition
      [Vptr(handoff_symbol EntrySource.___stringlit_111)Ptrofs.zero;
       Vptr(handoff_arguments b)Ptrofs.zero;Vptr(handoff_environment b)Ptrofs.zero]
      (handoff_exec_cont(handoff_locals_env b)caller(Kseq(guest_tail 24(fn_body EntrySource.f_guest))k))after)).
  { exists b,after,caller,uidbytes,fdtexts,k;split;[reflexivity|]. split.
    - unfold caller,handoff_checked_argument_env;rewrite !PTree.gso by discriminate;exact FINALFAILURE.
    - split;[exact AFTER|]. split;[exact MODE|]. split;[exact UIDBOUND|]. split.
      + destruct(handoff_tables_numbers_separate b(proj1 LAYOUT))as[UIDARGS[UIDENV REST]].
        eapply handoff_tables_preserves_input;[exact TABLEFRAME|exact UIDARGS|exact UIDENV|exact FDUINT].
      + split;[exact UIDLENGTH|]. split;[exact UIDPARSED|]. split.
        * eapply handoff_fd_history_tables;[exact(proj1 LAYOUT)|exact TABLEFRAME|exact FDHISTORY].
        * split;[exact FDLENGTH|]. split;[exact CHECKED|]. split;assumption. }
  assert(RUN:exists prefix,entry_handoff_steps handoff_ge cell
    (live(Callstate(Internal EntrySource.f_guest)[Vint input_fd;Vint output_fd;Vint errors_fd;Vint failure]k before))prefix
    (live(Callstate entry_exec_definition
      [Vptr(handoff_symbol EntrySource.___stringlit_111)Ptrofs.zero;
       Vptr(handoff_arguments b)Ptrofs.zero;Vptr(handoff_environment b)Ptrofs.zero]
      (handoff_exec_cont(handoff_locals_env b)caller(Kseq(guest_tail 24(fn_body EntrySource.f_guest))k))after))).
  { eexists;eapply handoff_success_trans;[exact INIT|]. eapply handoff_success_trans;[exact UID|].
    rewrite handoff_descriptors_tail_actual at 1;handoff_success_route.
    rewrite handoff_descriptor_loop_actual at 1;handoff_success_route.
    eapply handoff_success_edge;[apply certified_set_edge with(v:=Vint Int.zero);apply old_expression_value,value_int|].
    handoff_success_route;eapply handoff_success_trans;[exact FDS|]. handoff_success_route.
    eapply handoff_success_trans;[exact STDOUT|]. eapply handoff_success_path;[exact TABLEPATH|constructor]. }
  assert(DATA:handoff_chosen_image_data cell input b words after uidbytes encode).
  { constructor.
    - exact AFTER.
    - destruct(handoff_tables_numbers_separate b(proj1 LAYOUT))as[UIDARGS[UIDENV REST]].
      eapply handoff_tables_preserves_input;[exact TABLEFRAME|exact UIDARGS|exact UIDENV|exact FDUINT].
    - exact UIDLENGTH.
    - cbn[app]in FDCHOICE;rewrite <-FDCHOICE.
      eapply handoff_fd_history_tables;[exact(proj1 LAYOUT)|exact TABLEFRAME|exact FDHISTORY].
    - exact ARGSTABLE.
    - exact ENVTABLE. }
  destruct RUN as[prefix RUN];exists b,after,caller,prefix;split;[exact SNAPSHOT|]. split;[exact DATA|]. split;[exact RUN|].
  eapply handoff_success_trans;[exact RUN|]. econstructor;[apply entry_exec_image_step|constructor].
Qed.

Theorem handoff_useful_image cell input before input_fd output_fd errors_fd failure k uidbytes encode :
  handoff_borrowed_input cell before input -> handoff_borrowed_mode_bytes input=handoff_normal_bytes ->
  100000<=Int.unsigned(handoff_borrowed_uid input)<=100999 ->
  handoff_descriptors_checked(handoff_original_words input_fd output_fd errors_fd failure)4 ->
  (1<=length uidbytes<32)%nat -> Forall(fun byte=>byte<>Byte.zero)uidbytes ->
  decimal_number uidbytes=Some(Int.unsigned(handoff_borrowed_uid input)) ->
  handoff_useful_encoding(handoff_original_words input_fd output_fd errors_fd failure)encode ->
  exists b after caller prefix,
    let endpoint:=Callstate entry_exec_definition
      [Vptr(handoff_symbol EntrySource.___stringlit_111)Ptrofs.zero;
       Vptr(handoff_arguments b)Ptrofs.zero;Vptr(handoff_environment b)Ptrofs.zero]
      (handoff_exec_cont(handoff_locals_env b)caller(Kseq(guest_tail 24(fn_body EntrySource.f_guest))k))after in
    handoff_image_snapshot cell input input_fd output_fd errors_fd failure endpoint /\
    entry_handoff_steps handoff_ge cell
      (live(Callstate(Internal EntrySource.f_guest)[Vint input_fd;Vint output_fd;Vint errors_fd;Vint failure]k before))prefix(live endpoint) /\
    entry_handoff_steps handoff_ge cell
      (live(Callstate(Internal EntrySource.f_guest)[Vint input_fd;Vint output_fd;Vint errors_fd;Vint failure]k before))
      (prefix++[entry_image(Vptr(handoff_symbol EntrySource.___stringlit_111)Ptrofs.zero)
        (Vptr(handoff_arguments b)Ptrofs.zero)(Vptr(handoff_environment b)Ptrofs.zero)])(dead after).
Proof.
  intros INPUT MODE UIDBOUND CHECKED UIDLENGTH UIDNONZERO UIDPARSED ENCODE.
  destruct(handoff_useful_image_data cell input before input_fd output_fd errors_fd failure k uidbytes encode
    INPUT MODE UIDBOUND CHECKED UIDLENGTH UIDNONZERO UIDPARSED ENCODE)
    as(b &after &caller &prefix &SNAPSHOT &DATA &PREFIX &RUN).
  exists b,after,caller,prefix;split;[exact SNAPSHOT|]. split;assumption.
Qed.

Definition handoff_example_encode index := [Byte.repr(52+index)].
Definition handoff_example_uid := map Byte.repr[49;48;48;48;48;48].

Lemma handoff_example_word index : 0<=index<4 ->
  handoff_original_words(Int.repr 4)(Int.repr 5)(Int.repr 6)(Int.repr 7)index=Int.repr(4+index).
Proof.
  intros BOUND;assert(CASES:index=0 \/ index=1 \/ index=2 \/ index=3)by lia.
  destruct CASES as[SAME|[SAME|[SAME|SAME]]];subst index;vm_compute;reflexivity.
Qed.
Theorem handoff_example_descriptors :
  handoff_descriptors_checked(handoff_original_words(Int.repr 4)(Int.repr 5)(Int.repr 6)(Int.repr 7))4.
Proof.
  intros index BOUND;split.
  - rewrite handoff_example_word by exact BOUND;rewrite Int.signed_repr;[lia|].
    change Int.min_signed with(-2147483648);change Int.max_signed with 2147483647;lia.
  - intros previous PREVIOUS;rewrite !handoff_example_word by lia;apply Int.eq_false.
    intros SAME;apply(f_equal Int.signed)in SAME;rewrite !Int.signed_repr in SAME;
      change Int.min_signed with(-2147483648)in *;change Int.max_signed with 2147483647 in *;lia.
Qed.

Theorem handoff_example_encoding :
  handoff_useful_encoding(handoff_original_words(Int.repr 4)(Int.repr 5)(Int.repr 6)(Int.repr 7))handoff_example_encode.
Proof.
  intros index BOUND;assert(CASES:index=0 \/ index=1 \/ index=2 \/ index=3)by lia.
  destruct CASES as[SAME|[SAME|[SAME|SAME]]];subst index;vm_compute.
  all:split;[lia|].
  all:split;[constructor;[discriminate|constructor]|reflexivity].
Qed.

Theorem handoff_example_uid_correct :
  (1<=length handoff_example_uid<32)%nat /\
  Forall(fun byte=>byte<>Byte.zero)handoff_example_uid /\ decimal_number handoff_example_uid=Some 100000.
Proof.
  vm_compute;split;[lia|]. split;[repeat constructor;discriminate|reflexivity].
Qed.

Theorem handoff_example_image cell input before k :
  handoff_borrowed_input cell before input ->
  handoff_borrowed_mode_bytes input=handoff_normal_bytes -> handoff_borrowed_uid input=Int.repr 100000 ->
  exists b after caller prefix,
    let endpoint:=Callstate entry_exec_definition
      [Vptr(handoff_symbol EntrySource.___stringlit_111)Ptrofs.zero;
       Vptr(handoff_arguments b)Ptrofs.zero;Vptr(handoff_environment b)Ptrofs.zero]
      (handoff_exec_cont(handoff_locals_env b)caller(Kseq(guest_tail 24(fn_body EntrySource.f_guest))k))after in
    handoff_image_snapshot cell input(Int.repr 4)(Int.repr 5)(Int.repr 6)(Int.repr 7)endpoint /\
    entry_handoff_steps handoff_ge cell
      (live(Callstate(Internal EntrySource.f_guest)[Vint(Int.repr 4);Vint(Int.repr 5);Vint(Int.repr 6);Vint(Int.repr 7)]k before))prefix(live endpoint) /\
    entry_handoff_steps handoff_ge cell
      (live(Callstate(Internal EntrySource.f_guest)[Vint(Int.repr 4);Vint(Int.repr 5);Vint(Int.repr 6);Vint(Int.repr 7)]k before))
      (prefix++[entry_image(Vptr(handoff_symbol EntrySource.___stringlit_111)Ptrofs.zero)
        (Vptr(handoff_arguments b)Ptrofs.zero)(Vptr(handoff_environment b)Ptrofs.zero)])(dead after).
Proof.
  intros INPUT MODE UID;destruct handoff_example_uid_correct as[UIDLENGTH[UIDNONZERO UIDPARSED]].
  apply handoff_useful_image with(uidbytes:=handoff_example_uid)(encode:=handoff_example_encode);try assumption.
  - rewrite UID;change(100000<=100000<=100999);lia.
  - exact handoff_example_descriptors.
  - rewrite UID;exact UIDPARSED.
  - exact handoff_example_encoding.
Qed.
