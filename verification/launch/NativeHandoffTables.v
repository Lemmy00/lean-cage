(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Construct the complete argv and environment from caller-owned pointers. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps ScalarMemory Library WriteAll.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffStructure NativeHandoffArguments
  NativeHandoffAllocation NativeHandoffInput NativeHandoffMemory NativeHandoffPrefix NativeHandoffExec NativeHandoffSuffix.
From LeanCageMainNumber Require Import NumberInitial.
Import ListNotations.
Open Scope Z_scope.
Local Opaque handoff_ge handoff_symbol.

Definition handoff_public_arguments b input :=
  handoff_prefix_values b(handoff_borrowed_preflight input)(address_block(handoff_borrowed_mode input))
    (Ptrofs.repr(address_offset(handoff_borrowed_mode input))) ++
  map handoff_argument_value(handoff_borrowed_arguments input)++[Vlong Int64.zero].
Definition handoff_pointer_table m output values := forall position item,
  nth_error values position=Some item ->
  Mem.loadv Mptr m(Vptr output(Ptrofs.repr(8*Z.of_nat position)))=Some(Val.load_result Mptr item).

Lemma handoff_pointer_table_stores output before values after :
  handoff_pointer_stores output 0 before values after -> (length values<=74)%nat ->
  handoff_pointer_table after output values.
Proof.
  intros STORES LENGTH position item FOUND.
  assert(POSITION:(position<length values)%nat)by(apply nth_error_Some;rewrite FOUND;discriminate).
  unfold Mem.loadv;rewrite Ptrofs.unsigned_repr by
    (change Ptrofs.max_unsigned with 18446744073709551615;lia).
  destruct(zle _ _)as[LIMIT|OVER].
  - pose proof(handoff_pointer_stores_content _ _ _ _ _ _ _ STORES FOUND)as CONTENT.
    rewrite Z.add_0_l in CONTENT;exact CONTENT.
  - exfalso;change(8*Z.of_nat position+8>18446744073709551616)in OVER;lia.
Qed.

Lemma handoff_pointer_table_other_stores output before values after other index writes :
  handoff_pointer_table before output values -> output<>other ->
  handoff_pointer_stores other index before writes after -> handoff_pointer_table after output values.
Proof.
  intros TABLE DIFFERENT STORES position item FOUND.
  rewrite(handoff_pointer_stores_load_other _ _ _ _ _ _ _ _ STORES DIFFERENT);apply TABLE;exact FOUND.
Qed.

Lemma handoff_copy_inputs_last m source offset : forall arguments index,
  handoff_copy_inputs m source offset index arguments ->
  Mem.loadv Mptr m(Vptr source(Ptrofs.add offset(Ptrofs.repr(8*(index+Z.of_nat(length arguments))))))=
    Some(Vlong Int64.zero).
Proof.
  induction arguments as[|pointer rest IH];intros index INPUTS;cbn[handoff_copy_inputs]in INPUTS.
  - cbn[length Z.of_nat];rewrite Z.add_0_r;exact INPUTS.
  - destruct INPUTS as[HEAD[WEAK REST]];pose proof(IH(index+1)REST)as LAST.
    cbn[length];rewrite Nat2Z.inj_succ.
    replace(index+Z.succ(Z.of_nat(length rest)))with(index+1+Z.of_nat(length rest))by lia;exact LAST.
Qed.

Theorem handoff_argument_tables_source cell input b words before le k failure :
  handoff_private_layout cell input b -> handoff_live_data cell input b words before ->
  le!EntrySource._failure=Some(Vint failure) ->
  exists after count copied,
    (count<=2048)%nat /\ handoff_live_data cell input b words after /\
    handoff_tables_frame b before after /\
    handoff_pointer_table after(handoff_arguments b)(handoff_public_arguments b input) /\
    handoff_pointer_table after(handoff_environment b)handoff_environment_values /\
    copied!EntrySource._failure=Some(Vint failure) /\
    store_path handoff_ge(handoff_tables_frame b before)
      (State EntrySource.f_guest guest_argument_tail k(handoff_locals_env b)le before)count
      (Callstate entry_exec_definition
        [Vptr(handoff_symbol EntrySource.___stringlit_111)Ptrofs.zero;
         Vptr(handoff_arguments b)Ptrofs.zero;Vptr(handoff_environment b)Ptrofs.zero]
        (handoff_exec_cont(handoff_locals_env b)
          (handoff_checked_argument_env copied(handoff_borrowed_source input)(handoff_borrowed_source_offset input))
          (Kseq(guest_tail 24(fn_body EntrySource.f_guest))k))after).
Proof.
  intros LAYOUT LIVE FAILURE.
  set(preflight:=handoff_borrowed_preflight input).
  set(mode:=address_block(handoff_borrowed_mode input)).
  set(offset:=Ptrofs.repr(address_offset(handoff_borrowed_mode input))).
  set(arguments:=handoff_borrowed_arguments input).
  set(n:=Z.of_nat(length arguments)).
  destruct(handoff_private_object cell input b(handoff_arguments b)592 LAYOUT
    ltac:(unfold handoff_objects;cbn;auto 8))as[ARGSTLS ARGSSHARED].
  assert(GLOBALS:handoff_symbol EntrySource._preflight<>handoff_arguments b /\
    handoff_symbol EntrySource._mode<>handoff_arguments b /\
    handoff_symbol EntrySource._policy__1<>handoff_arguments b /\
    handoff_borrowed_source input<>handoff_arguments b).
  { repeat split;intros SAME;apply ARGSSHARED;rewrite <- SAME;
      (apply handoff_borrowed_global_member;cbn;auto 8)||apply handoff_borrowed_source_member. }
  destruct GLOBALS as[PREFLIGHTSEP[MODESEP[POLICYSEP SOURCESEP]]].
  destruct(handoff_argument_prefix_source_bounded b before le preflight mode offset failure k FAILURE
    (handoff_local_object b before(handoff_arguments b)592 (handoff_live_owned _ _ _ _ _ LIVE)
      ltac:(unfold handoff_objects;cbn;auto 8)) PREFLIGHTSEP MODESEP
    (handoff_borrowed_preflight_load _ _ _ (handoff_live_borrowed _ _ _ _ _ LIVE))
    (handoff_borrowed_mode_load _ _ _ (handoff_live_borrowed _ _ _ _ _ LIVE)))
    as[prefix[prefix_count[prefixle[PREFIXBOUND[PREFIXSTORES[PREFIXFRAME[PREFIXINDEX[PREFIXFAILURE PREFIXPATH]]]]]]]].
  assert(PREFIXLIVE:handoff_live_data cell input b words prefix)
    by(eapply handoff_live_table_stores;[exact LAYOUT|exact LIVE|left;reflexivity|exact PREFIXSTORES]).
  assert(PREFIXTABLES:handoff_tables_frame b before prefix)
    by(eapply handoff_tables_scalar;[left;reflexivity|exact PREFIXSTORES]).
  assert(BOUND:0<=n<=64).
  { unfold n,arguments;pose proof(handoff_borrowed_arguments_bound _ _ _ (handoff_live_borrowed _ _ _ _ _ LIVE));lia. }
  destruct(handoff_pointer_stores_exist(handoff_arguments b)9 prefix(map handoff_argument_value arguments)
    ltac:(lia)ltac:(rewrite length_map;unfold n in BOUND;lia)
    (handoff_local_object b prefix(handoff_arguments b)592 (handoff_live_owned _ _ _ _ _ PREFIXLIVE)
      ltac:(unfold handoff_objects;cbn;auto 8)))as[copied_memory COPYSTORES].
  assert(COPYLIVE:handoff_live_data cell input b words copied_memory)
    by(eapply handoff_live_table_stores;[exact LAYOUT|exact PREFIXLIVE|left;reflexivity|exact COPYSTORES]).
  assert(COPYTABLES:handoff_tables_frame b before copied_memory).
  { eapply handoff_tables_frame_trans;[exact PREFIXTABLES|]. eapply handoff_tables_scalar;[left;reflexivity|exact COPYSTORES]. }
  destruct(handoff_copy_loop_source_bounded(handoff_locals_env b)prefixle prefix copied_memory
    (handoff_borrowed_source input)(handoff_borrowed_source_offset input)0(handoff_arguments b)arguments
    (Kseq(guest_tail 19(fn_body EntrySource.f_guest))k)failure
    ltac:(apply handoff_nonlocal_binding;cbn;intuition discriminate)
    ltac:(unfold handoff_locals_env;WriteAll.lookup) SOURCESEP POLICYSEP
    (handoff_borrowed_policy_load _ _ _ (handoff_live_borrowed _ _ _ _ _ PREFIXLIVE))
    PREFIXINDEX PREFIXFAILURE ltac:(lia)ltac:(unfold n in BOUND;lia)
    (handoff_borrowed_argument_slots _ _ _ (handoff_live_borrowed _ _ _ _ _ PREFIXLIVE))
    ltac:(change(handoff_pointer_stores(handoff_arguments b)9 prefix(map handoff_argument_value arguments)copied_memory);exact COPYSTORES))
    as[copy_count[copied[COPYBOUND[COPYINDEX[COPYFAILURE COPYPATH]]]]].
  assert(ALLSTORES:handoff_pointer_stores(handoff_arguments b)0 before
    (handoff_prefix_values b preflight mode offset++map handoff_argument_value arguments)copied_memory).
  { eapply handoff_pointer_stores_append;[exact PREFIXSTORES|]. exact COPYSTORES. }
  assert(FIRST:Mem.loadv Mptr copied_memory(Vptr(handoff_arguments b)Ptrofs.zero)=
    Some(Vptr(handoff_symbol EntrySource.___stringlit_111)Ptrofs.zero)).
  { pose proof(handoff_pointer_stores_content _ _ _ _ _ 0%nat
      (Vptr(handoff_symbol EntrySource.___stringlit_111)Ptrofs.zero)ALLSTORES eq_refl)as FIRST.
    exact FIRST. }
  assert(LAST:Mem.loadv Mptr copied_memory
    (Vptr(handoff_borrowed_source input)(Ptrofs.add(handoff_borrowed_source_offset input)(Ptrofs.repr(8*n))))=
    Some(Vlong Int64.zero)).
  { pose proof(handoff_copy_inputs_last _ _ _ _ 0
      (handoff_borrowed_argument_slots _ _ _ (handoff_live_borrowed _ _ _ _ _ COPYLIVE)))as LAST.
    rewrite Z.add_0_l in LAST;exact LAST. }
  destruct(handoff_argument_suffix_source cell input b words copied_memory copied k n
    (handoff_borrowed_source input)(handoff_borrowed_source_offset input) LAYOUT COPYLIVE
    ltac:(rewrite Z.add_0_l in COPYINDEX;exact COPYINDEX) BOUND
    (handoff_borrowed_policy_load _ _ _ (handoff_live_borrowed _ _ _ _ _ COPYLIVE))LAST FIRST)
    as[terminated[after[NULLSTORES[ENVSTORES[AFTER[SUFFIXFRAME SUFFIXPATH]]]]]].
  assert(ALLNULL:handoff_pointer_stores(handoff_arguments b)0 before(handoff_public_arguments b input)terminated).
  { unfold handoff_public_arguments;rewrite app_assoc.
    eapply handoff_pointer_stores_append;[exact ALLSTORES|].
    rewrite length_app,length_map;change(length(handoff_prefix_values b preflight mode offset))with 9%nat.
    rewrite Nat2Z.inj_add;change(Z.of_nat 9)with 9;replace(0+(9+Z.of_nat(length(handoff_borrowed_arguments input))))
      with(9+n)by(unfold n,arguments;lia);exact NULLSTORES. }
  assert(ARGSTABLE:handoff_pointer_table after(handoff_arguments b)(handoff_public_arguments b input)).
  { eapply handoff_pointer_table_other_stores;[| |exact ENVSTORES].
    - eapply handoff_pointer_table_stores;[exact ALLNULL|].
      unfold handoff_public_arguments;rewrite !length_app,length_map.
      change(length(handoff_prefix_values b(handoff_borrowed_preflight input)
        (address_block(handoff_borrowed_mode input))(Ptrofs.repr(address_offset(handoff_borrowed_mode input)))))with 9%nat.
      cbn[length];unfold n,arguments in BOUND;lia.
    - destruct LAYOUT as[DISTINCT _];cbn[handoff_objects map fst]in DISTINCT.
      repeat match goal with N:NoDup(_::_)|-_=>inversion N;clear N;subst end;cbn in *;intuition congruence. }
  assert(FRAME:handoff_tables_frame b before after)
    by(eapply handoff_tables_frame_trans;[exact COPYTABLES|exact SUFFIXFRAME]).
  exists after,(prefix_count+copy_count+1+23)%nat,copied.
  split;[unfold n in BOUND;lia|]. split;[exact AFTER|]. split;[exact FRAME|]. split;[exact ARGSTABLE|]. split.
  - apply handoff_pointer_table_stores with(before:=terminated);[exact ENVSTORES|cbn;lia].
  - split;[exact COPYFAILURE|].
    replace(prefix_count+copy_count+1+23)%nat with(prefix_count+(copy_count+24))%nat by lia.
    eapply store_path_trans with(n:=prefix_count).
    + eapply number_path_implication;[|exact PREFIXPATH].
      intros current CURRENT;eapply Mem.unchanged_on_implies;[exact CURRENT|intros object pos[ARGS ENV]VALID;exact ARGS].
    + eapply store_path_trans with(n:=copy_count).
      * eapply number_path_implication;[|exact COPYPATH].
        intros current[written[rest[VALUES WRITTEN]]].
        eapply handoff_tables_frame_trans;[exact PREFIXTABLES|]. eapply handoff_tables_scalar;[left;reflexivity|exact WRITTEN].
      * eapply store_next;[exact COPYTABLES|apply unchanged_store_edge;WriteAll.structural|].
        eapply number_path_implication;[|exact SUFFIXPATH].
        intros current CURRENT;eapply handoff_tables_frame_trans;[exact COPYTABLES|exact CURRENT].
Qed.
