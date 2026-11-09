(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: NULL termination and the two environment stores precede the actual exec call. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps ScalarMemory WriteAll.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffStructure NativeHandoffArguments
  NativeHandoffAllocation NativeHandoffInput NativeHandoffMemory NativeHandoffExec.
From LeanCageMainNumber Require Import NumberInitial.
Import ListNotations.
Open Scope Z_scope.
Local Opaque handoff_ge handoff_symbol.

Lemma handoff_scalar_stores_append output before first middle second after :
  scalar_stores output before first middle -> scalar_stores output middle second after ->
  scalar_stores output before(first++second)after.
Proof. intros FIRST;revert after;induction FIRST;intros last SECOND;cbn;[exact SECOND|econstructor;eauto]. Qed.
Lemma handoff_pointer_cells_append index first second :
  handoff_pointer_cells index(first++second)=
    handoff_pointer_cells index first++handoff_pointer_cells(index+Z.of_nat(length first))second.
Proof.
  revert index;induction first as[|value first IH];intros index;cbn[handoff_pointer_cells length app].
  - rewrite Z.add_0_r;reflexivity.
  - rewrite IH;rewrite Nat2Z.inj_succ.
    replace(index+Z.succ(Z.of_nat(length first)))with(index+1+Z.of_nat(length first))by lia;reflexivity.
Qed.
Lemma handoff_pointer_stores_append output index before first middle second after :
  handoff_pointer_stores output index before first middle ->
  handoff_pointer_stores output(index+Z.of_nat(length first))middle second after ->
  handoff_pointer_stores output index before(first++second)after.
Proof.
  intros FIRST SECOND;unfold handoff_pointer_stores in *;rewrite handoff_pointer_cells_append.
  eapply handoff_scalar_stores_append;eassumption.
Qed.

Definition handoff_environment_values :=
  [Vptr(handoff_symbol EntrySource.___stringlit_114)Ptrofs.zero;Vlong Int64.zero].

Lemma handoff_environment_stores_exist b before : handoff_local_owned b before ->
  exists after,handoff_pointer_stores(handoff_environment b)0 before handoff_environment_values after.
Proof.
  intros OWN;apply scalar_stores_exist with(size:=16).
  - apply scalar_list_validb_sound;reflexivity.
  - apply handoff_local_object with(b:=b)(size:=16);[exact OWN|unfold handoff_objects;cbn;auto 8].
Qed.

Lemma handoff_suffix_tail19_actual : guest_tail 19(fn_body EntrySource.f_guest)=
  Ssequence(guest_phase 19)(guest_tail 20(fn_body EntrySource.f_guest)).
Proof. reflexivity. Qed.
Lemma handoff_suffix_tail20_actual : guest_tail 20(fn_body EntrySource.f_guest)=
  Ssequence(guest_phase 20)(guest_tail 21(fn_body EntrySource.f_guest)).
Proof. reflexivity. Qed.
Lemma handoff_suffix_tail21_actual : guest_tail 21(fn_body EntrySource.f_guest)=
  Ssequence(guest_phase 21)(guest_tail 22(fn_body EntrySource.f_guest)).
Proof. reflexivity. Qed.
Lemma handoff_suffix_tail22_actual : guest_tail 22(fn_body EntrySource.f_guest)=
  Ssequence(guest_phase 22)(guest_tail 23(fn_body EntrySource.f_guest)).
Proof. reflexivity. Qed.
Lemma handoff_suffix_tail23_actual : guest_tail 23(fn_body EntrySource.f_guest)=
  Ssequence(guest_phase 23)(guest_tail 24(fn_body EntrySource.f_guest)).
Proof. reflexivity. Qed.

Theorem handoff_argument_suffix_source cell input b words before le k index source offset :
  handoff_private_layout cell input b -> handoff_live_data cell input b words before ->
  le!EntrySource._i__2=Some(Vlong(Int64.repr index)) -> 0<=index<=64 ->
  Mem.loadv Mptr before(Vptr(handoff_symbol EntrySource._policy__1)(Ptrofs.repr 88))=Some(Vptr source offset) ->
  Mem.loadv Mptr before(Vptr source(Ptrofs.add offset(Ptrofs.repr(8*index))))=Some(Vlong Int64.zero) ->
  Mem.loadv Mptr before(Vptr(handoff_arguments b)Ptrofs.zero)=
    Some(Vptr(handoff_symbol EntrySource.___stringlit_111)Ptrofs.zero) ->
  exists terminated after,
    handoff_pointer_stores(handoff_arguments b)(9+index)before[Vlong Int64.zero]terminated /\
    handoff_pointer_stores(handoff_environment b)0 terminated handoff_environment_values after /\
    handoff_live_data cell input b words after /\ handoff_tables_frame b before after /\
    store_path handoff_ge(handoff_tables_frame b before)
      (State EntrySource.f_guest(guest_tail 19(fn_body EntrySource.f_guest))k(handoff_locals_env b)le before)23
      (Callstate entry_exec_definition
        [Vptr(handoff_symbol EntrySource.___stringlit_111)Ptrofs.zero;
         Vptr(handoff_arguments b)Ptrofs.zero;Vptr(handoff_environment b)Ptrofs.zero]
        (handoff_exec_cont(handoff_locals_env b)(handoff_checked_argument_env le source offset)
          (Kseq(guest_tail 24(fn_body EntrySource.f_guest))k))after).
Proof.
  intros LAYOUT LIVE INDEX BOUND POLICY LAST FIRST.
  destruct(handoff_pointer_stores_exist(handoff_arguments b)(9+index)before[Vlong Int64.zero]
    ltac:(lia)ltac:(change(9+index+1<=74);lia)
    (handoff_local_object b before(handoff_arguments b)592 (handoff_live_owned _ _ _ _ _ LIVE)
      ltac:(unfold handoff_objects;cbn;auto 8)))as[terminated NULLSTORES].
  assert(TERMINATED:handoff_live_data cell input b words terminated)
    by(eapply handoff_live_table_stores;[exact LAYOUT|exact LIVE|left;reflexivity|exact NULLSTORES]).
  destruct(handoff_environment_stores_exist b terminated(handoff_live_owned _ _ _ _ _ TERMINATED))as[after ENVSTORES].
  assert(AFTER:handoff_live_data cell input b words after)
    by(eapply handoff_live_table_stores;[exact LAYOUT|exact TERMINATED|right;reflexivity|exact ENVSTORES]).
  pose proof NULLSTORES as NS;cbn[handoff_pointer_stores handoff_pointer_cells]in NS.
  inversion NS as[|? ? ? middle ? NULLSTORE TAIL];subst;inversion TAIL;subst middle.
  pose proof ENVSTORES as ES;cbn[handoff_pointer_stores handoff_pointer_cells handoff_environment_values]in ES.
  inversion ES as[|? ? ? environment_one ? ENVVALUE TAILONE];subst.
  inversion TAILONE as[|? ? ? environment_two ? ENVNULL TAILTWO];subst;inversion TAILTWO;subst.
  change(Mem.store Mptr before(handoff_arguments b)(8*(9+index))(Vlong Int64.zero)=Some terminated)in NULLSTORE.
  change(Mem.store Mptr terminated(handoff_environment b)0(Vptr(handoff_symbol EntrySource.___stringlit_114)Ptrofs.zero)=Some environment_one)in ENVVALUE.
  change(Mem.store Mptr environment_one(handoff_environment b)8(Vlong Int64.zero)=Some after)in ENVNULL.
  assert(ARGSENV:handoff_arguments b<>handoff_environment b).
  { destruct LAYOUT as[DISTINCT _];cbn[handoff_objects map fst]in DISTINCT.
    repeat match goal with N:NoDup(_::_)|-_=>inversion N;clear N;subst end;cbn in *;intuition congruence. }
  assert(FIRSTTERM:Mem.loadv Mptr terminated(Vptr(handoff_arguments b)Ptrofs.zero)=
    Some(Vptr(handoff_symbol EntrySource.___stringlit_111)Ptrofs.zero)).
  { change(Mem.load Mptr terminated(handoff_arguments b)0=Some(Vptr(handoff_symbol EntrySource.___stringlit_111)Ptrofs.zero)).
    rewrite(Mem.load_store_other _ _ _ _ _ _ NULLSTORE).
    - exact FIRST.
    - right;left;change(0+8<=8*(9+index));lia. }
  assert(FIRSTAFTER:Mem.loadv Mptr after(Vptr(handoff_arguments b)Ptrofs.zero)=
    Some(Vptr(handoff_symbol EntrySource.___stringlit_111)Ptrofs.zero)).
  { rewrite(handoff_pointer_stores_load_other _ _ _ _ _ _ _ _ ENVSTORES ARGSENV);exact FIRSTTERM. }
  assert(F0:handoff_tables_frame b before before)by apply handoff_tables_frame_refl.
  assert(FT:handoff_tables_frame b before terminated).
  { eapply handoff_tables_scalar;[left;reflexivity|exact NULLSTORES]. }
  assert(F1:handoff_tables_frame b before environment_one).
  { eapply handoff_tables_frame_trans;[exact FT|].
    eapply Mem.store_unchanged_on;[exact ENVVALUE|].
    intros pos RANGE[ARGS ENV];exact(ENV eq_refl). }
  assert(F2:handoff_tables_frame b before after).
  { eapply handoff_tables_frame_trans;[exact FT|]. eapply handoff_tables_scalar;[right;reflexivity|exact ENVSTORES]. }
  exists terminated,after;split;[exact NULLSTORES|]. split;[exact ENVSTORES|]. split;[exact AFTER|]. split;[exact F2|].
  rewrite handoff_suffix_tail19_actual at 1.
  eapply store_next;[exact F0|apply unchanged_store_edge;WriteAll.structural|].
  eapply store_path_trans with(n:=7%nat).
  - eapply number_path_implication with(P:=fun current=>current=before);[intros current SAME;subst;exact F0|].
    apply handoff_final_argument_check_source with(source:=source)(offset:=offset)(index:=index).
    + apply handoff_nonlocal_binding;cbn;intuition discriminate.
    + exact POLICY.
    + exact INDEX.
    + exact BOUND.
    + exact LAST.
  - eapply store_next;[exact F0|apply unchanged_store_edge;WriteAll.structural|].
    rewrite handoff_suffix_tail20_actual at 1.
    eapply store_next;[exact F0|apply unchanged_store_edge;WriteAll.structural|].
    eapply store_path_trans with(n:=1%nat).
    + eapply number_path_implication with(P:=fun current=>current=before \/ current=terminated).
      * intros current[SAME|SAME];subst;assumption.
      * apply handoff_argument_terminator_source with(output:=handoff_arguments b)(index:=index).
        -- unfold handoff_locals_env;WriteAll.lookup.
        -- unfold handoff_checked_argument_env;rewrite !PTree.gso by discriminate;exact INDEX.
        -- exact BOUND.
        -- exact NULLSTORE.
    + eapply store_next;[exact FT|apply unchanged_store_edge;WriteAll.structural|].
      rewrite handoff_suffix_tail21_actual at 1.
      eapply store_next;[exact FT|apply unchanged_store_edge;WriteAll.structural|].
      eapply store_path_trans with(n:=1%nat).
      * eapply number_path_implication with(P:=fun current=>current=terminated \/ current=environment_one).
        -- intros current[SAME|SAME];subst;assumption.
        -- apply handoff_environment_value_source with(environment:=handoff_environment b).
           ++ unfold handoff_locals_env;WriteAll.lookup.
           ++ apply handoff_nonlocal_binding;cbn;intuition discriminate.
           ++ exact ENVVALUE.
      * eapply store_next;[exact F1|apply unchanged_store_edge;WriteAll.structural|].
        rewrite handoff_suffix_tail22_actual at 1.
        eapply store_next;[exact F1|apply unchanged_store_edge;WriteAll.structural|].
        eapply store_path_trans with(n:=1%nat).
        -- eapply number_path_implication with(P:=fun current=>current=environment_one \/ current=after).
           ++ intros current[SAME|SAME];subst;assumption.
           ++ apply handoff_environment_terminator_source with(environment:=handoff_environment b).
              ** unfold handoff_locals_env;WriteAll.lookup.
              ** exact ENVNULL.
        -- eapply store_next;[exact F2|apply unchanged_store_edge;WriteAll.structural|].
           rewrite handoff_suffix_tail23_actual at 1.
           eapply store_next;[exact F2|apply unchanged_store_edge;WriteAll.structural|].
           eapply number_path_implication with(P:=fun current=>current=after);[intros current SAME;subst;exact F2|].
           apply handoff_entry_exec_source.
           ++ unfold handoff_locals_env;WriteAll.lookup.
           ++ unfold handoff_locals_env;WriteAll.lookup.
           ++ apply handoff_nonlocal_binding;cbn;intuition discriminate.
           ++ exact FIRSTAFTER.
Qed.
