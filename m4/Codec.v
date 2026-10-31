(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-native.evidence: Actual generated get32 body, arbitrary readable bytes. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events
  Ctypes Ctypesdefs Cop Clight ClightBigstep.
Require Import Slice.
From compcert Require Import Smallstep.
Import ListNotations.
Open Scope Z_scope.

Definition get32_word (a b c d : int) : int :=
  Int.or (Int.or (Int.or (Int.or Int.zero (Int.shl a (Int.repr 0)))
    (Int.shl b (Int.repr 8))) (Int.shl c (Int.repr 16)))
    (Int.shl d (Int.repr 24)).

Ltac expression :=
  first [apply eval_Econst_int
  | eapply eval_Etempvar; repeat first [rewrite PTree.gss | rewrite PTree.gso by discriminate]; first [reflexivity | eassumption]
  | eapply eval_Ebinop; [expression | expression | reflexivity]
  | eapply eval_Ecast; [expression | reflexivity]
  | eapply eval_Elvalue; [eapply eval_Ederef; expression |
      eapply deref_loc_value; [reflexivity |
        cbn;
        match goal with |- context [Ptrofs.mul ?v1 ?v2] =>
          let n := eval vm_compute in (Ptrofs.mul v1 v2) in
          change (Ptrofs.mul v1 v2) with n end; eassumption]] ].

Ltac assignment := eapply exec_Sset; expression.
Ltac sequential := eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
Ltac condition := eapply exec_Sifthenelse; [expression | reflexivity |].
Ltac iteration :=
  eapply exec_Sloop_loop with (t1 := E0) (t2 := E0) (t3 := E0);
  [ sequential; [condition; apply exec_Sskip | sequential; assignment]
  | constructor
  | assignment
  | ].

Theorem get32_body_exec : forall (ge : genv) e le m block ofs a b c d,
  le ! _p = Some (Vptr block ofs) ->
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 0))) = Some (Vint a) ->
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 1))) = Some (Vint b) ->
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 2))) = Some (Vint c) ->
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 3))) = Some (Vint d) ->
  exists le', exec_stmt function_entry2 ge e le m (fn_body f_get32)
    E0 le' m (Out_return (Some (Vint (get32_word a b c d), tuint))).
Proof.
  intros ge e le m block ofs a b c d HP HA HB HC HD.
  unfold f_get32; simpl fn_body.
  eexists.
  sequential; [assignment|].
  sequential.
  - sequential; [assignment|].
    do 4 iteration.
    eapply exec_Sloop_stop1.
    + eapply exec_Sseq_2.
      * condition; apply exec_Sbreak.
      * discriminate.
    + constructor.
  - apply exec_Sreturn_some. expression.
Qed.

Check get32_body_exec.
Print Assumptions get32_body_exec.

Theorem get32_call_exec : forall ge m block ofs a b c d,
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 0))) = Some (Vint a) ->
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 1))) = Some (Vint b) ->
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 2))) = Some (Vint c) ->
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 3))) = Some (Vint d) ->
  eval_funcall function_entry2 ge m (Internal f_get32)
    [Vptr block ofs] E0 m (Vint (get32_word a b c d)).
Proof.
  intros ge m block ofs a b c d HA HB HC HD.
  set (le := PTree.set _p (Vptr block ofs)
     (create_undef_temps (fn_temps f_get32))).
  destruct (get32_body_exec ge empty_env le m block ofs a b c d)
    as [le' BODY]; try assumption.
  { unfold le; apply PTree.gss. }
  eapply eval_funcall_internal with (e := empty_env) (le1 := le)
    (m1 := m) (le2 := le') (m2 := m).
  - constructor.
    + constructor.
    + repeat constructor; simpl; tauto.
    + unfold list_disjoint, var_names, f_get32; simpl.
      intros x y HX HY. simpl in HX, HY.
      destruct HX as [HX|HX]; [subst x|contradiction].
      destruct HY as [HY|[HY|[HY|HY]]]; try contradiction; subst y; discriminate.
    + constructor.
    + reflexivity.
  - exact BODY.
  - split; [discriminate|reflexivity].
  - reflexivity.
Qed.

Theorem get32_smallstep : forall (p : Clight.program) m block ofs a b c d k,
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 0))) = Some (Vint a) ->
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 1))) = Some (Vint b) ->
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 2))) = Some (Vint c) ->
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 3))) = Some (Vint d) ->
  is_call_cont k ->
  star step2 (Clight.globalenv p)
    (Callstate (Internal f_get32) [Vptr block ofs] k m) E0
    (Returnstate (Vint (get32_word a b c d)) k m).
Proof.
  intros. eapply eval_funcall_steps; [|assumption].
  eapply get32_call_exec; eassumption.
Qed.
Check get32_call_exec.
Print Assumptions get32_call_exec.
Check get32_smallstep.
Print Assumptions get32_smallstep.

Theorem get32_ownership_inhabited :
  exists m b,
    Mem.load Mint8unsigned m b 0 = Some (Vint Int.zero) /\
    Mem.load Mint8unsigned m b 1 = Some (Vint Int.zero) /\
    Mem.load Mint8unsigned m b 2 = Some (Vint Int.zero) /\
    Mem.load Mint8unsigned m b 3 = Some (Vint Int.zero).
Proof.
  destruct (Mem.alloc Mem.empty 0 4) as [m b] eqn:ALLOC.
  assert (ACCESS : forall i, 0 <= i < 4 ->
    Mem.valid_access m Mint8unsigned b i Writable).
  { intros i BOUNDS. eapply Mem.valid_access_implies.
    - eapply Mem.valid_access_alloc_same; eauto; simpl; try lia.
      apply Z.divide_1_l.
    - constructor. }
  assert (A0 : Mem.valid_access m Mint8unsigned b 0 Writable).
  { apply ACCESS; lia. }
  destruct (Mem.valid_access_store m Mint8unsigned b 0 (Vint Int.zero) A0) as [m0 S0].
  assert (A1 : Mem.valid_access m0 Mint8unsigned b 1 Writable).
  { eapply Mem.store_valid_access_1; [exact S0|]. apply ACCESS; lia. }
  destruct (Mem.valid_access_store m0 Mint8unsigned b 1 (Vint Int.zero) A1) as [m1 S1].
  assert (A2 : Mem.valid_access m1 Mint8unsigned b 2 Writable).
  { eapply Mem.store_valid_access_1; [exact S1|]. eapply Mem.store_valid_access_1; [exact S0|]. apply ACCESS; lia. }
  destruct (Mem.valid_access_store m1 Mint8unsigned b 2 (Vint Int.zero) A2) as [m2 S2].
  assert (A3 : Mem.valid_access m2 Mint8unsigned b 3 Writable).
  { eapply Mem.store_valid_access_1; [exact S2|]. eapply Mem.store_valid_access_1; [exact S1|]. eapply Mem.store_valid_access_1; [exact S0|]. apply ACCESS; lia. }
  destruct (Mem.valid_access_store m2 Mint8unsigned b 3 (Vint Int.zero) A3) as [m3 S3].
  exists m3, b. repeat split.
  - erewrite Mem.load_store_other by (eauto; simpl; lia). erewrite Mem.load_store_other by (eauto; simpl; lia). erewrite Mem.load_store_other by (eauto; simpl; lia). pose proof (Mem.load_store_same _ _ _ _ _ _ S0) as H. exact H.
  - erewrite Mem.load_store_other by (eauto; simpl; lia). erewrite Mem.load_store_other by (eauto; simpl; lia). pose proof (Mem.load_store_same _ _ _ _ _ _ S1) as H. exact H.
  - erewrite Mem.load_store_other by (eauto; simpl; lia). pose proof (Mem.load_store_same _ _ _ _ _ _ S2) as H. exact H.
  - pose proof (Mem.load_store_same _ _ _ _ _ _ S3) as H. exact H.
Qed.
Check get32_ownership_inhabited.
Print Assumptions get32_ownership_inhabited.

Definition get64_word (a b c d e f g h : int) : int64 :=
  (Int64.or (Int64.or (Int64.or (Int64.or (Int64.or (Int64.or (Int64.or (Int64.or Int64.zero (Int64.shl (Int64.repr (Int.unsigned a)) (Int64.repr 0))) (Int64.shl (Int64.repr (Int.unsigned b)) (Int64.repr 8))) (Int64.shl (Int64.repr (Int.unsigned c)) (Int64.repr 16))) (Int64.shl (Int64.repr (Int.unsigned d)) (Int64.repr 24))) (Int64.shl (Int64.repr (Int.unsigned e)) (Int64.repr 32))) (Int64.shl (Int64.repr (Int.unsigned f)) (Int64.repr 40))) (Int64.shl (Int64.repr (Int.unsigned g)) (Int64.repr 48))) (Int64.shl (Int64.repr (Int.unsigned h)) (Int64.repr 56))).

Theorem get64_body_exec : forall (ge : genv) e le m block ofs a b c d e0 f g h,
  le ! _p = Some (Vptr block ofs) ->
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 0))) = Some (Vint a) ->
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 1))) = Some (Vint b) ->
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 2))) = Some (Vint c) ->
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 3))) = Some (Vint d) ->
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 4))) = Some (Vint e0) ->
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 5))) = Some (Vint f) ->
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 6))) = Some (Vint g) ->
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 7))) = Some (Vint h) ->
  exists le', exec_stmt function_entry2 ge e le m (fn_body f_get64)
    E0 le' m (Out_return (Some (Vlong (get64_word a b c d e0 f g h), tulong))).
Proof.
  intros ge e le m block ofs a b c d e0 f g h HP HA HB HC HD HE HF HG HH.
  unfold f_get64; simpl fn_body.
  eexists.
  sequential; [assignment|].
  sequential.
  - sequential; [assignment|].
    do 8 iteration.
    eapply exec_Sloop_stop1.
    + eapply exec_Sseq_2.
      * condition; apply exec_Sbreak.
      * discriminate.
    + constructor.
  - apply exec_Sreturn_some. expression.
Qed.
Check get64_body_exec.
Print Assumptions get64_body_exec.

Theorem get64_call_exec : forall ge m block ofs a b c d e0 f g h,
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 0))) = Some (Vint a) ->
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 1))) = Some (Vint b) ->
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 2))) = Some (Vint c) ->
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 3))) = Some (Vint d) ->
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 4))) = Some (Vint e0) ->
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 5))) = Some (Vint f) ->
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 6))) = Some (Vint g) ->
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 7))) = Some (Vint h) ->
  eval_funcall function_entry2 ge m (Internal f_get64)
    [Vptr block ofs] E0 m (Vlong (get64_word a b c d e0 f g h)).
Proof.
  intros ge m block ofs a b c d e0 f g h HA HB HC HD HE HF HG HH.
  set (le := PTree.set _p (Vptr block ofs)
     (create_undef_temps (fn_temps f_get64))).
  destruct (get64_body_exec ge empty_env le m block ofs a b c d e0 f g h)
    as [le' BODY]; try assumption.
  { unfold le; apply PTree.gss. }
  eapply eval_funcall_internal with (e := empty_env) (le1 := le)
    (m1 := m) (le2 := le') (m2 := m).
  - constructor.
    + constructor.
    + repeat constructor; simpl; tauto.
    + unfold list_disjoint, var_names, f_get64; simpl.
      intros x y HX HY. simpl in HX, HY.
      destruct HX as [HX|HX]; [subst x|contradiction].
      destruct HY as [HY|[HY|[HY|HY]]]; try contradiction; subst y; discriminate.
    + constructor.
    + reflexivity.
  - exact BODY.
  - split; [discriminate|reflexivity].
  - reflexivity.
Qed.

Theorem get64_smallstep : forall (p : Clight.program) m block ofs a b c d e0 f g h k,
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 0))) = Some (Vint a) ->
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 1))) = Some (Vint b) ->
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 2))) = Some (Vint c) ->
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 3))) = Some (Vint d) ->
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 4))) = Some (Vint e0) ->
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 5))) = Some (Vint f) ->
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 6))) = Some (Vint g) ->
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 7))) = Some (Vint h) ->
  is_call_cont k ->
  star step2 (Clight.globalenv p)
    (Callstate (Internal f_get64) [Vptr block ofs] k m) E0
    (Returnstate (Vlong (get64_word a b c d e0 f g h)) k m).
Proof.
  intros. eapply eval_funcall_steps; [|assumption].
  eapply get64_call_exec; eassumption.
Qed.
Check get64_call_exec.
Print Assumptions get64_call_exec.
Check get64_smallstep.
Print Assumptions get64_smallstep.


Theorem get64_ownership_inhabited : exists m b,
  Mem.load Mint8unsigned m b 0 = Some (Vint Int.zero) /\
  Mem.load Mint8unsigned m b 1 = Some (Vint Int.zero) /\
  Mem.load Mint8unsigned m b 2 = Some (Vint Int.zero) /\
  Mem.load Mint8unsigned m b 3 = Some (Vint Int.zero) /\
  Mem.load Mint8unsigned m b 4 = Some (Vint Int.zero) /\
  Mem.load Mint8unsigned m b 5 = Some (Vint Int.zero) /\
  Mem.load Mint8unsigned m b 6 = Some (Vint Int.zero) /\
  Mem.load Mint8unsigned m b 7 = Some (Vint Int.zero).
Proof.
  destruct (Mem.alloc Mem.empty 0 8) as [m b] eqn:ALLOC.
  assert (ACCESS : forall i, 0 <= i < 8 ->
    Mem.valid_access m Mint8unsigned b i Writable).
  { intros i BOUNDS. eapply Mem.valid_access_implies.
    - eapply Mem.valid_access_alloc_same; eauto; simpl; try lia.
      apply Z.divide_1_l.
    - constructor. }
  assert (A0 : Mem.valid_access m Mint8unsigned b 0 Writable).
  { apply ACCESS; lia. }
  destruct (Mem.valid_access_store m Mint8unsigned b 0 (Vint Int.zero) A0) as [m0 S0].
  assert (A1 : Mem.valid_access m0 Mint8unsigned b 1 Writable).
  { eapply Mem.store_valid_access_1; [exact S0|]. apply ACCESS; lia. }
  destruct (Mem.valid_access_store m0 Mint8unsigned b 1 (Vint Int.zero) A1) as [m1 S1].
  assert (A2 : Mem.valid_access m1 Mint8unsigned b 2 Writable).
  { eapply Mem.store_valid_access_1; [exact S1|]. eapply Mem.store_valid_access_1; [exact S0|]. apply ACCESS; lia. }
  destruct (Mem.valid_access_store m1 Mint8unsigned b 2 (Vint Int.zero) A2) as [m2 S2].
  assert (A3 : Mem.valid_access m2 Mint8unsigned b 3 Writable).
  { eapply Mem.store_valid_access_1; [exact S2|]. eapply Mem.store_valid_access_1; [exact S1|]. eapply Mem.store_valid_access_1; [exact S0|]. apply ACCESS; lia. }
  destruct (Mem.valid_access_store m2 Mint8unsigned b 3 (Vint Int.zero) A3) as [m3 S3].
  assert (A4 : Mem.valid_access m3 Mint8unsigned b 4 Writable).
  { eapply Mem.store_valid_access_1; [exact S3|]. eapply Mem.store_valid_access_1; [exact S2|]. eapply Mem.store_valid_access_1; [exact S1|]. eapply Mem.store_valid_access_1; [exact S0|]. apply ACCESS; lia. }
  destruct (Mem.valid_access_store m3 Mint8unsigned b 4 (Vint Int.zero) A4) as [m4 S4].
  assert (A5 : Mem.valid_access m4 Mint8unsigned b 5 Writable).
  { eapply Mem.store_valid_access_1; [exact S4|]. eapply Mem.store_valid_access_1; [exact S3|]. eapply Mem.store_valid_access_1; [exact S2|]. eapply Mem.store_valid_access_1; [exact S1|]. eapply Mem.store_valid_access_1; [exact S0|]. apply ACCESS; lia. }
  destruct (Mem.valid_access_store m4 Mint8unsigned b 5 (Vint Int.zero) A5) as [m5 S5].
  assert (A6 : Mem.valid_access m5 Mint8unsigned b 6 Writable).
  { eapply Mem.store_valid_access_1; [exact S5|]. eapply Mem.store_valid_access_1; [exact S4|]. eapply Mem.store_valid_access_1; [exact S3|]. eapply Mem.store_valid_access_1; [exact S2|]. eapply Mem.store_valid_access_1; [exact S1|]. eapply Mem.store_valid_access_1; [exact S0|]. apply ACCESS; lia. }
  destruct (Mem.valid_access_store m5 Mint8unsigned b 6 (Vint Int.zero) A6) as [m6 S6].
  assert (A7 : Mem.valid_access m6 Mint8unsigned b 7 Writable).
  { eapply Mem.store_valid_access_1; [exact S6|]. eapply Mem.store_valid_access_1; [exact S5|]. eapply Mem.store_valid_access_1; [exact S4|]. eapply Mem.store_valid_access_1; [exact S3|]. eapply Mem.store_valid_access_1; [exact S2|]. eapply Mem.store_valid_access_1; [exact S1|]. eapply Mem.store_valid_access_1; [exact S0|]. apply ACCESS; lia. }
  destruct (Mem.valid_access_store m6 Mint8unsigned b 7 (Vint Int.zero) A7) as [m7 S7].
  exists m7, b. repeat split.
  - erewrite Mem.load_store_other by (eauto; simpl; lia). erewrite Mem.load_store_other by (eauto; simpl; lia). erewrite Mem.load_store_other by (eauto; simpl; lia). erewrite Mem.load_store_other by (eauto; simpl; lia). erewrite Mem.load_store_other by (eauto; simpl; lia). erewrite Mem.load_store_other by (eauto; simpl; lia). erewrite Mem.load_store_other by (eauto; simpl; lia). exact (Mem.load_store_same _ _ _ _ _ _ S0).
  - erewrite Mem.load_store_other by (eauto; simpl; lia). erewrite Mem.load_store_other by (eauto; simpl; lia). erewrite Mem.load_store_other by (eauto; simpl; lia). erewrite Mem.load_store_other by (eauto; simpl; lia). erewrite Mem.load_store_other by (eauto; simpl; lia). erewrite Mem.load_store_other by (eauto; simpl; lia). exact (Mem.load_store_same _ _ _ _ _ _ S1).
  - erewrite Mem.load_store_other by (eauto; simpl; lia). erewrite Mem.load_store_other by (eauto; simpl; lia). erewrite Mem.load_store_other by (eauto; simpl; lia). erewrite Mem.load_store_other by (eauto; simpl; lia). erewrite Mem.load_store_other by (eauto; simpl; lia). exact (Mem.load_store_same _ _ _ _ _ _ S2).
  - erewrite Mem.load_store_other by (eauto; simpl; lia). erewrite Mem.load_store_other by (eauto; simpl; lia). erewrite Mem.load_store_other by (eauto; simpl; lia). erewrite Mem.load_store_other by (eauto; simpl; lia). exact (Mem.load_store_same _ _ _ _ _ _ S3).
  - erewrite Mem.load_store_other by (eauto; simpl; lia). erewrite Mem.load_store_other by (eauto; simpl; lia). erewrite Mem.load_store_other by (eauto; simpl; lia). exact (Mem.load_store_same _ _ _ _ _ _ S4).
  - erewrite Mem.load_store_other by (eauto; simpl; lia). erewrite Mem.load_store_other by (eauto; simpl; lia). exact (Mem.load_store_same _ _ _ _ _ _ S5).
  - erewrite Mem.load_store_other by (eauto; simpl; lia). exact (Mem.load_store_same _ _ _ _ _ _ S6).
  - exact (Mem.load_store_same _ _ _ _ _ _ S7).
Qed.
Check get64_ownership_inhabited.
Print Assumptions get64_ownership_inhabited.

(* The advertised ownership boundary additionally forbids address-space wrap.
   Each successful Mint8unsigned load establishes readable initialized bytes in
   the same CompCert block; no alignment beyond byte alignment is required. *)
Theorem get32_owned_smallstep : forall (p : Clight.program) m block ofs a b c d k,
  Ptrofs.unsigned ofs + 4 <= Ptrofs.modulus ->
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 0))) = Some (Vint a) ->
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 1))) = Some (Vint b) ->
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 2))) = Some (Vint c) ->
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 3))) = Some (Vint d) ->
  is_call_cont k ->
  star step2 (Clight.globalenv p)
    (Callstate (Internal f_get32) [Vptr block ofs] k m) E0
    (Returnstate (Vint (get32_word a b c d)) k m).
Proof. intros; eapply get32_smallstep; eassumption. Qed.
Check get32_owned_smallstep.
Print Assumptions get32_owned_smallstep.

Theorem get64_owned_smallstep : forall (p : Clight.program) m block ofs a b c d e f g h k,
  Ptrofs.unsigned ofs + 8 <= Ptrofs.modulus ->
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 0))) = Some (Vint a) ->
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 1))) = Some (Vint b) ->
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 2))) = Some (Vint c) ->
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 3))) = Some (Vint d) ->
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 4))) = Some (Vint e) ->
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 5))) = Some (Vint f) ->
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 6))) = Some (Vint g) ->
  Mem.loadv Mint8unsigned m (Vptr block (Ptrofs.add ofs (Ptrofs.repr 7))) = Some (Vint h) ->
  is_call_cont k ->
  star step2 (Clight.globalenv p)
    (Callstate (Internal f_get64) [Vptr block ofs] k m) E0
    (Returnstate (Vlong (get64_word a b c d e f g h)) k m).
Proof. intros; eapply get64_smallstep; eassumption. Qed.
Check get64_owned_smallstep.
Print Assumptions get64_owned_smallstep.

(* Actual generated program definitions, rather than disconnected hand-built ASTs. *)
Theorem get32_in_source_program :
  In (_get32, Gfun (Internal f_get32)) (prog_defs Slice.prog).
Proof.
  change (In (_get32, Gfun (Internal f_get32)) global_definitions).
  unfold global_definitions; repeat first [left; reflexivity | right].
Qed.

Theorem get64_in_source_program :
  In (_get64, Gfun (Internal f_get64)) (prog_defs Slice.prog).
Proof.
  change (In (_get64, Gfun (Internal f_get64)) global_definitions).
  unfold global_definitions; repeat first [left; reflexivity | right].
Qed.
Check get32_in_source_program.
Print Assumptions get32_in_source_program.
Check get64_in_source_program.
Print Assumptions get64_in_source_program.
