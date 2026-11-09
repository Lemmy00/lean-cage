(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.pid: Actual bounded PID bytes and readback determine the cgroup command. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs
  Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll ScalarMemory.
From EntryNative Require Import EntrySource NativeArguments NativeHandoffMachine HandoffRegion
  NativeHandoffArguments NativeHandoffNumeric NativeHandoffFormat NativeHandoffNumberBound.
From EntryProcess Require Import ProcessAllocation ProcessStructure.
From LeanCageMainNumber Require Import NumberMath NumberMemory NumberStorage NumberControl
  NumberInitial NumberSource NumberWords.
Import ListNotations.
Open Scope Z_scope.

Lemma admission_numeric_guards_actual :
  admission_positive_length = Sifthenelse
    (Ebinop Ole (Etempvar _pidlength tint) (Econst_int Int.zero tint) tint) admission_failure Sskip /\
  admission_bounded_length = Sifthenelse
    (Ebinop Oge (Ecast (Etempvar _pidlength tint) tulong)
      (Esizeof (tarray tschar 32) tulong) tint) admission_failure Sskip /\
  admission_leading_digit = Ssequence
    (Sset _t'9 (Ederef (Ebinop Oadd (Evar _pidtext (tarray tschar 32))
      (Econst_int Int.zero tint) (tptr tschar)) tschar))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'9 tschar)
      (Econst_int (Int.repr 48) tint) tint) admission_failure Sskip) /\
  admission_number = Ssequence
    (Scall (Some _t'5) (Evar _number (Tfunction [tptr tschar;tptr tulong] tint cc_default))
      [Evar _pidtext (tarray tschar 32);Eaddrof (Evar _encoded_pid tulong) (tptr tulong)])
    (Sifthenelse (Etempvar _t'5 tint) admission_failure Sskip) /\
  admission_pid_equal = Ssequence (Sset _t'8 (Evar _encoded_pid tulong))
    (Sifthenelse (Ebinop One (Etempvar _t'8 tulong)
      (Ecast (Etempvar _child tint) tulong) tint) admission_failure Sskip).
Proof. repeat split; reflexivity. Qed.

Theorem admission_positive_length_source locals le m count k :
  le!_pidlength = Some (Vint count) ->
  store_path admission_ge (fun after=>after=m)
    (State f_admit_child admission_positive_length k (admission_env locals) le m) 1
    (State f_admit_child (if Int.signed count <=? 0 then admission_failure else Sskip)
      k (admission_env locals) le m).
Proof.
  intros COUNT; rewrite (proj1 admission_numeric_guards_actual).
  eapply store_next; [reflexivity|apply certified_if_edge with
    (v:=Val.of_bool (Int.signed count <=? 0)) (b:=Int.signed count <=? 0)|].
  - eapply binary_expression_value.
    + apply old_expression_value,value_temp; exact COUNT.
    + apply old_expression_value,value_int.
    + apply handoff_count_lower.
  - apply number_bool_value.
  - apply store_done; reflexivity.
Qed.

Definition admission_numeric_memory encoded before after :=
  Mem.unchanged_on (fun object _=>object<>encoded) before after /\
  forall object position kind permission,
    Mem.perm after object position kind permission <-> Mem.perm before object position kind permission.

Lemma admission_numeric_memory_refl encoded before : admission_numeric_memory encoded before before.
Proof. split; [apply Mem.unchanged_on_refl|intros; reflexivity]. Qed.

Lemma admission_numeric_memory_post before after encoded parsed :
  number_memory before encoded Ptrofs.zero parsed after ->
  admission_numeric_memory encoded before after.
Proof.
  intros [SAME|POST]; [subst; apply admission_numeric_memory_refl|].
  destruct parsed as [value|]; [|cbn [number_post] in POST; subst; apply admission_numeric_memory_refl].
  unfold number_post,Mem.storev in POST; destruct (zle _ _); [|discriminate].
  split.
  - eapply Mem.store_unchanged_on; [exact POST|].
    intros position RANGE DIFFERENT; exact (DIFFERENT eq_refl).
  - intros; split; [eapply Mem.perm_store_2|eapply Mem.perm_store_1]; eassumption.
Qed.

Lemma admission_numeric_input_preserved before after encoded text bytes :
  admission_numeric_memory encoded before after -> text<>encoded ->
  number_input before text Ptrofs.zero bytes -> number_input after text Ptrofs.zero bytes.
Proof.
  intros [FRAME PERMISSIONS] SEPARATE [BOUND [NONZERO LOAD]].
  split; [exact BOUND|]. split; [exact NONZERO|].
  eapply Mem.loadbytes_unchanged_on; [exact FRAME| |exact LOAD].
  intros; exact SEPARATE.
Qed.

Lemma admission_numeric_post_load before after encoded value :
  number_post before encoded Ptrofs.zero (Some value) after ->
  Mem.loadv Mint64 after (Vptr encoded Ptrofs.zero)=Some(Vlong(Int64.repr value)).
Proof.
  unfold number_post,Mem.storev,Mem.loadv; destruct (zle _ _); [|discriminate].
  intros STORE; rewrite (Mem.load_store_same _ _ _ _ _ _ STORE); reflexivity.
Qed.

Definition admission_temp_frame (before after : temp_env) :=
  forall id, ~In id [_t'9;_t'5;_t'8] -> after!id=before!id.

Lemma admission_temp_frame_refl le : admission_temp_frame le le.
Proof. intros id ABSENT; reflexivity. Qed.

Lemma admission_temp_frame_set before after id value :
  admission_temp_frame before after -> In id [_t'9;_t'5;_t'8] ->
  admission_temp_frame before (PTree.set id value after).
Proof.
  intros FRAME PRESENT chosen ABSENT; rewrite PTree.gso by (intro SAME; subst; contradiction).
  apply FRAME; exact ABSENT.
Qed.

Definition admission_numeric_leaf locals before original child count k state :=
  (exists after le continuation,
    state=State f_admit_child admission_failure continuation (admission_env locals) le after /\
    call_cont continuation=call_cont k /\
    admission_temp_frame original le) \/
  (exists after le bytes first rest,
    state=State f_admit_child (admission_tail 10 (fn_body f_admit_child)) k
      (admission_env locals) le after /\
    admission_temp_frame original le /\
    Z.of_nat(length bytes)=Int.signed count /\ 0<Int.signed count<32 /\ bytes=first::rest /\
    first<>Byte.repr 48 /\ Forall decimal_digit_ok bytes /\
    decimal_number bytes=Some(Int.signed child) /\
    number_input after (admission_text locals) Ptrofs.zero bytes /\
    number_post before (admission_encoded locals) Ptrofs.zero (Some(Int.signed child)) after).

Definition admission_path (P:mem->Prop) (R:Clight.state->Prop) budget start :=
  exists count last, store_path admission_ge P start count last /\ (count<=budget)%nat /\ R last.

Lemma admission_path_stop P R budget state :
  P(memory_of state) -> R state -> admission_path P R budget state.
Proof. intros MEMORY RESULT; exists 0%nat,state; split; [constructor; exact MEMORY|]. split; [lia|exact RESULT]. Qed.

Lemma admission_path_weaken P R budget start larger :
  admission_path P R budget start -> (budget<=larger)%nat -> admission_path P R larger start.
Proof.
  intros [count [last [PATH [BOUND RESULT]]]] LARGER.
  exists count,last; split; [exact PATH|]. split; [lia|exact RESULT].
Qed.

Lemma admission_path_prepend P R count start next budget :
  store_path admission_ge P start count next -> admission_path P R budget next ->
  admission_path P R (count+budget) start.
Proof.
  intros PATH [extra [last [TAIL [BOUND RESULT]]]].
  exists (count+extra)%nat,last; split; [eapply store_path_trans; eassumption|]. split; [lia|exact RESULT].
Qed.

Lemma admission_path_edge P R start next budget :
  P(memory_of start) -> store_edge admission_ge start next -> admission_path P R budget next ->
  admission_path P R (S budget) start.
Proof.
  intros MEMORY EDGE [count [last [PATH [BOUND RESULT]]]].
  exists (S count),last; split; [econstructor; eassumption|]. split; [lia|exact RESULT].
Qed.

Theorem admission_bounded_length_source locals le m count k :
  le!_pidlength = Some (Vint count) -> 0 < Int.signed count ->
  store_path admission_ge (fun after=>after=m)
    (State f_admit_child admission_bounded_length k (admission_env locals) le m) 1
    (State f_admit_child (if 32 <=? Int.signed count then admission_failure else Sskip)
      k (admission_env locals) le m).
Proof.
  intros COUNT POSITIVE; rewrite (proj1 (proj2 admission_numeric_guards_actual)).
  eapply store_next; [reflexivity|apply certified_if_edge with
    (v:=Val.of_bool (32 <=? Int.signed count)) (b:=32 <=? Int.signed count)|].
  - eapply binary_expression_value.
    + eapply cast_expression_value; [apply old_expression_value,value_temp; exact COUNT|reflexivity].
    + apply handoff_size32_value.
    + apply handoff_count_upper. pose proof (Int.signed_range count).
      change Int.max_signed with 2147483647 in H.
      change Int64.max_unsigned with 18446744073709551615; lia.
  - apply number_bool_value.
  - apply store_done; reflexivity.
Qed.

Definition admission_leading_word byte := Int.sign_ext 8 (Int.repr (Byte.unsigned byte)).
Definition admission_leading_zero byte := Int.eq (admission_leading_word byte) (Int.repr 48).

Theorem admission_leading_digit_source locals le m byte rest k :
  number_input m (admission_text locals) Ptrofs.zero (byte::rest) ->
  store_path admission_ge (fun after=>after=m)
    (State f_admit_child admission_leading_digit k (admission_env locals) le m) 4
    (State f_admit_child (if admission_leading_zero byte then admission_failure else Sskip)
      k (admission_env locals) (PTree.set _t'9 (Vint (admission_leading_word byte)) le) m).
Proof.
  intros INPUT.
  rewrite (proj1 (proj2 (proj2 admission_numeric_guards_actual))).
  destruct (number_read_head _ _ _ _ _ _ INPUT eq_refl) as [UNSIGNED SIGNED].
  handoff_route; handoff_set.
  - eapply location_read_value.
    + apply pointer_location_value; eapply binary_expression_value.
      * apply handoff_array_value; apply (proj1 (admission_local_bindings locals)).
      * apply old_expression_value,value_int.
      * reflexivity.
    + eapply deref_loc_value; [reflexivity|exact SIGNED].
  - handoff_route; eapply store_next; [reflexivity|apply certified_if_edge with
      (v:=Val.of_bool (admission_leading_zero byte)) (b:=admission_leading_zero byte)|].
    + eapply binary_expression_value.
      * apply old_expression_value,value_temp; apply PTree.gss.
      * apply old_expression_value,value_int.
      * reflexivity.
    + apply number_bool_value.
    + apply store_done; reflexivity.
Qed.

Definition admission_number_cont locals le k :=
  Kcall (Some _t'5) f_admit_child (admission_env locals) le
    (Kseq (Sifthenelse (Etempvar _t'5 tint) admission_failure Sskip) k).

Theorem admission_number_call_source locals le m k :
  store_path admission_ge (fun after=>after=m)
    (State f_admit_child admission_number k (admission_env locals) le m) 2
    (Callstate (Internal f_number)
      [Vptr (admission_text locals) Ptrofs.zero;Vptr (admission_encoded locals) Ptrofs.zero]
      (admission_number_cont locals le k) m).
Proof.
  rewrite (proj1 (proj2 (proj2 (proj2 admission_numeric_guards_actual)))).
  unfold admission_number_cont; handoff_route.
  eapply store_next; [reflexivity| |].
  - eapply certified_call_edge.
    + reflexivity.
    + apply old_expression_value; eapply value_function.
      * apply admission_nonlocal_binding; discriminate.
      * exact (proj1 handoff_number_binding).
      * reflexivity.
    + eapply cons_argument_values.
      * apply handoff_array_value; apply (proj1 (admission_local_bindings locals)).
      * reflexivity.
      * eapply cons_argument_values.
        -- apply LeanCageMain.MainValues.main_address_value,local_location_value.
           apply (proj2 (admission_local_bindings locals)).
        -- reflexivity.
        -- apply no_argument_values.
    + exact (proj2 handoff_number_binding).
    + reflexivity.
  - apply store_done; reflexivity.
Qed.

Theorem admission_number_return_source locals le m k parsed :
  store_path admission_ge (fun after=>after=m)
    (Returnstate (number_code parsed) (admission_number_cont locals le k) m) 3
    (State f_admit_child (match parsed with None=>admission_failure|Some _=>Sskip end)
      k (admission_env locals) (PTree.set _t'5 (number_code parsed) le) m).
Proof.
  unfold admission_number_cont; destruct parsed; cbn [number_code].
  - handoff_route; handoff_route.
    eapply store_next; [reflexivity|apply certified_if_edge with (v:=Vint Int.zero) (b:=false)|].
    + apply old_expression_value,value_temp; apply PTree.gss.
    + reflexivity.
    + apply store_done; reflexivity.
  - handoff_route; handoff_route.
    eapply store_next; [reflexivity|apply certified_if_edge with (v:=Vint Int.mone) (b:=true)|].
    + apply old_expression_value,value_temp; apply PTree.gss.
    + reflexivity.
    + apply store_done; reflexivity.
Qed.

Theorem admission_pid_equal_source locals le m value child k :
  le!_child = Some (Vint child) -> 0 <= Int.signed child ->
  0 <= value <= Int64.max_unsigned ->
  Mem.loadv Mint64 m (Vptr (admission_encoded locals) Ptrofs.zero) = Some (Vlong (Int64.repr value)) ->
  store_path admission_ge (fun after=>after=m)
    (State f_admit_child admission_pid_equal k (admission_env locals) le m) 4
    (State f_admit_child (if value =? Int.signed child then Sskip else admission_failure)
      k (admission_env locals) (PTree.set _t'8 (Vlong (Int64.repr value)) le) m).
Proof.
  intros CHILD POSITIVE RANGE LOAD; rewrite (proj2 (proj2 (proj2 (proj2 admission_numeric_guards_actual)))).
  replace (if value =? Int.signed child then Sskip else admission_failure)
    with (if negb (value =? Int.signed child) then admission_failure else Sskip)
    by (destruct (value =? Int.signed child); reflexivity).
  handoff_route; handoff_set.
  - eapply location_read_value; [apply local_location_value; apply (proj2 (admission_local_bindings locals))|].
    eapply deref_loc_value; [reflexivity|exact LOAD].
  - handoff_route; eapply store_next; [reflexivity|apply certified_if_edge with
      (v:=Val.of_bool (negb (value =? Int.signed child))) (b:=negb (value =? Int.signed child))|].
    + eapply binary_expression_value.
      * apply old_expression_value,value_temp; apply PTree.gss.
      * eapply cast_expression_value.
        -- apply old_expression_value,value_temp; rewrite PTree.gso by discriminate; exact CHILD.
        -- reflexivity.
      * apply handoff_numeric_compare_long; [exact RANGE|].
        pose proof (Int.signed_range child); change Int.max_signed with 2147483647 in H.
        change Int64.max_unsigned with 18446744073709551615; lia.
    + apply number_bool_value.
    + apply store_done; reflexivity.
Qed.

Lemma admission_leading_checked byte : admission_leading_zero byte=false -> byte<>Byte.repr 48.
Proof. intros ZERO SAME; subst; vm_compute in ZERO; discriminate. Qed.

Lemma admission_numeric_tail7_actual : admission_tail 7 (fn_body f_admit_child)=
  Ssequence admission_leading_digit (admission_tail 8 (fn_body f_admit_child)).
Proof. reflexivity. Qed.
Lemma admission_numeric_tail8_actual : admission_tail 8 (fn_body f_admit_child)=
  Ssequence admission_number (admission_tail 9 (fn_body f_admit_child)).
Proof. reflexivity. Qed.
Lemma admission_numeric_tail9_actual : admission_tail 9 (fn_body f_admit_child)=
  Ssequence admission_pid_equal (admission_tail 10 (fn_body f_admit_child)).
Proof. reflexivity. Qed.

Theorem admission_numeric_bytes_path locals before original child count bytes k :
  original!_child=Some(Vint child) -> 0<=Int.signed child ->
  Z.of_nat(length bytes)=Int.signed count -> 0<Int.signed count<32 ->
  number_input before (admission_text locals) Ptrofs.zero bytes ->
  number_output before (admission_encoded locals) Ptrofs.zero ->
  admission_text locals<>admission_encoded locals ->
  admission_path (admission_numeric_memory (admission_encoded locals) before)
    (admission_numeric_leaf locals before original child count k) 3300
    (State f_admit_child (admission_tail 7 (fn_body f_admit_child))
      k (admission_env locals) original before).
Proof.
  intros CHILD POSITIVE LENGTH EXTENT INPUT OUTPUT SEPARATE.
  destruct bytes as [|first rest]; [cbn in LENGTH; lia|].
  set (P:=admission_numeric_memory (admission_encoded locals) before).
  set (R:=admission_numeric_leaf locals before original child count k).
  assert (P0:P before) by apply admission_numeric_memory_refl.
  set (leading:=PTree.set _t'9 (Vint(admission_leading_word first)) original).
  assert (LEADING:admission_temp_frame original leading).
  { apply admission_temp_frame_set; [apply admission_temp_frame_refl|cbn; auto]. }
  rewrite admission_numeric_tail7_actual at 1.
  eapply admission_path_edge; [exact P0|apply unchanged_store_edge; WriteAll.structural|].
  eapply admission_path_prepend with (count:=4%nat) (budget:=3295%nat).
  - eapply number_path_implication with (P:=fun current=>current=before).
    + intros current SAME; subst; exact P0.
    + apply admission_leading_digit_source with (rest:=rest); exact INPUT.
  - destruct (admission_leading_zero first) eqn:ZERO.
    + apply admission_path_stop; [exact P0|].
      left; eexists; eexists; eexists; split; [reflexivity|]. split; [reflexivity|exact LEADING].
    + eapply admission_path_edge; [exact P0|apply unchanged_store_edge; WriteAll.structural|].
      rewrite admission_numeric_tail8_actual at 1.
      eapply admission_path_edge; [exact P0|apply unchanged_store_edge; WriteAll.structural|].
      eapply admission_path_prepend with (count:=2%nat) (budget:=3291%nat).
      * eapply number_path_implication with (P:=fun current=>current=before).
        -- intros current SAME; subst; exact P0.
        -- apply admission_number_call_source.
      * destruct (handoff_number_source_bound admission_ge before (admission_text locals) Ptrofs.zero
          (first::rest) (admission_encoded locals) Ptrofs.zero
          (admission_number_cont locals leading
            (Kseq (admission_tail 9 (fn_body f_admit_child)) k)) INPUT OUTPUT)
          as [number_count [after [BOUND [POST PARSE]]]].
        assert (P1:P after).
        { eapply admission_numeric_memory_post; right; exact POST. }
        assert (NUMBER_BOUND:(number_count+20<=3291)%nat).
        { assert (LEN:(length(first::rest)<=31)%nat) by lia; lia. }
        eapply admission_path_weaken with (budget:=(number_count+20)%nat); [|exact NUMBER_BOUND].
        eapply admission_path_prepend with (count:=number_count) (budget:=20%nat).
        -- eapply number_path_implication with
             (P:=number_memory before (admission_encoded locals) Ptrofs.zero (decimal_number (first::rest))).
           ++ intros current MEMORY; eapply admission_numeric_memory_post; exact MEMORY.
           ++ rewrite current_entry_number_exact.
              exact PARSE.
        -- set (numbered:=PTree.set _t'5 (number_code(decimal_number(first::rest))) leading).
           assert (NUMBERED:admission_temp_frame original numbered).
           { apply admission_temp_frame_set; [exact LEADING|cbn; auto]. }
           eapply admission_path_prepend with (count:=3%nat) (budget:=17%nat).
           ++ eapply number_path_implication with (P:=fun current=>current=after).
              ** intros current SAME; subst; exact P1.
              ** apply admission_number_return_source.
           ++ destruct (decimal_number(first::rest)) as [value|] eqn:PARSED.
              ** eapply admission_path_edge; [exact P1|apply unchanged_store_edge; WriteAll.structural|].
                 rewrite admission_numeric_tail9_actual at 1.
                 eapply admission_path_edge; [exact P1|apply unchanged_store_edge; WriteAll.structural|].
                 destruct (proj1 (decimal_number_exact (first::rest) value) PARSED)
                   as [NONEMPTY [DIGITS [VALUE RANGE]]].
                 eapply admission_path_prepend with (count:=4%nat) (budget:=11%nat).
                 --- eapply number_path_implication with (P:=fun current=>current=after).
                     +++ intros current SAME; subst; exact P1.
                     +++ apply admission_pid_equal_source.
                         *** unfold numbered,leading; rewrite !PTree.gso by discriminate; exact CHILD.
                         *** exact POSITIVE.
                         *** exact RANGE.
                         *** eapply admission_numeric_post_load; exact POST.
                 --- set (compared:=PTree.set _t'8 (Vlong(Int64.repr value)) numbered).
                     assert (COMPARED:admission_temp_frame original compared).
                     { apply admission_temp_frame_set; [exact NUMBERED|cbn; auto]. }
                     destruct (value =? Int.signed child) eqn:EQUAL.
                     +++ eapply admission_path_edge; [exact P1|apply unchanged_store_edge; WriteAll.structural|].
                         apply admission_path_stop; [exact P1|].
                         right; exists after,compared,(first::rest),first,rest.
                         split; [reflexivity|]. split; [exact COMPARED|].
                         split; [exact LENGTH|]. split; [exact EXTENT|]. split; [reflexivity|].
                         split; [apply admission_leading_checked; exact ZERO|].
                         split; [exact DIGITS|]. apply Z.eqb_eq in EQUAL.
                         split; [rewrite <-EQUAL; exact PARSED|]. split.
                         *** eapply admission_numeric_input_preserved; eassumption.
                         *** rewrite <-EQUAL; exact POST.
                     +++ apply admission_path_stop; [exact P1|].
                         left; eexists; eexists; eexists; split; [reflexivity|].
                         split; [reflexivity|exact COMPARED].
              ** apply admission_path_stop; [exact P1|].
                 left; eexists; eexists; eexists; split; [reflexivity|]. split; [reflexivity|exact NUMBERED].
Qed.

Lemma admission_numeric_tail5_actual : admission_tail 5 (fn_body f_admit_child)=
  Ssequence admission_positive_length (admission_tail 6 (fn_body f_admit_child)).
Proof. reflexivity. Qed.
Lemma admission_numeric_tail6_actual : admission_tail 6 (fn_body f_admit_child)=
  Ssequence admission_bounded_length (admission_tail 7 (fn_body f_admit_child)).
Proof. reflexivity. Qed.

Theorem admission_numeric_source cell locals formatting_before before original child count k :
  original!_child=Some(Vint child) -> 0<=Int.signed child ->
  original!_pidlength=Some(Vint count) ->
  entry_format_result cell formatting_before (admission_text locals) Ptrofs.zero count before ->
  number_output before (admission_encoded locals) Ptrofs.zero ->
  admission_text locals<>admission_encoded locals ->
  admission_path (admission_numeric_memory (admission_encoded locals) before)
    (admission_numeric_leaf locals before original child count k) 3400
    (State f_admit_child (admission_tail 5 (fn_body f_admit_child))
      k (admission_env locals) original before).
Proof.
  intros CHILD POSITIVE COUNT FORMATTED OUTPUT SEPARATE.
  assert (P0:admission_numeric_memory (admission_encoded locals) before before)
    by apply admission_numeric_memory_refl.
  rewrite admission_numeric_tail5_actual at 1.
  eapply admission_path_edge; [exact P0|apply unchanged_store_edge; WriteAll.structural|].
  eapply admission_path_prepend with (count:=1%nat) (budget:=3398%nat).
  - eapply number_path_implication with (P:=fun current=>current=before).
    + intros current SAME; subst; exact P0.
    + apply admission_positive_length_source; exact COUNT.
  - destruct (Int.signed count <=? 0) eqn:LOW.
    + apply admission_path_stop; [exact P0|].
      left; eexists; eexists; eexists; split; [reflexivity|]. split; [reflexivity|apply admission_temp_frame_refl].
    + apply Z.leb_gt in LOW.
      eapply admission_path_edge; [exact P0|apply unchanged_store_edge; WriteAll.structural|].
      rewrite admission_numeric_tail6_actual at 1.
      eapply admission_path_edge; [exact P0|apply unchanged_store_edge; WriteAll.structural|].
      eapply admission_path_prepend with (count:=1%nat) (budget:=3395%nat).
      * eapply number_path_implication with (P:=fun current=>current=before).
        -- intros current SAME; subst; exact P0.
        -- apply admission_bounded_length_source; [exact COUNT|exact LOW].
      * destruct (32 <=? Int.signed count) eqn:HIGH.
        -- apply admission_path_stop; [exact P0|].
           left; eexists; eexists; eexists; split; [reflexivity|]. split; [reflexivity|apply admission_temp_frame_refl].
        -- apply Z.leb_gt in HIGH.
           assert (EXTENT:0<Int.signed count<32) by lia.
           destruct (entry_format_string _ _ _ _ _ _ FORMATTED EXTENT) as [bytes [LENGTH INPUT]].
           eapply admission_path_edge; [exact P0|apply unchanged_store_edge; WriteAll.structural|].
           eapply admission_path_weaken with (budget:=3300%nat); [|lia].
           eapply admission_numeric_bytes_path; eassumption.
Qed.

Definition admission_format_cont locals le k :=
  Kcall (Some _t'4) f_admit_child (admission_env locals) le
    (Kseq (Sset _pidlength (Etempvar _t'4 tint))
      (Kseq (admission_tail 5 (fn_body f_admit_child)) k)).

Definition admission_format_returned le count :=
  PTree.set _pidlength (Vint count) (PTree.set _t'4 (Vint count) le).

Theorem admission_format_return_source locals le before count k :
  store_path admission_ge (fun after=>after=before)
    (Returnstate (Vint count) (admission_format_cont locals le k) before) 4
    (State f_admit_child (admission_tail 5 (fn_body f_admit_child))
      k (admission_env locals) (admission_format_returned le count) before).
Proof.
  unfold admission_format_cont,admission_format_returned.
  handoff_route; handoff_route; handoff_set.
  - apply old_expression_value,value_temp; apply PTree.gss.
  - handoff_route; apply store_done; reflexivity.
Qed.
