(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Checked formatter extents either continue or enter the actual failure callee. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs
  Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll ErrorNumber.
From EntryNative Require Import EntrySource NativeHandoffMachine HandoffRegion NativeHandoffError
  NativeHandoffArguments NativeHandoffNumeric NativeHandoffFormat.
From LeanCageMainNumber Require Import NumberControl NumberInitial.
Import ListNotations.
Open Scope Z_scope.

Lemma handoff_failure_binding :
  Genv.find_symbol handoff_ge _fail_child=Some(handoff_symbol _fail_child) /\
  Genv.find_funct handoff_ge (Vptr(handoff_symbol _fail_child) Ptrofs.zero)=Some(Internal f_fail_child).
Proof. split; reflexivity. Qed.

Theorem handoff_failure_call_edge e le m k failure stage error stage_expression error_expression :
  e!_fail_child=None -> le!_failure=Some(Vint failure) ->
  expression_value handoff_ge e le m stage_expression (Vint stage) ->
  sem_cast (Vint stage) (typeof stage_expression) tuint m=Some(Vint stage) ->
  expression_value handoff_ge e le m error_expression (Vint error) ->
  sem_cast (Vint error) (typeof error_expression) tint m=Some(Vint error) ->
  store_edge handoff_ge
    (State f_guest (Scall None (Evar _fail_child (Tfunction [tint;tuint;tint] tvoid cc_default))
      [Etempvar _failure tint;stage_expression;error_expression]) k e le m)
    (Callstate (Internal f_fail_child) [Vint failure;Vint stage;Vint error]
      (Kcall None f_guest e le k) m).
Proof.
  intros GLOBAL FAILURE STAGE STAGE_CAST ERROR ERROR_CAST; eapply certified_call_edge.
  - reflexivity.
  - apply old_expression_value; eapply value_function;
      [exact GLOBAL|exact(proj1 handoff_failure_binding)|reflexivity].
  - eapply cons_argument_values.
    + apply old_expression_value,value_temp; exact FAILURE.
    + reflexivity.
    + eapply cons_argument_values; [exact STAGE|exact STAGE_CAST|].
      eapply cons_argument_values; [exact ERROR|exact ERROR_CAST|apply no_argument_values].
  - exact(proj2 handoff_failure_binding).
  - reflexivity.
Qed.

Lemma handoff_error_number_binding :
  Genv.find_symbol handoff_ge _error_number=Some(handoff_symbol _error_number) /\
  Genv.find_funct handoff_ge (Vptr(handoff_symbol _error_number) Ptrofs.zero)=Some(Internal f_error_number).
Proof. split; reflexivity. Qed.

Lemma handoff_count_negative_value ge m count :
  sem_binary_operation ge Olt (Vint count) tint (Vint Int.zero) tint m=
    Some(Val.of_bool (Int.signed count <? 0)).
Proof.
  change (Some(Val.of_bool(Int.lt count Int.zero))=Some(Val.of_bool(Int.signed count <? 0))).
  unfold Int.lt; change (Some(Val.of_bool(if zlt (Int.signed count) 0 then true else false))=
    Some(Val.of_bool(Int.signed count <? 0))).
  destruct (zlt (Int.signed count) 0).
  - rewrite (proj2(Z.ltb_lt (Int.signed count) 0) l); reflexivity.
  - rewrite (proj2(Z.ltb_ge (Int.signed count) 0) ltac:(lia)); reflexivity.
Qed.

Definition handoff_count_error_cont returned selected e le k :=
  Kcall (Some returned) f_guest e le
    (Kseq (Sset selected (Ecast(Etempvar returned tint)tint)) k).

Theorem handoff_count_error_call_source e le m k returned selected :
  e!_error_number=None ->
  store_path handoff_ge (fun after=>after=m)
    (State f_guest
      (Ssequence (Scall (Some returned) (Evar _error_number(Tfunction [] tint cc_default)) [])
        (Sset selected (Ecast(Etempvar returned tint)tint))) k e le m) 2
    (Callstate (Internal f_error_number) [] (handoff_count_error_cont returned selected e le k) m).
Proof.
  intros GLOBAL; unfold handoff_count_error_cont; handoff_route.
  eapply store_next; [reflexivity| |].
  - eapply certified_call_edge.
    + reflexivity.
    + apply old_expression_value; eapply value_function;
        [exact GLOBAL|exact(proj1 handoff_error_number_binding)|reflexivity].
    + apply no_argument_values.
    + exact(proj2 handoff_error_number_binding).
    + reflexivity.
  - apply store_done; reflexivity.
Qed.

Theorem handoff_count_error_return_source e le m k returned selected error :
  store_path handoff_ge (fun after=>after=m)
    (Returnstate (Vint error) (handoff_count_error_cont returned selected e le k) m) 3
    (State f_guest Sskip k e (PTree.set selected (Vint error) (PTree.set returned (Vint error) le)) m).
Proof.
  unfold handoff_count_error_cont; handoff_route; handoff_route; handoff_set.
  - eapply cast_expression_value; [apply old_expression_value,value_temp; apply PTree.gss|reflexivity].
  - apply store_done; reflexivity.
Qed.

Definition handoff_count_temp_frame (original final:temp_env) bad returned selected :=
  forall id, ~In id [bad;returned;selected] -> final!id=original!id.

Lemma handoff_count_frame_refl (le:temp_env) bad returned selected :
  handoff_count_temp_frame le le bad returned selected.
Proof. intros id ABSENT; reflexivity. Qed.

Lemma handoff_count_frame_set (original final:temp_env) bad returned selected changed value :
  handoff_count_temp_frame original final bad returned selected -> In changed [bad;returned;selected] ->
  handoff_count_temp_frame original (PTree.set changed value final) bad returned selected.
Proof.
  intros FRAME PRESENT id ABSENT; rewrite PTree.gso by (intro SAME; subst; contradiction).
  apply FRAME; exact ABSENT.
Qed.

Definition handoff_count_leaf e original m k bad returned selected count failure state :=
  (exists final, state=State f_guest Sskip k e final m /\
    handoff_count_temp_frame original final bad returned selected /\ 0<Int.signed count<32) \/
  (exists final error,
    state=Callstate (Internal f_fail_child) [Vint failure;Vint Int.one;Vint error]
      (Kcall None f_guest e final k) m /\
    handoff_count_temp_frame original final bad returned selected /\ 1<=Int.signed error<=4095).

Theorem handoff_count_region cell e le m k bad returned selected count failure (P:mem->Prop) :
  e!_error_number=None -> e!_fail_child=None ->
  le!_count=Some(Vint count) -> le!_failure=Some(Vint failure) ->
  bad<>_count -> bad<>_failure -> returned<>_failure -> selected<>_failure ->
  entry_errno_ready cell m -> P m ->
  handoff_region handoff_ge cell P
    (handoff_count_leaf e le m k bad returned selected count failure) 128
    (State f_guest (handoff_count_program bad returned selected) k e le m).
Proof.
  intros ERROR_GLOBAL FAILURE_GLOBAL COUNT FAILURE BAD_COUNT BAD_FAILURE RETURN_FAILURE SELECT_FAILURE
    [error ERRNO] GOOD.
  set (R:=handoff_count_leaf e le m k bad returned selected count failure).
  set (chosen:=PTree.set bad (Val.of_bool(handoff_count_bad count)) le).
  assert (CHOSEN:handoff_count_temp_frame le chosen bad returned selected).
  { apply handoff_count_frame_set; [apply handoff_count_frame_refl|cbn; auto]. }
  assert (CHOSEN_FAILURE:chosen!_failure=Some(Vint failure)).
  { unfold chosen; rewrite PTree.gso by congruence; exact FAILURE. }
  assert (CHOSEN_COUNT:chosen!_count=Some(Vint count)).
  { unfold chosen; rewrite PTree.gso by congruence; exact COUNT. }
  unfold handoff_count_program.
  eapply handoff_region_source_prepend; [exact GOOD|apply unchanged_store_edge; WriteAll.structural|].
  eapply handoff_region_store_path with (count:=2%nat) (remaining:=125%nat).
  - eapply number_path_implication with (P:=fun after=>after=m).
    + intros after SAME; subst; exact GOOD.
    + apply handoff_count_choose_source; exact COUNT.
  - eapply handoff_region_source_prepend; [exact GOOD|apply unchanged_store_edge; WriteAll.structural|].
    unfold handoff_count_reject.
    eapply handoff_region_source_prepend; [exact GOOD|apply certified_if_edge with
      (v:=Val.of_bool(handoff_count_bad count)) (b:=handoff_count_bad count)|].
    + apply old_expression_value,value_temp; unfold chosen; apply PTree.gss.
    + apply number_bool_value.
    + destruct (handoff_count_bad count) eqn:BAD.
      * eapply handoff_region_source_prepend; [exact GOOD|apply unchanged_store_edge; WriteAll.structural|].
        unfold handoff_count_error.
        eapply handoff_region_source_prepend; [exact GOOD|apply certified_if_edge with
          (v:=Val.of_bool(Int.signed count <? 0)) (b:=Int.signed count <? 0)|].
        -- eapply binary_expression_value.
           ++ apply old_expression_value,value_temp; exact CHOSEN_COUNT.
           ++ apply old_expression_value,value_int.
           ++ apply handoff_count_negative_value.
        -- apply number_bool_value.
        -- destruct (Int.signed count <? 0) eqn:NEGATIVE.
           ++ eapply handoff_region_store_path with (count:=2%nat) (remaining:=119%nat).
              ** eapply number_path_implication with (P:=fun after=>after=m).
                 --- intros after SAME; subst; exact GOOD.
                 --- apply handoff_count_error_call_source; exact ERROR_GLOBAL.
              ** eapply handoff_region_weaken with (n:=(source_length error+85)%nat).
                 --- apply current_entry_error_region with (error:=error); [exact ERRNO|exact I|exact GOOD|].
                     eapply handoff_region_store_path with (count:=3%nat) (remaining:=82%nat).
                     +++ eapply number_path_implication with (P:=fun after=>after=m).
                         *** intros after SAME; subst; exact GOOD.
                         *** apply handoff_count_error_return_source.
                     +++ eapply handoff_region_source_prepend; [exact GOOD|apply unchanged_store_edge; WriteAll.structural|].
                         unfold handoff_count_failure.
                         eapply handoff_region_source_prepend; [exact GOOD|eapply handoff_failure_call_edge|].
                         *** exact FAILURE_GLOBAL.
                         *** rewrite !PTree.gso by congruence; exact FAILURE.
                         *** apply old_expression_value,value_int.
                         *** reflexivity.
                         *** apply old_expression_value,value_temp; apply PTree.gss.
                         *** reflexivity.
                         *** apply handoff_region_stop; [exact GOOD|].
                             right; eexists; exists(normalize error); split; [reflexivity|].
                             split.
                             ---- apply handoff_count_frame_set.
                                  ++++ apply handoff_count_frame_set; [exact CHOSEN|cbn; auto].
                                  ++++ cbn; auto.
                             ---- apply current_entry_error_range.
                 --- unfold source_length; destruct(positive error),(bounded error); cbn; lia.
           ++ eapply handoff_region_source_prepend; [exact GOOD|apply certified_set_edge|].
              ** eapply cast_expression_value; [apply old_expression_value,value_int|reflexivity].
              ** eapply handoff_region_source_prepend; [exact GOOD|apply unchanged_store_edge; WriteAll.structural|].
                 unfold handoff_count_failure.
                 eapply handoff_region_source_prepend; [exact GOOD|eapply handoff_failure_call_edge|].
                 --- exact FAILURE_GLOBAL.
                 --- rewrite !PTree.gso by congruence; exact FAILURE.
                 --- apply old_expression_value,value_int.
                 --- reflexivity.
                 --- apply old_expression_value,value_temp; apply PTree.gss.
                 --- reflexivity.
                 --- apply handoff_region_stop; [exact GOOD|].
                     right; eexists; exists(Int.repr 75); split; [reflexivity|]. split.
                     +++ apply handoff_count_frame_set; [exact CHOSEN|cbn; auto].
                     +++ change (1<=75<=4095); lia.
      * apply handoff_region_stop; [exact GOOD|].
        left; exists chosen; split; [reflexivity|]. split; [exact CHOSEN|].
        apply (proj1(handoff_count_good count)); exact BAD.
Qed.

Definition handoff_error_failure_program returned stage :=
  Ssequence (Scall (Some returned) (Evar _error_number(Tfunction [] tint cc_default)) [])
    (Scall None (Evar _fail_child(Tfunction [tint;tuint;tint] tvoid cc_default))
      [Etempvar _failure tint;Econst_int stage tint;Etempvar returned tint]).

Definition handoff_error_failure_cont returned stage e le k :=
  Kcall (Some returned) f_guest e le
    (Kseq (Scall None (Evar _fail_child(Tfunction [tint;tuint;tint] tvoid cc_default))
      [Etempvar _failure tint;Econst_int stage tint;Etempvar returned tint]) k).

Theorem handoff_error_failure_source e le m k returned stage :
  e!_error_number=None ->
  store_path handoff_ge (fun after=>after=m)
    (State f_guest (handoff_error_failure_program returned stage) k e le m) 2
    (Callstate (Internal f_error_number) [] (handoff_error_failure_cont returned stage e le k) m).
Proof.
  intros GLOBAL; unfold handoff_error_failure_program,handoff_error_failure_cont; handoff_route.
  eapply store_next; [reflexivity| |].
  - eapply certified_call_edge.
    + reflexivity.
    + apply old_expression_value; eapply value_function;
        [exact GLOBAL|exact(proj1 handoff_error_number_binding)|reflexivity].
    + apply no_argument_values.
    + exact(proj2 handoff_error_number_binding).
    + reflexivity.
  - apply store_done; reflexivity.
Qed.

Theorem handoff_error_failure_region cell e le m k returned stage failure (P:mem->Prop) :
  e!_error_number=None -> e!_fail_child=None -> returned<>_failure ->
  le!_failure=Some(Vint failure) -> entry_errno_ready cell m -> P m ->
  handoff_region handoff_ge cell P
    (fun state=>exists error,1<=Int.signed error<=4095 /\
      state=Callstate (Internal f_fail_child) [Vint failure;Vint stage;Vint error]
        (Kcall None f_guest e (PTree.set returned (Vint error) le) k) m) 128
    (State f_guest (handoff_error_failure_program returned stage) k e le m).
Proof.
  intros ERROR_GLOBAL FAILURE_GLOBAL DIFFERENT FAILURE [error ERRNO] GOOD.
  eapply handoff_region_weaken with (n:=(2+source_length error+3)%nat).
  - eapply handoff_region_store_path with (count:=2%nat) (remaining:=(source_length error+3)%nat).
    + eapply number_path_implication with (P:=fun after=>after=m).
      * intros after SAME; subst; exact GOOD.
      * apply handoff_error_failure_source; exact ERROR_GLOBAL.
    + apply current_entry_error_region with (error:=error); [exact ERRNO|exact I|exact GOOD|].
      unfold handoff_error_failure_cont.
      eapply handoff_region_source_prepend; [exact GOOD|apply unchanged_store_edge; WriteAll.structural|].
      eapply handoff_region_source_prepend; [exact GOOD|apply unchanged_store_edge; WriteAll.structural|].
      eapply handoff_region_source_prepend; [exact GOOD|eapply handoff_failure_call_edge|].
      * exact FAILURE_GLOBAL.
      * cbn [set_opttemp]; rewrite PTree.gso by congruence; exact FAILURE.
      * apply old_expression_value,value_int.
      * reflexivity.
      * apply old_expression_value,value_temp; apply PTree.gss.
      * reflexivity.
      * apply handoff_region_stop; [exact GOOD|].
        exists(normalize error); split; [apply current_entry_error_range|reflexivity].
  - unfold source_length; destruct(positive error),(bounded error); cbn; lia.
Qed.

Theorem handoff_count_success_source e le m k bad returned selected count :
  le!_count=Some(Vint count) -> 0<Int.signed count<32 ->
  store_path handoff_ge (fun after=>after=m)
    (State f_guest (handoff_count_program bad returned selected) k e le m) 5
    (State f_guest Sskip k e (PTree.set bad (Vint Int.zero) le)m).
Proof.
  intros COUNT GOOD.
  assert (BAD:handoff_count_bad count=false) by (apply(proj2(handoff_count_good count));exact GOOD).
  pose proof(handoff_count_choose_source e le m
    (Kseq(handoff_count_reject bad returned selected)k)bad count COUNT)as CHOOSE.
  rewrite BAD in CHOOSE.
  unfold handoff_count_program; handoff_route.
  eapply store_path_trans with(n:=2%nat); [exact CHOOSE|].
  handoff_route; unfold handoff_count_reject.
  eapply store_next; [reflexivity|apply certified_if_edge with(v:=Vint Int.zero)(b:=false)|].
  - apply old_expression_value,value_temp; apply PTree.gss.
  - reflexivity.
  - apply store_done; reflexivity.
Qed.
