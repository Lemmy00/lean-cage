(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-entry.release: Real source initializes the private byte and checks resume before write. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs
  Ctypes Ctypesdefs Cop Clight.
Require Import IO Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessAllocation ProcessStructure ProcessReturns.
Import ListNotations.
Open Scope Z_scope.

Definition release_env (grant : block) : env := PTree.set _grant (grant,tuchar) empty_env.
Definition release_parameters child peer : temp_env :=
  PTree.set _peer (Vint peer) (PTree.set _child (Vint child)
    (create_undef_temps (fn_temps f_release_child))).
Definition release_tail index := admission_tail index (fn_body f_release_child).
Definition release_failure := Sreturn (Some (Eunop Oneg (Econst_int Int.one tint) tint)).
Definition release_resume_guard := Sifthenelse (Etempvar _t'1 tlong) release_failure Sskip.
Definition release_write_guard := Sifthenelse
  (Ebinop One (Etempvar _t'2 tlong) (Econst_int Int.one tint) tint) release_failure Sskip.
Definition release_resume_cont grant le k :=
  Kcall (Some _t'1) f_release_child (release_env grant) le
    (Kseq release_resume_guard (Kseq (release_tail 2) k)).
Definition release_write_cont grant le k :=
  Kcall (Some _t'2) f_release_child (release_env grant) le
    (Kseq release_write_guard (Kseq (release_tail 3) k)).

Theorem release_source_phases : fn_body f_release_child =
  Ssequence (Sassign (Evar _grant tuchar) (Econst_int (Int.repr 165) tint))
    (Ssequence
      (Ssequence (Scall (Some _t'1)
        (Evar _entry_ptrace4 (Tfunction [tint;tint;tptr tvoid;tptr tvoid] tlong cc_default))
        [Econst_int (Int.repr 7) tint;Etempvar _child tint;
         Econst_int Int.zero tint;Econst_int Int.zero tint]) release_resume_guard)
      (Ssequence
        (Ssequence (Scall (Some _t'2)
          (Evar _write (Tfunction [tint;tptr tvoid;tulong] tlong cc_default))
          [Etempvar _peer tint;Eaddrof (Evar _grant tuchar) (tptr tuchar);
           Econst_int Int.one tint]) release_write_guard)
        (Sreturn (Some (Econst_int Int.zero tint))))).
Proof. reflexivity. Qed.

Lemma release_nonlocal_binding grant id : id <> _grant -> (release_env grant)!id = None.
Proof. intro OTHER; unfold release_env; rewrite PTree.gso by congruence; apply PTree.gempty. Qed.

Theorem release_function_entry before allocated grant child peer :
  Mem.alloc before 0 1 = (allocated,grant) ->
  function_entry2 admission_ge f_release_child [Vint child;Vint peer] before
    (release_env grant) (release_parameters child peer) allocated.
Proof.
  intro ALLOC; constructor.
  - repeat (apply list_norepet_cons; [cbn;intuition discriminate|]); apply list_norepet_nil.
  - repeat (apply list_norepet_cons; [cbn;intuition discriminate|]); apply list_norepet_nil.
  - unfold list_disjoint,var_names; cbn; intros a b A B.
    repeat destruct A as [A|A]; try contradiction; subst a;
      repeat destruct B as [B|B]; try contradiction; subst b; discriminate.
  - unfold release_env; econstructor; [exact ALLOC|constructor].
  - reflexivity.
Qed.

Theorem release_primitive_symbols :
  (exists object, Genv.find_symbol admission_ge _entry_ptrace4 = Some object /\
    Genv.find_funct admission_ge (Vptr object Ptrofs.zero) = Some process_ptrace_definition) /\
  (exists object, Genv.find_symbol admission_ge _write = Some object /\
    Genv.find_funct admission_ge (Vptr object Ptrofs.zero) =
      Some (External (io_function writing) [tint;tptr tvoid;tulong] tlong cc_default)).
Proof. split; eexists; split; vm_compute; reflexivity. Qed.

Local Opaque EntrySource.prog.

Theorem release_grant_initialization grant le before after k :
  Mem.store Mint8unsigned before grant 0 (Vint (Int.repr 165)) = Some after ->
  store_edge admission_ge
    (State f_release_child (Sassign (Evar _grant tuchar) (Econst_int (Int.repr 165) tint))
      k (release_env grant) le before)
    (State f_release_child Sskip k (release_env grant) le after).
Proof.
  intro STORE; eapply assignment_source_edge with (b:=grant) (ofs:=Ptrofs.zero)
    (v:=Vint (Int.repr 165)) (w:=Vint (Int.repr 165)).
  - apply local_location_value; unfold release_env; apply PTree.gss.
  - apply old_expression_value,value_int.
  - reflexivity.
  - eapply assign_loc_value; [reflexivity|]. unfold Mem.storev.
    exact STORE.
Qed.

Theorem release_start_to_resume before allocated grant after child peer k :
  Mem.alloc before 0 1 = (allocated,grant) ->
  Mem.store Mint8unsigned allocated grant 0 (Vint (Int.repr 165)) = Some after ->
  store_path admission_ge (fun _ => True)
    (Callstate (Internal f_release_child) [Vint child;Vint peer] k before) 7
    (Callstate process_ptrace_definition
      [Vint (Int.repr 7);Vint child;Vlong Int64.zero;Vlong Int64.zero]
      (release_resume_cont grant (release_parameters child peer) k) after).
Proof.
  intros ALLOC STORE; destruct release_primitive_symbols as [[object [SYMBOL FUNCTION]] _].
  eapply store_next; [exact I|apply function_entry_source_edge,release_function_entry;exact ALLOC|].
  rewrite release_source_phases; admission_route.
  eapply store_next; [exact I|apply release_grant_initialization;exact STORE|].
  admission_route; admission_route; admission_route.
  eapply store_next; [exact I|eapply certified_call_edge|apply store_done;exact I].
  - reflexivity.
  - apply old_expression_value; eapply value_function;
      [apply release_nonlocal_binding;discriminate|exact SYMBOL|reflexivity].
  - eapply cons_argument_values; [apply old_expression_value,value_int|reflexivity|].
    eapply cons_argument_values.
    + apply old_expression_value,value_temp; unfold release_parameters;WriteAll.lookup.
    + reflexivity.
    + eapply cons_argument_values; [apply old_expression_value,value_int|reflexivity|].
      eapply cons_argument_values; [apply old_expression_value,value_int|reflexivity|apply no_argument_values].
  - exact FUNCTION.
  - reflexivity.
Qed.

Definition release_resumed returned := Int64.eq returned Int64.zero.
Definition release_after_resume_env le returned := PTree.set _t'1 (Vlong returned) le.

Theorem release_resume_return_source grant le memory k returned :
  store_path admission_ge (fun _ => True)
    (Returnstate (Vlong returned) (release_resume_cont grant le k) memory)
    (if release_resumed returned then 4 else 3)%nat
    (if release_resumed returned then State f_release_child (release_tail 2) k
       (release_env grant) (release_after_resume_env le returned) memory
     else State f_release_child release_failure (Kseq (release_tail 2) k)
       (release_env grant) (release_after_resume_env le returned) memory).
Proof.
  unfold release_resume_cont,release_resume_guard,release_after_resume_env.
  replace (if release_resumed returned then 4 else 3)%nat with
    (S (S (S (if release_resumed returned then 1 else 0))))
    by (destruct (release_resumed returned);reflexivity).
  admission_route; admission_route.
  eapply store_next; [exact I|apply certified_if_edge with
    (v:=Vlong returned) (b:=negb (release_resumed returned))|].
  - apply old_expression_value,value_temp; apply PTree.gss.
  - reflexivity.
  - destruct (release_resumed returned); cbn; [admission_route|];apply store_done;exact I.
Qed.

Theorem release_write_call_source grant le memory k peer : le!_peer = Some (Vint peer) ->
  store_path admission_ge (fun _ => True)
    (State f_release_child (release_tail 2) k (release_env grant) le memory) 3
    (Callstate (External (io_function writing) [tint;tptr tvoid;tulong] tlong cc_default)
      [Vint peer;Vptr grant Ptrofs.zero;Vlong Int64.one]
      (release_write_cont grant le k) memory).
Proof.
  intro PEER; destruct release_primitive_symbols as [_ [object [SYMBOL FUNCTION]]].
  change (release_tail 2) with (Ssequence
    (Ssequence (Scall (Some _t'2)
      (Evar _write (Tfunction [tint;tptr tvoid;tulong] tlong cc_default))
      [Etempvar _peer tint;Eaddrof (Evar _grant tuchar) (tptr tuchar);Econst_int Int.one tint])
      release_write_guard) (release_tail 3)).
  admission_route; admission_route.
  eapply store_next; [exact I|eapply certified_call_edge|apply store_done;exact I].
  - reflexivity.
  - apply old_expression_value; eapply value_function;
      [apply release_nonlocal_binding;discriminate|exact SYMBOL|reflexivity].
  - eapply cons_argument_values; [apply old_expression_value,value_temp;exact PEER|reflexivity|].
    eapply cons_argument_values.
    + assert (LOCAL : (release_env grant)!_grant = Some (grant,tuchar))
        by (unfold release_env;apply PTree.gss).
      split.
      * apply eval_Eaddrof,eval_Evar_local;exact LOCAL.
      * intros other VALUE; inversion VALUE;subst.
        -- match goal with LOCATION : eval_lvalue _ _ _ _ (Evar _ _) _ _ _ |- _ =>
             inversion LOCATION;subst;try congruence end;f_equal;congruence.
        -- match goal with LOCATION : eval_lvalue _ _ _ _ (Eaddrof _ _) _ _ _ |- _ => inversion LOCATION end.
    + reflexivity.
    + eapply cons_argument_values; [apply old_expression_value,value_int|reflexivity|apply no_argument_values].
  - exact FUNCTION.
  - reflexivity.
Qed.

Definition release_written returned := Int64.eq returned Int64.one.
Definition release_after_write_env le returned := PTree.set _t'2 (Vlong returned) le.

Theorem release_write_return_source grant le memory k returned :
  store_path admission_ge (fun _ => True)
    (Returnstate (Vlong returned) (release_write_cont grant le k) memory)
    (if release_written returned then 4 else 3)%nat
    (if release_written returned then State f_release_child (release_tail 3) k
       (release_env grant) (release_after_write_env le returned) memory
     else State f_release_child release_failure (Kseq (release_tail 3) k)
       (release_env grant) (release_after_write_env le returned) memory).
Proof.
  unfold release_write_cont,release_write_guard,release_after_write_env.
  replace (if release_written returned then 4 else 3)%nat with
    (S (S (S (if release_written returned then 1 else 0))))
    by (destruct (release_written returned);reflexivity).
  admission_route; admission_route.
  eapply store_next; [exact I|apply certified_if_edge with
    (v:=Val.of_bool (negb (release_written returned))) (b:=negb (release_written returned))|].
  - apply old_expression_value; eapply value_binary;
      [apply value_temp;apply PTree.gss|apply value_int|reflexivity].
  - destruct (release_written returned);reflexivity.
  - destruct (release_written returned);cbn;[admission_route|];apply store_done;exact I.
Qed.
