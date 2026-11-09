(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: The actual helper tracer has no syscall/register-substitution callsite. *)
From Stdlib Require Import ZArith List Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Smallstep Ctypes Ctypesdefs Cop Clight.
From EntryNative Require Import EntrySource.
Require Import Machine LibraryMachine.
From EntryNative Require Import NativeHandoffMachine.
From EntryProcess Require Import ProcessControl ProcessExpressions ProcessMachine ProcessControlMachine.
Import ListNotations.
Open Scope Z_scope.

Definition tracer_request_allowed (request : int) : bool :=
  Int.eq request (Int.repr 7) || Int.eq request (Int.repr 16896) ||
  Int.eq request (Int.repr 16898).

Definition tracer_signature := Tfunction [tint; tint; tptr tvoid; tptr tvoid] tlong cc_default.
Definition tracer_expression := Evar _entry_ptrace4 tracer_signature.
Definition tracer_options :=
  Ecast (Ecast (Ebinop Oor (Econst_int (Int.repr 16) tint)
    (Econst_int (Int.repr 1048576) tint) tint) tulong) (tptr tvoid).

Definition tracer_call_allowed (fn : expr) (args : list expr) : bool :=
  match fn with
  | Evar id _ =>
      if Pos.eqb id _entry_ptrace4 then
        expression_equal fn tracer_expression && match args with
        | [Econst_int request request_type; child; _; data] =>
            if type_eq request_type tint then
              if type_eq (typeof child) tint then
                tracer_request_allowed request &&
                (if Int.eq request (Int.repr 16896) then
                   expression_equal data tracer_options else true)
              else false
            else false
        | _ => false
        end
      else true
  | _ => false
  end.

Definition helper_functions_checked : bool :=
  forallb (fun item => match snd item with
    | Gfun (Internal fn) => checked_statement tracer_call_allowed (fn_body fn)
    | _ => true
    end) (prog_defs EntrySource.prog).

Theorem helper_tracer_source_checked : helper_functions_checked = true.
Proof. vm_compute; reflexivity. Qed.

Local Opaque EntrySource.prog.

Lemma helper_function_checked address fn :
  Genv.find_funct (Clight.globalenv EntrySource.prog) address = Some (Internal fn) ->
  checked_statement tracer_call_allowed (fn_body fn) = true.
Proof.
  intro FOUND. destruct (Genv.find_funct_inversion EntrySource.prog address FOUND) as [id MEMBER].
  pose proof helper_tracer_source_checked as CHECKED.
  unfold helper_functions_checked in CHECKED.
  apply forallb_forall with (x := (id,Gfun (Internal fn))) in CHECKED; auto.
Qed.

Lemma tracer_options_value (ge : genv) env temps memory :
  eval_expr ge env temps memory tracer_options (Vlong (Int64.repr 1048592)).
Proof.
  unfold tracer_options.
  eapply eval_Ecast with (v1 := Vlong (Int64.repr 1048592)); [|reflexivity].
  eapply eval_Ecast with (v1 := Vint (Int.repr 1048592)); [|reflexivity].
  eapply eval_Ebinop with (v1 := Vint (Int.repr 16))
    (v2 := Vint (Int.repr 1048576)); [constructor|constructor|reflexivity].
Qed.

Lemma literal_value_exact (ge : genv) env temps memory word ty value :
  eval_expr ge env temps memory (Econst_int word ty) value -> value = Vint word.
Proof.
  intro EVAL; inversion EVAL; subst; auto.
  match goal with H : eval_lvalue _ _ _ _ (Econst_int _ _) _ _ _ |- _ => inversion H end.
Qed.

Lemma temporary_value_exact (ge : genv) env temps memory id ty value :
  eval_expr ge env temps memory (Etempvar id ty) value -> temps!id = Some value.
Proof.
  intro EVAL; inversion EVAL; subst; auto.
  match goal with H : eval_lvalue _ _ _ _ (Etempvar _ _) _ _ _ |- _ => inversion H end.
Qed.

Lemma tracer_argument_values (ge : genv) env temps memory request child address data values :
  eval_exprlist ge env temps memory
    [Econst_int request tint; child; address; data]
    [tint; tint; tptr tvoid; tptr tvoid] values ->
  exists child_value address_value data_value,
    values = [Vint request; child_value; address_value; data_value].
Proof.
  intro EVAL.
  inversion EVAL as [|a bl ty tyl v1 v2 values1 HEAD CAST TAIL]; subst; clear EVAL.
  apply literal_value_exact in HEAD; subst v1.
  cbn in CAST; inversion CAST; subst; clear CAST.
  inversion TAIL as [|a bl ty tyl v21 v22 values2 HEAD2 CAST2 REST]; subst; clear TAIL.
  inversion REST as [|a bl ty tyl v31 v32 values3 HEAD3 CAST3 TAIL]; subst; clear REST.
  inversion TAIL as [|a bl ty tyl v41 v42 values4 HEAD4 CAST4 REST]; subst; clear TAIL.
  inversion REST; subst.
  do 3 eexists; reflexivity.
Qed.

Theorem helper_tracer_prefix start trace after :
  checked_state tracer_call_allowed start ->
  star step2 (Clight.globalenv EntrySource.prog) start trace after ->
  checked_state tracer_call_allowed after.
Proof.
  apply checked_execution_prefix. exact helper_function_checked.
Qed.

Lemma tracer_request_exact request : tracer_request_allowed request = true ->
  request = Int.repr 7 \/ request = Int.repr 16896 \/ request = Int.repr 16898.
Proof.
  unfold tracer_request_allowed. rewrite !orb_true_iff.
  intros [[CONT|OPTIONS]|INFO]; [left|right;left|right;right];
    apply Int.same_if_eq; assumption.
Qed.

Lemma tracer_call_shape ty args :
  tracer_call_allowed (Evar _entry_ptrace4 ty) args = true ->
  exists request child address data,
    args = [Econst_int request tint; child; address; data] /\
    ty = tracer_signature /\ typeof child = tint /\
    (request = Int.repr 7 \/ request = Int.repr 16896 \/ request = Int.repr 16898) /\
    (request = Int.repr 16896 -> data = tracer_options).
Proof.
  intro CALL.
  cbn [tracer_call_allowed] in CALL.
  rewrite Pos.eqb_refl in CALL.
  apply andb_true_iff in CALL as [SIGNATURE CALL].
  apply expression_equal_exact in SIGNATURE.
  unfold tracer_expression in SIGNATURE. inversion SIGNATURE; subst ty.
  destruct args as [|first [|child [|address [|data [|extra tail]]]]];
    try destruct first; cbn in CALL; try discriminate.
  change ((if type_eq t tint then if type_eq (typeof child) tint then
    tracer_request_allowed i &&
    (if Int.eq i (Int.repr 16896) then expression_equal data tracer_options else true)
    else false else false) = true) in CALL.
  destruct (type_eq t tint) as [REQUESTTYPE|]; [subst t|discriminate].
  destruct (type_eq (typeof child) tint) as [CHILDTYPE|]; [|discriminate].
  apply andb_true_iff in CALL as [REQUEST OPTIONS].
  do 4 eexists; split; [reflexivity|]. split; [reflexivity|]. split; [exact CHILDTYPE|]. split.
  - apply tracer_request_exact; exact REQUEST.
  - intro SAME. subst i. rewrite Int.eq_true in OPTIONS.
    apply expression_equal_exact; exact OPTIONS.
Qed.

Theorem helper_tracer_callsite start trace fn opt args k env temps memory ty :
  checked_state tracer_call_allowed start ->
  star step2 (Clight.globalenv EntrySource.prog) start trace
    (State fn (Scall opt (Evar _entry_ptrace4 ty) args) k env temps memory) ->
  exists request child address data,
    args = [Econst_int request tint; child; address; data] /\
    ty = tracer_signature /\ typeof child = tint /\
    (request = Int.repr 7 \/ request = Int.repr 16896 \/ request = Int.repr 16898) /\
    (request = Int.repr 16896 -> data = tracer_options).
Proof.
  intros INITIAL RUN.
  pose proof (helper_tracer_prefix _ _ _ INITIAL RUN) as [_ [CALL _]].
  apply tracer_call_shape; exact CALL.
Qed.

Theorem namespace_init_checked arguments memory :
  checked_state tracer_call_allowed
    (Callstate (Internal f_namespace_init) arguments Kstop memory).
Proof. split; [vm_compute; reflexivity|exact I]. Qed.

Theorem namespace_tracer_callsite arguments before trace fn opt args k env temps memory ty :
  star step2 (Clight.globalenv EntrySource.prog)
    (Callstate (Internal f_namespace_init) arguments Kstop before) trace
    (State fn (Scall opt (Evar _entry_ptrace4 ty) args) k env temps memory) ->
  exists request child address data,
    args = [Econst_int request tint; child; address; data] /\
    ty = tracer_signature /\ typeof child = tint /\
    (request = Int.repr 7 \/ request = Int.repr 16896 \/ request = Int.repr 16898) /\
    (request = Int.repr 16896 -> data = tracer_options).
Proof.
  apply helper_tracer_callsite. apply namespace_init_checked.
Qed.

Theorem namespace_tracer_invocation arguments before trace fn opt args k env temps memory
    ty calltrace fd values next :
  star step2 (Clight.globalenv EntrySource.prog)
    (Callstate (Internal f_namespace_init) arguments Kstop before) trace
    (State fn (Scall opt (Evar _entry_ptrace4 ty) args) k env temps memory) ->
  step2 (Clight.globalenv EntrySource.prog)
    (State fn (Scall opt (Evar _entry_ptrace4 ty) args) k env temps memory) calltrace
    (Callstate fd values next memory) ->
  exists request child_value address_value data_value,
    values = [Vint request; child_value; address_value; data_value] /\
    (request = Int.repr 7 \/ request = Int.repr 16896 \/ request = Int.repr 16898).
Proof.
  intros RUN CALL.
  destruct (namespace_tracer_callsite _ _ _ _ _ _ _ _ _ _ _ RUN)
    as [request [child [address [data [ARGS [TYPE [CHILDTYPE [REQUEST OPTIONS]]]]]]]].
  subst args ty. inversion CALL; subst.
  match goal with H : classify_fun (typeof (Evar _entry_ptrace4 tracer_signature)) = _ |- _ =>
    cbn [tracer_signature typeof classify_fun] in H; inversion H; subst
  end.
  match goal with H : eval_exprlist _ _ _ _ _ _ _ |- _ =>
    destruct (tracer_argument_values _ _ _ _ _ _ _ _ _ H)
      as [child_value [address_value [data_value VALUES]]]
  end.
  do 4 eexists; split; eauto.
Qed.

Theorem helper_process_tracer_callsite cell start events fn opt args k env temps memory ty :
  checked_machine tracer_call_allowed start ->
  process_steps (Clight.globalenv EntrySource.prog) cell start events
    (live (State fn (Scall opt (Evar _entry_ptrace4 ty) args) k env temps memory)) ->
  exists request child address data,
    args = [Econst_int request tint; child; address; data] /\
    ty = tracer_signature /\ typeof child = tint /\
    (request = Int.repr 7 \/ request = Int.repr 16896 \/ request = Int.repr 16898) /\
    (request = Int.repr 16896 -> data = tracer_options).
Proof.
  intros INITIAL RUN.
  pose proof (checked_process_prefix tracer_call_allowed _ _ helper_function_checked _ _ _
    INITIAL RUN) as [_ [CALL _]].
  apply tracer_call_shape; exact CALL.
Qed.

Theorem namespace_process_tracer_callsite cell arguments before events fn opt args k env temps memory ty :
  process_steps (Clight.globalenv EntrySource.prog) cell
    (live (Callstate (Internal f_namespace_init) arguments Kstop before)) events
    (live (State fn (Scall opt (Evar _entry_ptrace4 ty) args) k env temps memory)) ->
  exists request child address data,
    args = [Econst_int request tint; child; address; data] /\
    ty = tracer_signature /\ typeof child = tint /\
    (request = Int.repr 7 \/ request = Int.repr 16896 \/ request = Int.repr 16898) /\
    (request = Int.repr 16896 -> data = tracer_options).
Proof.
  apply helper_process_tracer_callsite. apply namespace_init_checked.
Qed.

Theorem admission_process_tracer_callsite cell arguments before events fn opt args k env temps memory ty :
  process_steps (Clight.globalenv EntrySource.prog) cell
    (live (Callstate (Internal f_admit_child) arguments Kstop before)) events
    (live (State fn (Scall opt (Evar _entry_ptrace4 ty) args) k env temps memory)) ->
  exists request child address data,
    args = [Econst_int request tint; child; address; data] /\
    ty = tracer_signature /\ typeof child = tint /\
    (request = Int.repr 7 \/ request = Int.repr 16896 \/ request = Int.repr 16898) /\
    (request = Int.repr 16896 -> data = tracer_options).
Proof.
  apply helper_process_tracer_callsite. split; [vm_compute; reflexivity|exact I].
Qed.

Theorem namespace_process_tracer_invocation cell arguments before events fn opt args k env temps memory
    ty event fd values next :
  process_steps (Clight.globalenv EntrySource.prog) cell
    (live (Callstate (Internal f_namespace_init) arguments Kstop before)) events
    (live (State fn (Scall opt (Evar _entry_ptrace4 ty) args) k env temps memory)) ->
  process_step (Clight.globalenv EntrySource.prog) cell
    (live (State fn (Scall opt (Evar _entry_ptrace4 ty) args) k env temps memory)) event
    (live (Callstate fd values next memory)) ->
  exists request child_value address_value data_value,
    values = [Vint request; child_value; address_value; data_value] /\
    (request = Int.repr 7 \/ request = Int.repr 16896 \/ request = Int.repr 16898).
Proof.
  intros RUN CALL.
  destruct (namespace_process_tracer_callsite _ _ _ _ _ _ _ _ _ _ _ _ RUN)
    as [request [child [address [data [ARGS [TYPE [CHILDTYPE [REQUEST OPTIONS]]]]]]]].
  subst args ty.
  assert (INTERNAL : internal_state (State fn
    (Scall opt (Evar _entry_ptrace4 tracer_signature)
      [Econst_int request tint; child; address; data]) k env temps memory)) by exact I.
  destruct (process_internal_step_exact _ _ _ _ _ INTERNAL CALL) as [original [EVENT STEP]].
  inversion STEP; subst; try match goal with H : boundary _ _ _ |- _ => inversion H end.
  match goal with H : step2 _ _ _ _ |- _ => inversion H; subst end.
  match goal with H : classify_fun (typeof (Evar _entry_ptrace4 tracer_signature)) = _ |- _ =>
    cbn [tracer_signature typeof classify_fun] in H; inversion H; subst
  end.
  match goal with H : eval_exprlist _ _ _ _ _ _ _ |- _ =>
    destruct (tracer_argument_values _ _ _ _ _ _ _ _ _ H)
      as [child_value [address_value [data_value VALUES]]]
  end.
  do 4 eexists; split; eauto.
Qed.
