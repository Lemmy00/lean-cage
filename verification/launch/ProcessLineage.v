(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-entry.provenance: Native helpers cannot install a filter or bypass the restricted tracer. *)
From Stdlib Require Import ZArith List Bool Lia.
From compcert Require Import Coqlib Integers AST Values Events Globalenvs Smallstep Ctypes Clight.
From EntryNative Require Import EntrySource.
From EntryProcess Require Import ProcessControl.
Import ListNotations.
Open Scope Z_scope.

Definition avoids_requests (excluded : list Z) (args : list expr) : bool :=
  match args with
  | Econst_int request _ :: _ =>
      forallb (fun code => negb (Int.eq request (Int.repr code))) excluded
  | _ => false
  end.

Definition lineage_call_allowed (fn : expr) (args : list expr) : bool :=
  match fn with
  | Evar id _ =>
      if Pos.eqb id _prctl || Pos.eqb id _entry_prctl5 then avoids_requests [22] args
      else if Pos.eqb id _syscall then
        match args with
        | Econst_int request _::_ => (Int.unsigned request <? 1073741824) && avoids_requests [101;157;317] args
        | _=>false
        end
      else true
  | _ => false
  end.

Definition helper_lineage_checked : bool :=
  forallb (fun item => match snd item with
    | Gfun (Internal fn) => checked_statement lineage_call_allowed (fn_body fn)
    | _ => true
    end) (prog_defs EntrySource.prog).

Theorem helper_lineage_source_checked : helper_lineage_checked = true.
Proof. vm_compute; reflexivity. Qed.

Local Opaque EntrySource.prog.

Lemma helper_lineage_function_checked address fn :
  Genv.find_funct (Clight.globalenv EntrySource.prog) address = Some (Internal fn) ->
  checked_statement lineage_call_allowed (fn_body fn) = true.
Proof.
  intro FOUND. destruct (Genv.find_funct_inversion EntrySource.prog address FOUND) as [id MEMBER].
  pose proof helper_lineage_source_checked as CHECKED.
  unfold helper_lineage_checked in CHECKED.
  apply forallb_forall with (x := (id,Gfun (Internal fn))) in CHECKED; auto.
Qed.

Lemma namespace_lineage_initial arguments memory :
  checked_state lineage_call_allowed
    (Callstate (Internal f_namespace_init) arguments Kstop memory).
Proof. split; [vm_compute; reflexivity|exact I]. Qed.

Theorem namespace_lineage_prefix arguments before trace after :
  star step2 (Clight.globalenv EntrySource.prog)
    (Callstate (Internal f_namespace_init) arguments Kstop before) trace after ->
  checked_state lineage_call_allowed after.
Proof.
  apply checked_execution_prefix; [exact helper_lineage_function_checked|].
  apply namespace_lineage_initial.
Qed.

Lemma avoids_requests_exact excluded args : avoids_requests excluded args = true ->
  exists request ty rest, args = Econst_int request ty :: rest /\
    forall code, In code excluded -> request <> Int.repr code.
Proof.
  destruct args as [|first rest]; cbn; try discriminate.
  destruct first; cbn; try discriminate. intro SAFE.
  exists i, t, rest; split; [reflexivity|]. intros code MEMBER SAME.
  apply forallb_forall with (x := code) in SAFE; auto.
  rewrite SAME, Int.eq_true in SAFE; discriminate.
Qed.

Theorem namespace_prctl_no_install arguments before trace fn opt args k env temps memory ty :
  star step2 (Clight.globalenv EntrySource.prog)
    (Callstate (Internal f_namespace_init) arguments Kstop before) trace
    (State fn (Scall opt (Evar _entry_prctl5 ty) args) k env temps memory) ->
  exists request request_type rest, args = Econst_int request request_type :: rest /\
    request <> Int.repr 22.
Proof.
  intro RUN. pose proof (namespace_lineage_prefix _ _ _ _ RUN) as [_ [CALL _]].
  change (avoids_requests [22] args = true) in CALL.
  destruct (avoids_requests_exact _ _ CALL) as [request [request_type [rest [ARGS NOT]]]].
  exists request, request_type, rest; split; auto. apply NOT; simpl; auto.
Qed.

Theorem namespace_syscall_no_bypass arguments before trace fn opt args k env temps memory ty :
  star step2 (Clight.globalenv EntrySource.prog)
    (Callstate (Internal f_namespace_init) arguments Kstop before) trace
    (State fn (Scall opt (Evar _syscall ty) args) k env temps memory) ->
  exists request request_type rest, args = Econst_int request request_type :: rest /\
    request <> Int.repr 101 /\ request <> Int.repr 157 /\ request <> Int.repr 317.
Proof.
  intro RUN. pose proof (namespace_lineage_prefix _ _ _ _ RUN) as [_ [CALL _]].
  destruct args as[|first supplied];[discriminate CALL|].
  destruct first;try discriminate CALL.
  change ((Int.unsigned i <? 1073741824) && avoids_requests [101;157;317](Econst_int i t::supplied)=true) in CALL.
  apply andb_true_iff in CALL as[CANONICAL CALL].
  destruct (avoids_requests_exact _ _ CALL) as [request [request_type [rest [ARGS NOT]]]].
  exists request, request_type, rest; split; auto.
  repeat split; apply NOT; simpl; auto.
Qed.

Theorem namespace_syscall_canonical_number arguments before trace fn opt args k env temps memory ty :
  star step2 (Clight.globalenv EntrySource.prog)
    (Callstate (Internal f_namespace_init) arguments Kstop before) trace
    (State fn (Scall opt (Evar _syscall ty) args) k env temps memory) ->
  exists request request_type rest,args=Econst_int request request_type::rest /\
    0<=Int.unsigned request<1073741824.
Proof.
  intro RUN;pose proof(namespace_lineage_prefix _ _ _ _ RUN)as[_[CALL _]].
  destruct args as[|first rest];[discriminate CALL|].
  destruct first;try discriminate CALL.
  change ((Int.unsigned i <? 1073741824) && avoids_requests [101;157;317](Econst_int i t::rest)=true)in CALL.
  apply andb_true_iff in CALL as[BOUND OTHER];apply Z.ltb_lt in BOUND.
  exists i,t,rest;split;[reflexivity|];pose proof(Int.unsigned_range i);lia.
Qed.
