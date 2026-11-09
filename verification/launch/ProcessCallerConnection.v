(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-entry.provenance: Import the actual caller's request history into ordinary Lean. *)
From Stdlib Require Import ZArith List Lia NArith.
From compcert Require Import Coqlib Integers AST Values Memory Clight.
From LeanImport Require Import Lean.
Require Import Machine.
From EntryProcess Require Import ProcessImport ProcessConnection ProcessTrace ProcessGlobalCalls ProcessCaller.
From EntryNamespace Require Import NamespaceMachine.
Import ListNotations.
Local Close Scope lean_scope.
Local Open Scope Z_scope.

Definition caller_request_nat(request:int):Lean.Nat:=Nat_of_nat(Z.to_nat(Int.unsigned request)).
Fixpoint caller_request_values(requests:list int):List_inst1 Lean.Nat:=match requests with
  |[]=>List_nil_inst1 Lean.Nat
  |request::rest=>List_cons_inst1 Lean.Nat(caller_request_nat request)(caller_request_values rest)end.

Theorem caller_history_ordinary_Lean requests:
  Forall(fun request=>tracer_request_allowed request=true)requests ->
  LeanCage_Entry_CallerRequestsAllowed(caller_request_values requests).
Proof.
  intro CHECKED;induction CHECKED;cbn[caller_request_values LeanCage_Entry_CallerRequestsAllowed];constructor.
  - apply checked_tracer_request_word;exact H.
  - exact IHCHECKED.
Qed.

Theorem caller_source_history_ordinary_Lean cell before events after:
  caller_source_machine before ->namespace_steps caller_ge cell before events after ->
  LeanCage_Entry_CallerRequestsAllowed(caller_request_values(flat_map caller_event_requests events)).
Proof. intros SOURCE RUN;apply caller_history_ordinary_Lean;eapply caller_actual_request_history;eassumption. Qed.

Theorem caller_namespace_history_ordinary_Lean cell arguments memory events after:
  namespace_steps caller_ge cell
    (live(Callstate(Ctypes.Internal EntrySource.f_namespace_init)arguments Kstop memory))events after ->
  LeanCage_Entry_CallerRequestsAllowed(caller_request_values(flat_map caller_event_requests events)).
Proof. intro RUN;eapply caller_source_history_ordinary_Lean;[apply caller_namespace_initial|exact RUN]. Qed.

Lemma caller_word_small request (limit:N):0<=Int.unsigned request<Z.of_N limit ->
  (caller_request_nat request<Nat_of_N limit)%Nat.
Proof.
  intro BOUND;apply Nat_lt_to_N_l;unfold N_of_Nat,caller_request_nat;rewrite nat2Natid.
  apply N.ltb_lt;lia.
Qed.

Lemma caller_word_different request code:
  0<=code<=Int.max_unsigned ->request<>Int.repr code ->
  Not(Lean.eq(caller_request_nat request)(Nat_of_nat(Z.to_nat code))).
Proof.
  intros RANGE DIFFERENT SAME.
  assert(EQUALITY:caller_request_nat request=Nat_of_nat(Z.to_nat code))by(destruct SAME;reflexivity).
  apply(f_equal nat_of_Nat)in EQUALITY;unfold caller_request_nat in EQUALITY;rewrite !nat2Natid in EQUALITY.
  assert(UNSIGNED:Int.unsigned request=code)by(pose proof(Int.unsigned_range request);lia).
  exfalso;apply DIFFERENT;rewrite <-(Int.repr_unsigned request),UNSIGNED;reflexivity.
Qed.

Lemma caller_double_nat value:nat_of_Nat(double value)=(2*nat_of_Nat value)%nat.
Proof. induction value;cbn[double nat_of_Nat];rewrite ?IHvalue;lia. Qed.

Local Opaque double.

Theorem caller_prctl_lineage_ordinary_Lean request:
  request<>Int.repr 22 ->LeanCage_Entry_CallerLineageAllowed(Nat_of_nat 2)(caller_request_nat request).
Proof.
  intro EXCLUDED;unfold LeanCage_Entry_CallerLineageAllowed.
  do 10 apply Lean.Or_inr;apply Lean.Or_inl;constructor;[constructor|]. constructor.
  - apply nat_le_Nat_le.
    cbn[nat_of_Nat].
    unfold caller_request_nat;rewrite nat2Natid at 1;cbn[OfNat_ofNat_inst1 instOfNatNat ofNat0];
      repeat rewrite caller_double_nat;cbn[nat_of_Nat];repeat rewrite caller_double_nat;cbn[nat_of_Nat].
    pose proof(Int.unsigned_range request)as RANGE;change(0<=Int.unsigned request<4294967296)in RANGE;lia.
  - exact(caller_word_different request 22 ltac:(cbn;lia)EXCLUDED).
Qed.

Theorem caller_syscall_lineage_ordinary_Lean request:
  Int.unsigned request<1073741824 ->request<>Int.repr 101 ->request<>Int.repr 157 ->request<>Int.repr 317 ->
  LeanCage_Entry_CallerLineageAllowed(Nat_of_nat 3)(caller_request_nat request).
Proof.
  intros BOUND PTRACE PRCTL SECCOMP;unfold LeanCage_Entry_CallerLineageAllowed.
  do 11 apply Lean.Or_inr;apply Lean.Or_inl;constructor;[constructor|]. constructor.
  - apply nat_le_Nat_le.
    cbn[nat_of_Nat].
    unfold caller_request_nat;rewrite nat2Natid at 1;cbn[OfNat_ofNat_inst1 instOfNatNat ofNat0];
      repeat rewrite caller_double_nat;cbn[nat_of_Nat];repeat rewrite caller_double_nat;cbn[nat_of_Nat].
    pose proof(Int.unsigned_range request)as RANGE;change(0<=Int.unsigned request<4294967296)in RANGE;lia.
  - constructor;[exact(caller_word_different request 101 ltac:(cbn;lia)PTRACE)|].
    constructor;[exact(caller_word_different request 157 ltac:(cbn;lia)PRCTL)|].
    exact(caller_word_different request 317 ltac:(cbn;lia)SECCOMP).
Qed.

Theorem caller_ptrace_lineage_ordinary_Lean request:
  tracer_request_allowed request=true ->request<>Int.repr 16896 ->
  LeanCage_Entry_CallerLineageAllowed(Nat_of_nat 6)(caller_request_nat request).
Proof.
  intros ALLOWED NOT_OPTIONS;unfold LeanCage_Entry_CallerLineageAllowed;do 12 apply Lean.Or_inr;apply Lean.Or_inl.
  constructor;[constructor|].
  destruct(tracer_request_exact request ALLOWED)as[SAME|[SAME|SAME]];subst request.
  - apply Lean.Or_inl;constructor.
  - contradiction.
  - apply Lean.Or_inr;constructor.
Qed.

Definition caller_options_nat(word:int64):Lean.Nat:=Nat_of_nat(Z.to_nat(Int64.unsigned word)).

Lemma caller_native_nat_eq left right:nat_of_Nat left=nat_of_Nat right ->Lean.eq left right.
Proof. intro SAME;rewrite <-(Nat2natid left),<-(Nat2natid right);rewrite SAME;constructor. Qed.

Theorem caller_options_word_ordinary_Lean word:word=Int64.repr 1048592 ->
  LeanCage_Entry_TracerOptionsAllowed(caller_options_nat word).
Proof.
  intro WORD;subst word;unfold LeanCage_Entry_TracerOptionsAllowed;apply Lean.Or_inr.
  apply caller_native_nat_eq;unfold caller_options_nat;rewrite nat2Natid.
  rewrite Int64.unsigned_repr by(change Int64.max_unsigned with 18446744073709551615;lia).
  repeat first[rewrite caller_double_nat|progress(cbn[nat_of_Nat OfNat_ofNat_inst1 instOfNatNat ofNat0])].
  lia.
Qed.

Theorem caller_pending_options_ordinary_Lean cell before events child address word k memory:
  caller_source_machine before ->namespace_steps caller_ge cell before events
    (live(Callstate ProcessMachine.process_ptrace_definition
      [Vint(Int.repr 16896);Vint child;address;Vlong word]k memory)) ->
  LeanCage_Entry_TracerOptionsAllowed(caller_options_nat word).
Proof.
  intros SOURCE RUN;apply caller_options_word_ordinary_Lean.
  pose proof(caller_actual_pending_options _ _ _ _ _ _ _ _ SOURCE RUN)as WORD;inversion WORD;reflexivity.
Qed.

Theorem caller_setoptions_lineage_ordinary_Lean word:word=Int64.repr 1048592 ->
  LeanCage_Entry_CallerLineageAllowed(Nat_of_nat 13)(caller_options_nat word).
Proof.
  intro WORD;unfold LeanCage_Entry_CallerLineageAllowed;do 13 apply Lean.Or_inr.
  constructor;[constructor|apply caller_options_word_ordinary_Lean;exact WORD].
Qed.
