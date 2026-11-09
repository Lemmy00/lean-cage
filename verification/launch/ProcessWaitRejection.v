(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Wrong task identities and non-SIGSTOP statuses take actual error returns. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import IO Machine ClightSteps StoreSteps WriteAll ErrorNumber.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessAllocation ProcessStructure ProcessReturns
  ProcessWait ProcessStatus.
Import ListNotations.
Open Scope Z_scope.

Definition admission_stop_matches child got word :=
  Int.eq got child && admission_is_stopped word && admission_is_sigstop word.

Lemma admission_wait_values le got child status offset :
  le!_child=Some(Vint child) ->le!_status=Some(Vptr status offset) ->
  (admission_wait_return_env le got)!_child=Some(Vint child) /\
  (admission_wait_return_env le got)!_status=Some(Vptr status offset) /\
  (admission_wait_return_env le got)!_got=Some(Vint got).
Proof.
  intros CHILD STATUS;unfold admission_wait_return_env;repeat split;
    repeat rewrite PTree.gso by discriminate;try assumption;apply PTree.gss.
Qed.

Theorem admission_rejected_status_source locals le memory k got child status offset word :
  0<=Int.signed got ->le!_child=Some(Vint child) ->le!_status=Some(Vptr status offset) ->
  Mem.loadv Mint32 memory(Vptr status offset)=Some(Vint word) ->
  admission_stop_matches child got word=false ->
  exists count final continuation,
    call_cont continuation=call_cont k /\
    store_path admission_ge(fun _=>True)
      (Returnstate(Vint got)(admission_wait_call_cont(admission_env locals)le k)memory)count
      (State f_admit_child admission_failure continuation(admission_env locals)final memory).
Proof.
  intros POSITIVE CHILD STATUS LOAD REJECTED.
  destruct(admission_wait_values le got child status offset CHILD STATUS)as[CHILD'[STATUS' GOT]].
  pose proof(admission_wait_positive_source(admission_env locals)le memory got k POSITIVE)as RETURN.
  pose proof(admission_identity_guard(admission_env locals)(admission_wait_return_env le got)
    memory k got child GOT CHILD')as IDENTITY.
  destruct(Int.eq got child)eqn:SAME.
  -
    pose proof(admission_stopped_guard(admission_env locals)(admission_wait_return_env le got)
      memory k status offset word STATUS' LOAD)as STOPPED.
    destruct(admission_is_stopped word)eqn:STOP.
    +
      assert(STATUS'':(admission_stopped_env(admission_wait_return_env le got)word)!_status=
        Some(Vptr status offset)).
      { unfold admission_stopped_env;rewrite PTree.gso by discriminate;exact STATUS'. }
      pose proof(admission_stopsig_guard(admission_env locals)
        (admission_stopped_env(admission_wait_return_env le got)word)
        memory k status offset word STATUS'' LOAD)as SIGNAL.
      assert(SIGNAL_BAD:admission_is_sigstop word=false).
      { unfold admission_stop_matches in REJECTED;rewrite SAME,STOP in REJECTED;exact REJECTED. }
      rewrite SIGNAL_BAD in SIGNAL.
      eexists;exists(admission_stopsig_env(admission_stopped_env(admission_wait_return_env le got)word)word),
        (Kseq(admission_tail 4(fn_body f_admit_child))k);split;[reflexivity|].
      eapply store_path_trans;[exact RETURN|].
      eapply store_path_trans;[exact IDENTITY|].
      eapply store_path_trans;[exact STOPPED|exact SIGNAL].
    + eexists;exists(admission_stopped_env(admission_wait_return_env le got)word),
        (Kseq(admission_tail 3(fn_body f_admit_child))k);split;[reflexivity|].
      eapply store_path_trans;[exact RETURN|].
      eapply store_path_trans;[exact IDENTITY|exact STOPPED].
  - eexists;exists(admission_wait_return_env le got),
      (Kseq(admission_tail 2(fn_body f_admit_child))k);split;[reflexivity|].
    eapply store_path_trans;[exact RETURN|exact IDENTITY].
Qed.

Lemma admission_failed_errno_readback cell status offset before error after :
  process_wait_effect cell status offset before(wait_failed error)after ->
  entry_errno_ready cell after ->initialized_errno cell after error.
Proof.
  intros EFFECT[other[LOW[HIGH[ACCESS OLD]]]].
  inversion EFFECT;subst;unfold initialized_errno.
  split;[exact LOW|]. split;[exact HIGH|]. split;[exact ACCESS|].
  erewrite Mem.load_store_same by eassumption;reflexivity.
Qed.

Lemma admission_wait_status_readback cell status offset before got word after :
  status<>tls_block cell ->
  process_wait_effect cell status offset before(wait_status got word)after ->
  1<=Int.signed got /\Mem.loadv Mint32 after(Vptr status offset)=Some(Vint word).
Proof.
  intros SEPARATE EFFECT;inversion EFFECT;subst;split;[lia|].
  match goal with STORE:Mem.storev Mint32 _ _ _=Some _|-_=>
    unfold Mem.storev in STORE;destruct(zle _ _)as[BOUND|];[|discriminate] end.
  unfold Mem.loadv;destruct(zle _ _)as[BOUND'|];[|congruence].
  match goal with ERRNO:errno_change _ _ _ _|-_=>inversion ERRNO;subst end.
  - erewrite Mem.load_store_same by eassumption;reflexivity.
  - erewrite Mem.load_store_other;[|exact H|left;exact SEPARATE].
    erewrite Mem.load_store_same by eassumption;reflexivity.
Qed.

Theorem admission_errno_rejoins cell locals le memory child status offset error :
  1<=Int.signed child ->le!_child=Some(Vint child) ->le!_status=Some(Vptr status offset) ->
  initialized_errno cell memory error ->
  (exists count,
    store_path admission_ge(fun _=>True)
      (Returnstate(Vptr(tls_block cell)(Ptrofs.repr(tls_offset cell)))
        (admission_errno_cont(admission_env locals)le Kstop)memory)count
      (Callstate process_wait_definition[Vint child;Vptr status offset;Vint Int.zero]
        (admission_wait_call_cont(admission_env locals)(admission_errno_env cell le error)Kstop)memory)) \/
  (exists count final continuation,call_cont continuation=Kstop /\
    store_path admission_ge(fun _=>True)
      (Returnstate(Vptr(tls_block cell)(Ptrofs.repr(tls_offset cell)))
        (admission_errno_cont(admission_env locals)le Kstop)memory)count
      (State f_admit_child admission_failure continuation(admission_env locals)final memory)).
Proof.
  intros POSITIVE CHILD STATUS ERRNO.
  pose proof(admission_errno_retry_source cell(admission_env locals)le memory Kstop error ERRNO)as RETRY.
  assert(CHILD':(admission_errno_env cell le error)!_child=Some(Vint child)).
  { unfold admission_errno_env,admission_wait_saved;repeat rewrite PTree.gso by discriminate;exact CHILD. }
  assert(STATUS':(admission_errno_env cell le error)!_status=Some(Vptr status offset)).
  { unfold admission_errno_env,admission_wait_saved;repeat rewrite PTree.gso by discriminate;exact STATUS. }
  destruct(Int.eq error(Int.repr 4))eqn:INTERRUPTED.
  - left;eexists;eapply store_path_trans;[exact RETRY|].
    apply admission_wait_call_source;
      [apply admission_nonlocal_binding;discriminate|exact CHILD'|exact STATUS'].
  - assert(GOT:(admission_errno_env cell le error)!_got=Some(Vint Int.mone)).
    { unfold admission_errno_env,admission_wait_saved;WriteAll.lookup. }
    assert(DIFFERENT:Int.eq Int.mone child=false).
    { apply Int.eq_false;intro SAME;apply(f_equal Int.signed)in SAME;change(-1=Int.signed child)in SAME;lia. }
    pose proof(admission_identity_guard(admission_env locals)(admission_errno_env cell le error)
      memory Kstop Int.mone child GOT CHILD')as IDENTITY.
    rewrite DIFFERENT in IDENTITY.
    right;eexists;exists(admission_errno_env cell le error),(Kseq(admission_tail 2(fn_body f_admit_child))Kstop).
    split;[reflexivity|]. eapply store_path_trans;[exact RETRY|].
    admission_route;exact IDENTITY.
Qed.
