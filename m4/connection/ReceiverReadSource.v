(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-receiver.reads: Source-exact receiver loop, retries, EOF and failure branches. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events
  Globalenvs Errors Ctypes Ctypesdefs Cop Clight.
Require Import Slice IO Machine ClightSteps StoreSteps WriteAll LocalAccess CallAccess
  ResultLayout SourceReach DecoderControl ReceiverSource.
Import ListNotations.
Open Scope Z_scope.

Definition receiver_fd_load := Sset _t'27
  (Ederef (Ebinop Oadd (Evar _pipefd (tarray tint 1))
    (Econst_int Int.zero tint) (tptr tint)) tint).
Definition receiver_read_call := Scall (Some _t'1)
  (Evar _read (Tfunction [tint;tptr tvoid;tulong] tlong cc_default))
  [Etempvar _t'27 tint;
   Ebinop Oadd (Evar _failure_bytes (tarray tuchar 9)) (Etempvar _used tulong) (tptr tuchar);
   Ebinop Osub (Esizeof (tarray tuchar 9) tulong) (Etempvar _used tulong) tulong].
Definition receiver_save_read := Sset _n (Etempvar _t'1 tlong).
Definition receiver_errno_call := Scall (Some _t'3)
  (Evar ___errno_location (Tfunction [] (tptr tint) cc_default)) [].
Definition receiver_errno_load := Ssequence
  (Sset _t'26 (Ederef (Etempvar _t'3 (tptr tint)) tint))
  (Sset _t'2 (Ecast (Ebinop Oeq (Etempvar _t'26 tint)
    (Econst_int (Int.repr 4) tint) tint) tbool)).
Definition receiver_errno_test := Sifthenelse
  (Ebinop Olt (Etempvar _n tlong) (Econst_int Int.zero tint) tint)
  (Ssequence receiver_errno_call receiver_errno_load) (Sset _t'2 (Econst_int Int.zero tint)).
Definition receiver_continue := Sifthenelse (Etempvar _t'2 tint) Scontinue Sskip.
Definition receiver_failed := Sifthenelse
  (Ebinop Olt (Etempvar _n tlong) (Econst_int Int.zero tint) tint)
  (Ssequence (Sset _bad (Econst_int Int.one tint)) Sbreak) Sskip.
Definition receiver_eof := Sifthenelse (Eunop Onotbool (Etempvar _n tlong) tint) Sbreak Sskip.
Definition receiver_advance := Sset _used
  (Ebinop Oadd (Etempvar _used tulong) (Ecast (Etempvar _n tlong) tulong) tulong).
Definition receiver_read_rest := Ssequence receiver_failed (Ssequence receiver_eof receiver_advance).
Definition receiver_read_tail := Ssequence (Ssequence receiver_errno_test receiver_continue) receiver_read_rest.
Definition receiver_read_cont b le k := Kcall (Some _t'1) f_m4_collect_failure (receiver_env b) le
  (Kseq receiver_save_read (Kseq receiver_read_tail (receiver_body_cont k))).
Definition receiver_errno_cont b le k := Kcall (Some _t'3) f_m4_collect_failure (receiver_env b) le
  (Kseq receiver_errno_load (Kseq receiver_continue (Kseq receiver_read_rest (receiver_body_cont k)))).
Definition receiver_read_state b cell fd used le k m :=
  Callstate (External (io_function reading) [tint;tptr tvoid;tulong] tlong cc_default)
    (request_args (receiver_request b cell fd used)) (receiver_read_cont b le k) m.
Definition receiver_errno_state b le k m :=
  Callstate (External errno_function [] (tptr tint) cc_default) [] (receiver_errno_cont b le k) m.

Theorem receiver_loop_source : receiver_loop = Sloop
  (Ssequence (Sifthenelse (Ebinop Olt (Etempvar _used tulong)
      (Esizeof (tarray tuchar 9) tulong) tint) Sskip Sbreak)
    (Ssequence (Ssequence (Ssequence receiver_fd_load receiver_read_call) receiver_save_read)
      receiver_read_tail)) Sskip.
Proof. reflexivity. Qed.

Theorem receiver_read_symbol : exists b,
  Genv.find_symbol result_ge _read=Some b /\
  Genv.find_funct result_ge (Vptr b Ptrofs.zero)=
    Some (External (io_function reading) [tint;tptr tvoid;tulong] tlong cc_default).
Proof. eexists;split;vm_compute;reflexivity. Qed.
Theorem receiver_errno_symbol : exists b,
  Genv.find_symbol result_ge ___errno_location=Some b /\
  Genv.find_funct result_ge (Vptr b Ptrofs.zero)=
    Some (External errno_function [] (tptr tint) cc_default).
Proof. eexists;split;vm_compute;reflexivity. Qed.

Lemma receiver_sizeof : forall ge e le m ty resultty,
  expression_value ge e le m (Esizeof ty resultty) (Vptrofs (Ptrofs.repr (sizeof ge ty))).
Proof.
  intros;split;[constructor|]. intros other E;inversion E;subst;try reflexivity.
  match goal with L : eval_lvalue _ _ _ _ _ _ _ _ |- _=>inversion L end.
Qed.

Ltac receiver_location := first
  [eapply local_location_value;unfold receiver_env;WriteAll.lookup
  |eapply pointer_location_value;receiver_expression]
with receiver_expression := first
  [solve [apply old_expression_value;WriteAll.expression]
  |apply receiver_sizeof
  |eapply location_read_value;[receiver_location|apply deref_loc_reference;reflexivity]
  |eapply binary_expression_value;[receiver_expression|receiver_expression|]
  |eapply cast_expression_value;[receiver_expression|]];try reflexivity.
Ltac receiver_route := eapply store_next;
  [reflexivity|apply unchanged_store_edge;WriteAll.structural|].
Ltac receiver_set := eapply store_next;
  [reflexivity|apply unchanged_store_edge;eapply edge_set;decoder_control_expression|].
Ltac receiver_branch choice := eapply store_next;
  [reflexivity|apply unchanged_store_edge;eapply edge_if with (b:=choice);
    [decoder_control_expression|]|].

Lemma receiver_loop_less : forall used,0<=used<9 ->
  Int64.ltu (Int64.repr used) (Int64.repr 9)=true.
Proof.
  intros used RANGE;unfold Int64.ltu;rewrite !unsigned_small by lia.
  destruct (zlt used 9);[reflexivity|lia].
Qed.

Theorem receiver_loop_to_read : forall b cell fd used le k m,
  le!_used=Some(Vlong(Int64.repr used)) ->
  Mem.load Mint32 m (rb_pipe b) 0=Some(Vint fd) -> 0<=used<9 ->
  exists count,store_path result_ge (fun after=>after=m)
    (receiver_loop_state b le k m) count
    (receiver_read_state b cell fd used (PTree.set _t'27 (Vint fd) le) k m).
Proof.
  intros b cell fd used le k m USED FD RANGE.
  destruct receiver_read_symbol as [symbol [SYM FUN]].
  eexists;unfold receiver_loop_state;rewrite receiver_loop_source.
  receiver_route. receiver_route.
  eapply store_next;[reflexivity|eapply certified_if_edge with (b:=true)|].
  - eapply binary_expression_value;[receiver_expression|apply receiver_sizeof|reflexivity].
  - change (bool_val (Val.of_bool (Int64.ltu (Int64.repr used) (Int64.repr 9))) tint m=Some true).
    rewrite receiver_loop_less by exact RANGE;reflexivity.
  - receiver_route. receiver_route. receiver_route. receiver_route.
    unfold receiver_fd_load.
    eapply store_next;[reflexivity|eapply certified_set_edge|].
    + eapply location_read_value;[receiver_location|].
      apply deref_loc_value with (chunk:=Mint32);[reflexivity|exact FD].
    + receiver_route. unfold receiver_read_call,receiver_read_state,receiver_read_cont,
        receiver_body_cont,receiver_loop_test.
      eapply store_next;[reflexivity| |].
      * eapply certified_call_edge;[reflexivity|
          apply old_expression_value;eapply value_function;
            [unfold receiver_env;cbn;reflexivity|exact SYM|reflexivity]| |exact FUN|reflexivity].
        unfold request_args,receiver_request;cbn [descriptor buffer_block buffer_offset requested].
        eapply cons_argument_values;[receiver_expression|reflexivity|].
        eapply cons_argument_values with (v:=Vptr (rb_bytes b) (Ptrofs.repr used)).
        -- eapply binary_expression_value;[receiver_expression|receiver_expression|].
           change (Some (Vptr (rb_bytes b) (Ptrofs.add Ptrofs.zero
             (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_int64 (Int64.repr used)))))=
               Some(Vptr (rb_bytes b) (Ptrofs.repr used))).
           rewrite Ptrofs.add_zero_l,Ptrofs.mul_commut,Ptrofs.mul_one.
           unfold Ptrofs.of_int64;rewrite unsigned_small by lia;reflexivity.
        -- reflexivity.
        -- eapply cons_argument_values with (v:=Vlong (Int64.repr (9-used))).
           ++ eapply binary_expression_value;[|receiver_expression|].
              ** apply receiver_sizeof.
              ** change (Some(Vlong(Int64.sub (Int64.repr 9) (Int64.repr used)))=
                   Some(Vlong(Int64.repr (9-used)))).
                 rewrite count_decrease by lia;reflexivity.
           ++ reflexivity.
           ++ apply no_argument_values.
      * apply store_done;reflexivity.
Qed.

Definition receiver_kept (before after : temp_env) := forall id,
  In id [__res;_entered;_leader_done;_leader_status] -> after!id=before!id.
Ltac receiver_keep := unfold receiver_kept;intros id IN;
  cbn in IN;repeat destruct IN as [IN|IN];try contradiction;subst id;WriteAll.lookup.

Theorem receiver_full_to_close : forall b le k m,
  le!_used=Some(Vlong(Int64.repr 9)) ->
  exists count,store_path result_ge (fun after=>after=m)
    (receiver_loop_state b le k m) count (receiver_closed_state b le k m).
Proof.
  intros b le k m USED;eexists;unfold receiver_loop_state;rewrite receiver_loop_source.
  receiver_route. receiver_route.
  eapply store_next;[reflexivity|eapply certified_if_edge with(b:=false)|].
  - eapply binary_expression_value;[receiver_expression|apply receiver_sizeof|reflexivity].
  - reflexivity.
  - receiver_route. receiver_route. receiver_route. apply store_done;reflexivity.
Qed.

Definition receiver_saved le reply :=
  PTree.set _n (Vlong(returned reply)) (PTree.set _t'1 (Vlong(returned reply)) le).
Theorem receiver_read_to_errno : forall b le k m error,
  exists count,store_path result_ge (fun after=>after=m)
    (Returnstate (Vlong(returned(failure error))) (receiver_read_cont b le k) m) count
    (receiver_errno_state b (receiver_saved le (failure error)) k m).
Proof.
  intros b le k m error;destruct receiver_errno_symbol as [symbol [SYM FUN]].
  eexists;unfold receiver_read_cont,receiver_errno_state,receiver_errno_cont,receiver_saved,
    receiver_read_tail,receiver_errno_test,receiver_errno_call,receiver_save_read.
  receiver_route. receiver_route. receiver_set. receiver_route. receiver_route. receiver_route.
  receiver_branch true;[reflexivity|]. receiver_route.
  eapply store_next;[reflexivity| |].
  - eapply certified_call_edge;[reflexivity|
      apply old_expression_value;eapply value_function;
        [unfold receiver_env;cbn;reflexivity|exact SYM|reflexivity]|
      apply no_argument_values|exact FUN|reflexivity].
  - apply store_done;reflexivity.
Qed.

Theorem receiver_positive_to_loop : forall b le k m used bytes error,
  le!_used=Some(Vlong(Int64.repr used)) ->
  0<=used<9 -> 0<Z.of_nat(length bytes)<=9-used ->
  exists count next,receiver_kept le next /\ next!_bad=le!_bad /\
    next!_used=Some(Vlong(Int64.repr(used+Z.of_nat(length bytes)))) /\
    store_path result_ge (fun after=>after=m)
      (Returnstate (Vlong(returned(transfer bytes error))) (receiver_read_cont b le k) m) count
      (receiver_loop_state b next k m).
Proof.
  intros b le k m used bytes error USED RANGE SIZE.
  eexists;eexists;split;[|split;[|split]].
  4:{
    unfold receiver_read_cont,receiver_save_read,receiver_read_tail,receiver_errno_test,
      receiver_continue,receiver_read_rest,receiver_failed,receiver_eof,receiver_advance,
      receiver_loop_state.
    receiver_route. receiver_route. receiver_set. receiver_route. receiver_route. receiver_route.
    receiver_branch false.
    { change (bool_val (Val.of_bool (Int64.lt (Int64.repr(Z.of_nat(length bytes))) Int64.zero)) tint m=Some false).
      rewrite nonnegative_lt by lia;reflexivity. }
    receiver_set. receiver_route. receiver_branch false;[reflexivity|].
    receiver_route. receiver_route. receiver_branch false.
    { change (bool_val (Val.of_bool (Int64.lt (Int64.repr(Z.of_nat(length bytes))) Int64.zero)) tint m=Some false).
      rewrite nonnegative_lt by lia;reflexivity. }
    receiver_route. receiver_route. receiver_branch false.
    { rewrite Bool.negb_involutive.
      change (bool_val (Val.of_bool (Int64.eq (Int64.repr(Z.of_nat(length bytes))) Int64.zero)) tint m=Some false).
      rewrite int64_nonzero by lia;reflexivity. }
    receiver_route. receiver_set. receiver_route. receiver_route.
    apply store_done;reflexivity.
  }
  - receiver_keep.
  - WriteAll.lookup.
  - rewrite PTree.gss;f_equal;f_equal;unfold Int64.add;cbn [returned];rewrite !unsigned_small by lia;reflexivity.
Qed.

Theorem receiver_zero_to_close : forall b le k m used error,
  le!_used=Some(Vlong(Int64.repr used)) ->
  exists count next,receiver_kept le next /\ next!_bad=le!_bad /\
    next!_used=Some(Vlong(Int64.repr used)) /\
    store_path result_ge (fun after=>after=m)
      (Returnstate (Vlong(returned(zero error))) (receiver_read_cont b le k) m) count
      (receiver_closed_state b next k m).
Proof.
  intros b le k m used error USED;eexists;eexists;split;[|split;[|split]].
  4:{
    unfold receiver_read_cont,receiver_save_read,receiver_read_tail,receiver_errno_test,
      receiver_continue,receiver_read_rest,receiver_failed,receiver_eof,
      receiver_closed_state.
    receiver_route. receiver_route. receiver_set. receiver_route. receiver_route. receiver_route.
    receiver_branch false;[reflexivity|]. receiver_set. receiver_route.
    receiver_branch false;[reflexivity|]. receiver_route. receiver_route.
    receiver_branch false;[reflexivity|]. receiver_route. receiver_route.
    receiver_branch true;[reflexivity|]. receiver_route. receiver_route. receiver_route.
    apply store_done;reflexivity.
  }
  - receiver_keep.
  - WriteAll.lookup.
  - WriteAll.lookup.
Qed.


Theorem receiver_errno_retry_to_loop : forall b cell le k m used,
  le!_used=Some(Vlong(Int64.repr used)) -> le!_n=Some(Vlong Int64.mone) ->
  Mem.loadv Mint32 m (Vptr (tls_block cell) (Ptrofs.repr(tls_offset cell)))=Some(Vint(Int.repr 4)) ->
  exists count next,receiver_kept le next /\ next!_bad=le!_bad /\
    next!_used=Some(Vlong(Int64.repr used)) /\
    store_path result_ge (fun after=>after=m)
      (Returnstate (Vptr (tls_block cell) (Ptrofs.repr(tls_offset cell))) (receiver_errno_cont b le k) m) count
      (receiver_loop_state b next k m).
Proof.
  intros b cell le k m used USED N LOAD;eexists;eexists;split;[|split;[|split]].
  4:{
    unfold receiver_errno_cont,receiver_errno_load,receiver_continue,receiver_loop_state.
    receiver_route. receiver_route. receiver_route.
    eapply store_next;[reflexivity|apply unchanged_store_edge;eapply edge_set|
      ].
    - eapply value_load;[decoder_control_expression|reflexivity|exact LOAD].
    - receiver_route. receiver_set. receiver_route. receiver_branch true;[reflexivity|].
      receiver_route. receiver_route. receiver_route. apply store_done;reflexivity.
  }
  - receiver_keep.
  - WriteAll.lookup.
  - WriteAll.lookup.
Qed.

Theorem receiver_errno_failure_to_close : forall b cell le k m used error,
  le!_used=Some(Vlong(Int64.repr used)) -> le!_n=Some(Vlong Int64.mone) -> error<>Int.repr 4 ->
  Mem.loadv Mint32 m (Vptr (tls_block cell) (Ptrofs.repr(tls_offset cell)))=Some(Vint error) ->
  exists count next,receiver_kept le next /\ next!_bad=Some(Vint Int.one) /\
    next!_used=Some(Vlong(Int64.repr used)) /\
    store_path result_ge (fun after=>after=m)
      (Returnstate (Vptr (tls_block cell) (Ptrofs.repr(tls_offset cell))) (receiver_errno_cont b le k) m) count
      (receiver_closed_state b next k m).
Proof.
  intros b cell le k m used error USED N NE LOAD;eexists;eexists;split;[|split;[|split]].
  4:{
    unfold receiver_errno_cont,receiver_errno_load,receiver_continue,receiver_read_rest,receiver_failed,
      receiver_closed_state.
    receiver_route. receiver_route. receiver_route.
    eapply store_next;[reflexivity|apply unchanged_store_edge;eapply edge_set|].
    - eapply value_load;[decoder_control_expression|reflexivity|exact LOAD].
    - receiver_route.
      eapply store_next;[reflexivity|apply unchanged_store_edge;eapply edge_set with(v:=Vint Int.zero)|].
      + eapply value_cast;[eapply value_binary;[decoder_control_expression|decoder_control_expression|reflexivity]|].
        change (sem_cast (Val.of_bool (Int.eq error (Int.repr 4))) tint tbool m=Some(Vint Int.zero)).
        rewrite Int.eq_false by exact NE;reflexivity.
      + receiver_route. receiver_branch false;[reflexivity|]. receiver_route. receiver_route.
        receiver_branch true;[reflexivity|]. receiver_route. receiver_set.
        receiver_route. receiver_route. receiver_route. receiver_route.
        apply store_done;reflexivity.
  }
  - receiver_keep.
  - WriteAll.lookup.
  - WriteAll.lookup.
Qed.

Lemma receiver_saved_registers : forall le reply,
  receiver_kept le (receiver_saved le reply) /\
  (receiver_saved le reply)!_used=le!_used /\
  (receiver_saved le reply)!_bad=le!_bad /\
  (receiver_saved le reply)!_n=Some(Vlong(returned reply)).
Proof. intros;unfold receiver_saved;split;[receiver_keep|]. repeat split;WriteAll.lookup. Qed.
