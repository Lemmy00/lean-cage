(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.encoding: Complete scalar tail after actual digest copying. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Slice Machine ClightSteps WriteAll StoreSteps LocalAccess CallAccess Library LibraryMachine Writers WriteBytes
  CallPaths FreshMemory ResultLayout SourceReach FrameRecord SenderSource SenderAccess
  BytePatch SenderStorage SenderOperations SenderEncodingPrefix SenderCopies.
Import ListNotations.
Open Scope Z_scope.
Definition sender_tail_bytes sequence r digest :=
  patch_bytes (patch_bytes (patch_bytes (patch_bytes (sender_prefix_bytes sequence r) 104 digest)
    136 (frame_word64 (fr_oom r))) 144 (frame_word64 (fr_pids r))) 152 (frame_word32 (fr_export_error r)).
Definition sender_tail_result base result_local bytes_local r digest sequence fd k s :=
  exists le after, s=State f_send_frame sender_reporting k (sender_env result_local bytes_local) le after /\
    le ! _fd=Some (Vint fd) /\ le ! _sequence=Some (Vlong sequence) /\
    sender_storage base result_local bytes_local r digest (sender_tail_bytes sequence r digest) after.
Theorem sender_tail_source : forall base m result_local bytes_local r digest sequence fd k le,
  ~ Mem.valid_block base bytes_local -> result_local<>bytes_local ->
  sender_storage base result_local bytes_local r digest (patch_bytes (sender_prefix_bytes sequence r) 104 digest) m ->
  length (sender_prefix_bytes sequence r)=160%nat ->
  le ! _fd=Some (Vint fd) -> le ! _sequence=Some (Vlong sequence) ->
  source_reaches result_ge (old_memory base)
    (sender_tail_result base result_local bytes_local r digest sequence fd k)
    (State f_send_frame sender_after_digest k (sender_env result_local bytes_local) le m).
Proof.
  intros base m result_local bytes_local r digest sequence fd k le FRESH NE STORAGE PREFIXLEN FD SEQ.
  pose proof (proj1 (proj2 STORAGE)) as [_ [_ [_ [_ [DIGESTLEN _]]]]].
  sender_keep_length STORAGE.
  destruct sender_encoding_symbols as [b32 [b64 [bc [S32 [F32 [S64 [F64 [CS CF]]]]]]]].
  let body := eval cbv [sender_after_digest sender_after_zero sender_zero_tail statement_drop f_send_frame fn_body] in sender_after_digest in
    change (source_reaches result_ge (old_memory base)
      (sender_tail_result base result_local bytes_local r digest sequence fd k)
      (State f_send_frame body k (sender_env result_local bytes_local) le m)).
  Ltac sender_tail_run base result_local bytes_local r digest FRESH NE S32 F32 S64 F64 :=
    lazymatch goal with
    | |- source_reaches ?ge ?P ?Q (State ?f (Ssequence (Ssequence (Ssequence (Sifthenelse _ _ _) _) _) _) ?cont ?env ?temps ?memory) =>
      change (source_reaches ge P Q (State f sender_reporting cont env temps memory));
      apply source_reaches_done;
        [lazymatch goal with ST : sender_storage _ _ _ _ _ _ _ |- _=>exact (proj1 ST) end|];
      unfold sender_tail_result;eexists;eexists;split;[reflexivity|];
      split;[WriteAll.lookup|];split;[WriteAll.lookup|];
      unfold sender_tail_bytes;lazymatch goal with ST : sender_storage _ _ _ _ _ _ _ |- _ => exact ST end
    | |- source_reaches _ _ _ (State _ (Sset _ (Efield _ _ _)) _ _ _ ?m) =>
      lazymatch goal with ST : sender_storage _ _ _ _ _ _ m |- _ =>
        let OLD:=constr:(proj1 ST) in let OWN:=constr:(proj1 (proj2 ST)) in
        eapply source_reaches_prepend;[exact OLD|eapply certified_set_edge;sender_field r OWN|]
      end;sender_tail_run base result_local bytes_local r digest FRESH NE S32 F32 S64 F64
    | |- source_reaches _ _ _ (State _ (Scall _ (Evar _put32 _) _) _ _ _ ?m) =>
      lazymatch goal with ST : sender_storage _ _ _ _ _ ?bytes m |- _ =>
        let OLD:=constr:(proj1 ST) in sender_reach_call OLD S32 F32;cbn [Val.load_result ScalarMemory.scalar_chunk ScalarMemory.scalar_value cell32];
        lazymatch goal with |- source_reaches _ _ _ (Callstate _ [Vptr _ ?offset;Vint ?x] ?call _) =>
          let index:=eval vm_compute in (Z.to_nat (Ptrofs.unsigned offset)) in
          change offset with (Ptrofs.repr (Z.of_nat index));
          let after:=fresh "after" in let PATH:=fresh "PATH" in let NEXT:=fresh "STORAGE" in
          destruct (sender_writer32 base m result_local bytes_local r digest bytes index x call FRESH NE ST
            ltac:(sender_bytes_length) ltac:(lia) I) as [after [PATH NEXT]];
          eapply source_reaches_path;[exact PATH|];sender_keep_length NEXT;clear ST PATH
        end
      end;sender_tail_run base result_local bytes_local r digest FRESH NE S32 F32 S64 F64
    | |- source_reaches _ _ _ (State _ (Scall _ (Evar _put64 _) _) _ _ _ ?m) =>
      lazymatch goal with ST : sender_storage _ _ _ _ _ ?bytes m |- _ =>
        let OLD:=constr:(proj1 ST) in sender_reach_call OLD S64 F64;cbn [Val.load_result ScalarMemory.scalar_chunk ScalarMemory.scalar_value cell64];
        lazymatch goal with |- source_reaches _ _ _ (Callstate _ [Vptr _ ?offset;Vlong ?x] ?call _) =>
          let index:=eval vm_compute in (Z.to_nat (Ptrofs.unsigned offset)) in
          change offset with (Ptrofs.repr (Z.of_nat index));
          let after:=fresh "after" in let PATH:=fresh "PATH" in let NEXT:=fresh "STORAGE" in
          destruct (sender_writer64 base m result_local bytes_local r digest bytes index x call FRESH NE ST
            ltac:(sender_bytes_length) ltac:(lia) I) as [after [PATH NEXT]];
          eapply source_reaches_path;[exact PATH|];sender_keep_length NEXT;clear ST PATH
        end
      end;sender_tail_run base result_local bytes_local r digest FRESH NE S32 F32 S64 F64
    | |- source_reaches _ _ _ ?s =>
      let m:=eval cbn [memory_of] in (memory_of s) in
      lazymatch goal with ST : sender_storage _ _ _ _ _ _ m |- _=>
        let OLD:=constr:(proj1 ST) in sender_reach_route OLD end;sender_tail_run base result_local bytes_local r digest FRESH NE S32 F32 S64 F64
    end.
  sender_tail_run base result_local bytes_local r digest FRESH NE S32 F32 S64 F64.
Qed.
