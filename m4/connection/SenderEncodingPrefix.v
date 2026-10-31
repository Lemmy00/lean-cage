(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.encoding: Actual header and scalar encoding up to the digest copy. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Slice Machine ClightSteps WriteAll StoreSteps LocalAccess CallAccess Library LibraryMachine Writers WriteBytes
  CallPaths FreshMemory ResultLayout DecoderValidity SourceReach FrameRecord SenderSource
  SenderAccess BytePatch SenderStorage SenderOperations.
Import ListNotations.
Open Scope Z_scope.
Definition sender_after_magic := statement_drop 1 sender_after_zero.
Definition sender_digest_tail := statement_drop 19 sender_after_zero.
Definition sender_reporting := statement_drop 23 sender_after_zero.
Definition sender_magic_bytes := frame_magic ++ repeat Byte.zero 156.
Definition sender_prefix_bytes sequence r := fold_left
  (fun bytes change => patch_bytes bytes (fst change) (snd change))
  [(4%nat,[Byte.repr 1]);(6%nat,[Byte.repr (Int.unsigned (fr_kind r))]);
   (8%nat,frame_word64 (fr_run r));(16%nat,frame_word64 sequence);(24%nat,frame_word32 (Int.repr 128));
   (32%nat,frame_word32 (fr_stage r));(36%nat,frame_word32 (fr_detail r));(40%nat,frame_word32 (fr_entry r));
   (44%nat,frame_word32 (fr_clean r));(48%nat,frame_word32 (fr_triggers r));(52%nat,frame_word32 (fr_uid r));
   (56%nat,frame_word64 (fr_cpu r));(64%nat,frame_word64 (fr_peak r));(72%nat,frame_word64 (fr_out r));
   (80%nat,frame_word64 (fr_err r));(88%nat,frame_word64 (fr_elapsed r));
   (96%nat,frame_word32 (fr_export_state r));(100%nat,frame_word32 (fr_omitted r))] sender_magic_bytes.
Definition sender_prefix_result base result_local bytes_local r digest sequence fd k s :=
  exists le after, s=State f_send_frame sender_digest_tail k (sender_env result_local bytes_local) le after /\
    le ! _fd=Some (Vint fd) /\ le ! _sequence=Some (Vlong sequence) /\
    sender_storage base result_local bytes_local r digest (sender_prefix_bytes sequence r) after.

Ltac sender_bytes_length := first [assumption | repeat rewrite patch_bytes_length;
  cbn [frame_word32 frame_word64 put32_values put64_values map length sender_magic_bytes frame_magic app repeat];lia].

Ltac sender_keep_length ST := lazymatch type of ST with
  sender_storage _ _ _ _ _ (patch_bytes ?bytes ?index ?replacement) _ =>
  let LEN:=fresh "LENGTH" in
  lazymatch goal with PREV : length bytes=160%nat |- _ =>
    assert (LEN : length (patch_bytes bytes index replacement)=160%nat) by
      (rewrite patch_bytes_length;[exact PREV|rewrite PREV;
       cbn [frame_word32 frame_word64 put32_values put64_values map length];lia])
  end end.

Ltac sender_reach_route OLD := eapply source_reaches_prepend;
  [exact OLD|apply unchanged_store_edge;WriteAll.structural|].
Ltac sender_reach_call OLD SYMBOL FUNCTION := eapply source_reaches_prepend;
  [exact OLD| |];
  [eapply certified_call_edge;[reflexivity|
    apply old_expression_value;eapply value_function;[unfold sender_env;cbn;reflexivity|exact SYMBOL|reflexivity]|
    sender_arguments|exact FUNCTION|reflexivity]|].

Theorem sender_prefix_source : forall base m result_local bytes_local r digest sequence fd k le,
  ~ Mem.valid_block base bytes_local -> result_local<>bytes_local ->
  sender_storage base result_local bytes_local r digest sender_magic_bytes m ->
  le ! _fd=Some (Vint fd) -> le ! _sequence=Some (Vlong sequence) ->
  source_reaches result_ge (old_memory base)
    (sender_prefix_result base result_local bytes_local r digest sequence fd k)
    (State f_send_frame sender_after_magic k (sender_env result_local bytes_local) le m).
Proof.
  intros base m result_local bytes_local r digest sequence fd k le FRESH NE STORAGE FD SEQ.
  assert (LENGTH : length sender_magic_bytes=160%nat) by reflexivity.
  destruct sender_encoding_symbols as [b32 [b64 [bc [S32 [F32 [S64 [F64 [CS CF]]]]]]]].
  let body := eval cbv [sender_after_magic sender_after_zero sender_zero_tail statement_drop f_send_frame fn_body] in sender_after_magic in
    change (source_reaches result_ge (old_memory base)
      (sender_prefix_result base result_local bytes_local r digest sequence fd k)
      (State f_send_frame body k (sender_env result_local bytes_local) le m)).
  fold sender_digest_tail.
  Ltac sender_prefix_run base result_local bytes_local r digest FRESH NE S32 F32 S64 F64 :=
    lazymatch goal with
    | |- source_reaches _ _ _ (State _ sender_digest_tail _ _ _ _) =>
      apply source_reaches_done;
        [lazymatch goal with ST : sender_storage _ _ _ _ _ _ _ |- _=>exact (proj1 ST) end|];
      unfold sender_prefix_result;eexists;eexists;split;[reflexivity|];
      split;[WriteAll.lookup|];split;[WriteAll.lookup|];
      unfold sender_prefix_bytes;cbn [fold_left fst snd];
      lazymatch goal with ST : sender_storage _ _ _ _ _ _ _ |- _ => exact ST end
    | |- source_reaches ?ge ?P ?Q (State ?f (Ssequence (Scall _ (Evar _memcpy _) _) _) ?cont ?env ?temps ?memory) =>
      change (source_reaches ge P Q (State f sender_digest_tail cont env temps memory));
      sender_prefix_run base result_local bytes_local r digest FRESH NE S32 F32 S64 F64
    | |- source_reaches _ _ _ (State _ (Sset _ (Efield _ _ _)) _ _ _ ?m) =>
      lazymatch goal with ST : sender_storage _ _ _ _ _ _ m |- _ =>
        let OLD:=constr:(proj1 ST) in let OWN:=constr:(proj1 (proj2 ST)) in
        eapply source_reaches_prepend;[exact OLD|eapply certified_set_edge;sender_field r OWN|]
      end;sender_prefix_run base result_local bytes_local r digest FRESH NE S32 F32 S64 F64
    | |- source_reaches _ _ _ (State _ (Sassign _ ?rhs) _ _ ?temps ?m) =>
      lazymatch goal with ST : sender_storage _ _ _ _ _ ?bytes m |- _ =>
        let OLD:=constr:(proj1 ST) in
        lazymatch goal with |- source_reaches _ _ _ (State _ (Sassign (Ederef (Ebinop Oadd _ (Econst_int ?offset _) _) _) _) _ _ _ _) =>
          let index:=eval vm_compute in (Z.to_nat (Int.signed offset)) in
          let EV:=fresh "EV" in let value:=fresh "value" in
          evar (value : val);
          assert (EV : expression_value result_ge (sender_env result_local bytes_local) temps m rhs value)
            by (unfold value;sender_expression);
          subst value;
          lazymatch type of EV with expression_value _ _ _ _ _ (Vint ?word) =>
            let x:=constr:(cast_int_int I8 Unsigned word) in
            let after:=fresh "after" in let STORE:=fresh "STORE" in let NEXT:=fresh "STORAGE" in
            destruct (sender_byte_store base m result_local bytes_local r digest bytes index x FRESH NE ST
              ltac:(sender_bytes_length) ltac:(lia)) as [after [STORE NEXT]];
            eapply source_reaches_prepend;[exact OLD| |];
            [eapply assignment_source_edge;
              [sender_location|exact EV|reflexivity|eapply assign_loc_value;[reflexivity|exact STORE]]|];
            clear ST EV STORE;
            cbn [cast_int_int] in NEXT;rewrite ?narrowed_byte in NEXT;sender_keep_length NEXT
          end
        end
      end;sender_prefix_run base result_local bytes_local r digest FRESH NE S32 F32 S64 F64
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
      end;sender_prefix_run base result_local bytes_local r digest FRESH NE S32 F32 S64 F64
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
      end;sender_prefix_run base result_local bytes_local r digest FRESH NE S32 F32 S64 F64
    | |- source_reaches _ _ _ ?s =>
      let m:=eval cbn [memory_of] in (memory_of s) in
      lazymatch goal with ST : sender_storage _ _ _ _ _ _ m |- _=>
        let OLD:=constr:(proj1 ST) in sender_reach_route OLD end;sender_prefix_run base result_local bytes_local r digest FRESH NE S32 F32 S64 F64
    end.
  sender_prefix_run base result_local bytes_local r digest FRESH NE S32 F32 S64 F64.
Qed.
