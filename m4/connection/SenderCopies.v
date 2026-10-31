(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.encoding: Real literal and digest call sites with independent copy ownership. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Slice Machine ClightSteps WriteAll StoreSteps LocalAccess CallAccess Library LibraryMachine
  FreshMemory ResultLayout DecoderValidity FrameRecord SenderSource SenderAccess
  BytePatch SenderStorage SenderEncodingPrefix.
Import ListNotations.
Open Scope Z_scope.
Definition sender_after_digest := statement_drop 20 sender_after_zero.
Definition sender_magic_cont result_local bytes_local le k :=
  Kcall None f_send_frame (sender_env result_local bytes_local) le (Kseq sender_after_magic k).
Definition sender_digest_cont result_local bytes_local le k :=
  Kcall None f_send_frame (sender_env result_local bytes_local) le (Kseq sender_after_digest k).

Theorem sender_magic_call_source : forall (P : mem -> Prop) m result_local bytes_local le k magic,
  P m -> Genv.find_symbol result_ge ___stringlit_2=Some magic ->
  store_path result_ge P (State f_send_frame sender_after_zero k (sender_env result_local bytes_local) le m) 2
    (Callstate memcpy_definition
      (copy_args {|address_block:=magic;address_offset:=0|} {|address_block:=bytes_local;address_offset:=0|} frame_magic)
      (sender_magic_cont result_local bytes_local le k) m).
Proof.
  intros P m result_local bytes_local le k magic PM MS.
  destruct sender_encoding_symbols as [b32 [b64 [bc [S32 [F32 [S64 [F64 [CS CF]]]]]]]].
  change sender_after_zero with (Ssequence (Scall None
    (Evar _memcpy (Tfunction [tptr tvoid;tptr tvoid;tulong] (tptr tvoid) cc_default))
    [Evar _bytes (tarray tuchar 160);Evar ___stringlit_2 (tarray tschar 5);Econst_int (Int.repr 4) tint]) sender_after_magic).
  eapply store_next;[exact PM|apply unchanged_store_edge;WriteAll.structural|].
  eapply store_next;[exact PM| |apply store_done;exact PM].
  unfold sender_magic_cont,copy_args,address_value;cbn [address_block address_offset length frame_magic].
  eapply certified_call_edge;[reflexivity| | |exact CF|reflexivity].
  - apply old_expression_value;eapply value_function;[unfold sender_env;cbn;reflexivity|exact CS|reflexivity].
  - eapply cons_argument_values;[sender_expression|reflexivity|].
    eapply cons_argument_values.
    + apply old_expression_value;eapply value_function;[unfold sender_env;cbn;reflexivity|exact MS|reflexivity].
    + reflexivity.
    + eapply cons_argument_values;[sender_expression|reflexivity|apply no_argument_values].
Qed.

Lemma sender_magic_copy_owned : forall base m magic result_local bytes_local r digest bytes,
  ~ Mem.valid_block base bytes_local ->
  readable_bytes base {|address_block:=magic;address_offset:=0|} frame_magic ->
  sender_storage base result_local bytes_local r digest bytes m ->
  copy_owned m {|address_block:=magic;address_offset:=0|} {|address_block:=bytes_local;address_offset:=0|} frame_magic.
Proof.
  intros base m magic result_local bytes_local r digest bytes FRESH MAGIC [OLD [OWN [READ [RFREE BFREE]]]].
  split;[eapply old_memory_readable;[exact OLD|exact MAGIC]|]. split.
  - unfold span_bounds;cbn [address_offset length frame_magic];vm_compute;repeat split;discriminate.
  - split.
    + intros pos RANGE;eapply Mem.perm_implies;[apply BFREE;cbn [address_offset length frame_magic] in RANGE;lia|constructor].
    + left;cbn;intro SAME;subst magic;apply FRESH.
      eapply Mem.perm_valid_block with (ofs:=0).
      eapply Mem.loadbytes_range_perm;[exact (proj2 MAGIC)|cbn [address_offset length frame_magic];lia].
Qed.

Theorem sender_digest_call_source : forall (P : mem -> Prop) m result_local bytes_local le k digest,
  P m -> length digest=32%nat ->
  store_path result_ge P (State f_send_frame sender_digest_tail k (sender_env result_local bytes_local) le m) 2
    (Callstate memcpy_definition
      (copy_args {|address_block:=result_local;address_offset:=108|} {|address_block:=bytes_local;address_offset:=104|} digest)
      (sender_digest_cont result_local bytes_local le k) m).
Proof.
  intros P m result_local bytes_local le k digest PM LEN.
  destruct sender_encoding_symbols as [b32 [b64 [bc [S32 [F32 [S64 [F64 [CS CF]]]]]]]].
  change sender_digest_tail with (Ssequence (Scall None
    (Evar _memcpy (Tfunction [tptr tvoid;tptr tvoid;tulong] (tptr tvoid) cc_default))
    [Ebinop Cop.Oadd (Evar _bytes (tarray tuchar 160)) (Econst_int (Int.repr 104) tint) (tptr tuchar);
     Efield (Evar _result__1 result_type) _export_digest (tarray tuchar 32);Econst_int (Int.repr 32) tint]) sender_after_digest).
  eapply store_next;[exact PM|apply unchanged_store_edge;WriteAll.structural|].
  eapply store_next;[exact PM| |apply store_done;exact PM].
  unfold sender_digest_cont,copy_args,address_value;cbn [address_block address_offset];rewrite LEN.
  eapply certified_call_edge;[reflexivity| |sender_arguments|exact CF|reflexivity].
  apply old_expression_value;eapply value_function;[unfold sender_env;cbn;reflexivity|exact CS|reflexivity].
Qed.

Lemma sender_digest_copy_owned : forall base m result_local bytes_local r digest bytes,
  result_local<>bytes_local -> sender_storage base result_local bytes_local r digest bytes m ->
  copy_owned m {|address_block:=result_local;address_offset:=108|} {|address_block:=bytes_local;address_offset:=104|} digest.
Proof.
  intros base m result_local bytes_local r digest bytes NE [OLD [OWN [READ [RFREE BFREE]]]].
  destruct OWN as [_ [_ [_ [_ [LEN [CONTENTS DIGEST]]]]]].
  split;[exact DIGEST|]. split.
  - unfold span_bounds;rewrite LEN;cbn [address_offset];vm_compute;repeat split;discriminate.
  - split.
    + intros pos RANGE;eapply Mem.perm_implies;[apply BFREE;rewrite LEN in RANGE;cbn [address_offset] in RANGE;lia|constructor].
    + left;exact NE.
Qed.
