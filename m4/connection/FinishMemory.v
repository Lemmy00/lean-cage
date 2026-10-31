(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.finish: Preserve the outer caller's record across all sender I/O and local frees. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers Values Memory.
Require Import IO Machine Deterministic Library LibraryMachine SourceGuarantees FreshMemory
  FrameRecord SenderReportMemory.
Open Scope Z_scope.
Theorem sender_preserved_trans : forall cell base before after,
  sender_preserved cell base before -> sender_preserved cell before after -> sender_preserved cell base after.
Proof.
  intros cell base before after FIRST SECOND;eapply Mem.unchanged_on_trans;[exact FIRST|].
  eapply Mem.unchanged_on_implies;[exact SECOND|]. intros b pos [VALID OUTSIDE] VALIDBEFORE;split;assumption.
Qed.
Theorem preserved_frame_owned : forall cell before after b ofs r digest,
  sender_preserved cell before after -> b<>tls_block cell -> frame_result_owned before b ofs r digest ->
  frame_result_owned after b ofs r digest.
Proof.
  intros cell before after b ofs r digest PRESERVED NE [LOW [HIGH [ALIGN [PERMS [LEN [FIELDS [BOUNDS LOAD]]]]]]].
  assert (VALID : Mem.valid_block before b) by (eapply Mem.perm_valid_block with (ofs:=ofs);apply PERMS;lia).
  split;[exact LOW|]. split;[exact HIGH|]. split;[exact ALIGN|]. split.
  - intros pos RANGE;eapply Mem.perm_unchanged_on;[exact PRESERVED|split;[exact VALID|left;exact NE]|apply PERMS;exact RANGE].
  - split;[exact LEN|]. split.
    + intros field IN;eapply Mem.load_unchanged_on;[exact PRESERVED|intros;split;[exact VALID|left;exact NE]|apply FIELDS;exact IN].
    + split;[exact BOUNDS|]. eapply Mem.loadbytes_unchanged_on;[exact PRESERVED|intros;split;[exact VALID|left;exact NE]|exact LOAD].
Qed.
Theorem preserved_frame_freeable : forall cell before after b,
  sender_preserved cell before after -> b<>tls_block cell -> Mem.range_perm before b 0 144 Cur Freeable ->
  Mem.range_perm after b 0 144 Cur Freeable.
Proof.
  intros cell before after b PRESERVED NE FREE pos RANGE.
  eapply Mem.perm_unchanged_on;[exact PRESERVED| |apply FREE;exact RANGE].
  split;[eapply Mem.perm_valid_block;apply FREE;exact RANGE|left;exact NE].
Qed.
Theorem procedure_preservation_post : forall ge cell P R start,
  procedure_guarantee ge cell P R start ->
  procedure_guarantee ge cell P (fun value after=>P after /\ R value after) start.
Proof.
  intros ge cell P R start [MEMORY PROGRESS];split;[exact MEMORY|].
  intros events s RUN;destruct (PROGRESS _ _ RUN) as [[value [after [EQ POST]]]|NEXT];[left|right;exact NEXT].
  exists value,after;split;[exact EQ|]. split;[subst s;exact (MEMORY _ _ RUN)|exact POST].
Qed.
Theorem procedure_guarantee_consequence : forall ge cell P Q A B start,
  procedure_guarantee ge cell P A start ->
  (forall m,P m->Q m) -> (forall value after,A value after->B value after) ->
  procedure_guarantee ge cell Q B start.
Proof.
  intros ge cell P Q A B start [MEMORY PROGRESS] MEM POST;split.
  - intros;apply MEM;eapply MEMORY;eassumption.
  - intros events s RUN;destruct (PROGRESS _ _ RUN) as [[value [after [EQ RESULT]]]|NEXT];[left|right;exact NEXT].
    exists value,after;split;[exact EQ|apply POST;exact RESULT].
Qed.
