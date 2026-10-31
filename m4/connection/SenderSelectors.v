(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.input: Stable selectors remain readable across the actual TLS writes. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Globalenvs Clight.
Require Import Slice Machine Library ProcessEffects Fault WriteBytes FreshMemory ResultLayout FrameRecord WriteEffects.
Import ListNotations.
Open Scope Z_scope.
Inductive report_fault := wrong_sequence | bad_reserved | duplicate_frame | short_frame | drop_frame.
Definition report_literal tag := match tag with
  | wrong_sequence=>___stringlit_3
  | bad_reserved=>___stringlit_4
  | duplicate_frame=>___stringlit_5
  | short_frame=>___stringlit_6
  | drop_frame=>___stringlit_7
end.
Definition report_name tag : list Byte.int := match tag with
  | wrong_sequence=>map Byte.repr [114;101;112;111;114;116;95;119;114;111;110;103;95;115;101;113]
  | bad_reserved=>map Byte.repr [114;101;112;111;114;116;95;98;97;100;95;114;101;115;101;114;118;101;100]
  | duplicate_frame=>map Byte.repr [114;101;112;111;114;116;95;100;117;112;108;105;99;97;116;101]
  | short_frame=>map Byte.repr [114;101;112;111;114;116;95;115;104;111;114;116]
  | drop_frame=>map Byte.repr [114;101;112;111;114;116;95;100;114;111;112]
end.
Definition span_outside_tls cell p count := forall pos,
  address_offset p<=pos<address_offset p+count ->
  outside_bytes (tls_block cell) (tls_offset cell) 4 (address_block p) pos.
Definition stable_string cell m p bytes := c_string m p bytes /\
  span_outside_tls cell p (Z.of_nat (length (bytes++[Byte.zero]))).
Definition stable_mode_pointer cell m mode := exists mb,
  Genv.find_symbol result_ge _mode=Some mb /\
  Mem.load Mint64 m mb 0=Some (address_value mode) /\
  span_outside_tls cell {|address_block:=mb;address_offset:=0|} 8.
Definition sender_selectors cell m mode mode_bytes locations :=
  tls_ready cell m /\ stable_mode_pointer cell m mode /\ stable_string cell m mode mode_bytes /\
  forall tag,Genv.find_symbol result_ge (report_literal tag)=Some (locations tag) /\
    stable_string cell m {|address_block:=locations tag;address_offset:=0|} (report_name tag).
Definition report_enabled fd r := negb (Int.eq fd Int.one) && Int.cmpu Cle (fr_kind r) (Int.repr 4).
Definition report_matches mode_bytes tag := match compare_bytes mode_bytes (report_name tag) with Eq=>true|_=>false end.
Definition report_selected fd r mode_bytes tag := report_enabled fd r && report_matches mode_bytes tag.
Lemma stable_mode_fault_input : forall cell m mode,
  stable_mode_pointer cell m mode -> mode_pointer result_ge m mode.
Proof. intros cell m mode [mb [SYMBOL [LOAD SEP]]];exists mb;split;[exact SYMBOL|exact LOAD]. Qed.
Lemma sender_selector_input : forall cell m mode mode_bytes locations tag,
  sender_selectors cell m mode mode_bytes locations ->
  fault_input result_ge m mode {|address_block:=locations tag;address_offset:=0|} mode_bytes (report_name tag).
Proof.
  intros cell m mode mode_bytes locations tag [TLS [MODE [STRING LITERALS]]].
  split;[eapply stable_mode_fault_input;exact MODE|]. split;[exact (proj1 STRING)|exact (proj1 (proj2 (LITERALS tag)))].
Qed.
Lemma stable_string_history : forall cell m after p bytes,
  tls_history cell m after -> stable_string cell m p bytes -> stable_string cell after p bytes.
Proof.
  intros cell m after p bytes HISTORY [[NONZERO [BOUNDS LOAD]] SEP].
  split;[split;[exact NONZERO|];split;[exact BOUNDS|]|exact SEP].
  eapply Mem.loadbytes_unchanged_on;[eapply tls_history_outside;exact HISTORY|exact SEP|exact LOAD].
Qed.
Lemma stable_mode_history : forall cell m after mode,
  tls_history cell m after -> stable_mode_pointer cell m mode -> stable_mode_pointer cell after mode.
Proof.
  intros cell m after mode HISTORY [mb [SYMBOL [LOAD SEP]]].
  exists mb;split;[exact SYMBOL|]. split;[|exact SEP].
  eapply Mem.load_unchanged_on;[eapply tls_history_outside;exact HISTORY|exact SEP|exact LOAD].
Qed.
Theorem sender_selectors_history : forall cell m after mode mode_bytes locations,
  tls_history cell m after -> sender_selectors cell m mode mode_bytes locations ->
  sender_selectors cell after mode mode_bytes locations.
Proof.
  intros cell m after mode mode_bytes locations HISTORY [TLS [MODE [STRING LITERALS]]].
  split;[eapply tls_history_ready;eassumption|]. split;[eapply stable_mode_history;eassumption|].
  split;[eapply stable_string_history;eassumption|]. intros tag;split;[exact (proj1 (LITERALS tag))|].
  eapply stable_string_history;[exact HISTORY|exact (proj2 (LITERALS tag))].
Qed.
Theorem sender_selectors_old : forall cell base after mode mode_bytes locations,
  old_memory base after -> sender_selectors cell base mode mode_bytes locations ->
  sender_selectors cell after mode mode_bytes locations.
Proof.
  intros cell base after mode mode_bytes locations OLD [TLS [[mb [SYMBOL [LOAD SEP]]] [[STRING SEPSTRING] LITERALS]]].
  split;[eapply old_memory_tls;eassumption|]. split.
  - exists mb;split;[exact SYMBOL|]. split;[eapply old_memory_load;eassumption|exact SEP].
  - split;[split;[eapply old_memory_string;eassumption|exact SEPSTRING]|].
    intros tag;destruct (LITERALS tag) as [SYM [BYTES SEPNAME]].
    split;[exact SYM|]. split;[eapply old_memory_string;eassumption|exact SEPNAME].
Qed.
Theorem report_matches_exact : forall mode_bytes tag,
  report_matches mode_bytes tag=true <-> mode_bytes=report_name tag.
Proof. intros;unfold report_matches;rewrite <- compare_bytes_equal;destruct (compare_bytes mode_bytes (report_name tag));split;congruence. Qed.
Theorem report_names_distinct : forall a b,report_name a=report_name b -> a=b.
Proof. intros a b;destruct a,b;vm_compute;congruence. Qed.
Theorem report_selection_unique : forall fd r mode_bytes a b,
  report_selected fd r mode_bytes a=true -> report_selected fd r mode_bytes b=true -> a=b.
Proof.
  intros fd r mode_bytes a b A B;apply Bool.andb_true_iff in A;apply Bool.andb_true_iff in B.
  destruct A as [_ A];destruct B as [_ B];apply report_matches_exact in A;apply report_matches_exact in B.
  apply report_names_distinct;congruence.
Qed.
