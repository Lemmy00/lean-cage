(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-reporting.proof: General allocations inhabit the actual reporting call interface. *)
(* Adapted from the preserved LibraryWitnesses, FailureWitnesses, DecoderAllocation,
   SenderGlobals and SenderWitnesses modules. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Slice IO Machine Readers Library ProcessEffects FreshMemory Fault
 ResultLayout ScalarMemory DecoderValidity FrameRecord FrameAllocation SenderSelectors SenderSource SenderProgram.
Import ListNotations.
Open Scope Z_scope.
Definition global_address b := {|address_block:=b;address_offset:=0|}.
Lemma source_mode_symbol : Genv.find_symbol result_ge _mode=Some 316%positive.
Proof. vm_compute;reflexivity. Qed.
Lemma source_magic_symbol : Genv.find_symbol result_ge ___stringlit_2=Some 137%positive.
Proof. vm_compute;reflexivity. Qed.
Definition vacant_memory (next : block) : mem.
Proof.
  refine (Mem.mkmem (Mem.mem_contents Mem.empty) (Mem.mem_access Mem.empty) next _ _ _).
  - exact (Mem.access_max Mem.empty).
  - intros b ofs k UNUSED. cbn. rewrite PMap.gi. reflexivity.
  - exact (Mem.contents_default Mem.empty).
Defined.



Lemma allocate_failure_string : forall base bytes,
  Forall (fun b => b <> Byte.zero) bytes -> (length bytes <= 158)%nat ->
  exists after b, old_memory base after /\ c_string after (global_address b) bytes /\
    b = Mem.nextblock base /\ Mem.nextblock after = Pos.succ (Mem.nextblock base).
Proof.
  intros base bytes NONZERO BOUND.
  destruct (allocated_bytes base (bytes++[Byte.zero])) as [allocated [b [after [ALLOC [STORE LOAD]]]]].
  assert (FRESH : ~ Mem.valid_block base b) by (eapply Mem.fresh_block_alloc; exact ALLOC).
  exists after, b; split.
  - eapply Mem.unchanged_on_trans; [eapply Mem.alloc_unchanged_on; exact ALLOC|].
    eapply Mem.storebytes_unchanged_on; [exact STORE|]. intros pos RANGE VALID; contradiction.
  - split.
    + split; [exact NONZERO|]. split.
      * unfold span_bounds, global_address; cbn [address_offset]. rewrite app_length; cbn [length].
        change (0 <= 0 < 18446744073709551616 /\
          0+Z.of_nat (length bytes+1) <= 18446744073709551616 /\
          Z.of_nat (length bytes+1) <= 18446744073709551615); lia.
      * exact LOAD.
    + split; [exact (Mem.alloc_result _ _ _ _ _ ALLOC)|].
      rewrite (Mem.nextblock_storebytes _ _ _ _ _ STORE), (Mem.nextblock_alloc _ _ _ _ _ ALLOC); reflexivity.
Qed.

Fixpoint empty_allocations n m := match n with
  | O => m | S rest => let '(after,_) := Mem.alloc m 0 0 in empty_allocations rest after end.
Lemma empty_allocations_preserve : forall n m, old_memory m (empty_allocations n m).
Proof.
  induction n; intros m; cbn; [apply Mem.unchanged_on_refl|].
  destruct (Mem.alloc m 0 0) as [after b] eqn:ALLOC.
  eapply Mem.unchanged_on_trans; [eapply Mem.alloc_unchanged_on; exact ALLOC|].
  eapply Mem.unchanged_on_implies; [exact (IHn after)|].
  intros block pos VALID VALIDAFTER; exact VALIDAFTER.
Qed.
Lemma empty_allocations_next : forall n m,
  Pos.to_nat (Mem.nextblock (empty_allocations n m)) = (Pos.to_nat (Mem.nextblock m) + n)%nat.
Proof.
  induction n; intros m; cbn; [lia|].
  destruct (Mem.alloc m 0 0) as [after b] eqn:ALLOC.
  rewrite IHn, (Mem.nextblock_alloc _ _ _ _ _ ALLOC), Pos2Nat.inj_succ; lia.
Qed.



Lemma allocate_decoder_bytes : forall base bytes,
  (length bytes <= 160)%nat -> exists after b,
  old_memory base after /\ readable_bytes after {|address_block:=b;address_offset:=0|} bytes /\
  b=Mem.nextblock base /\ Mem.nextblock after=Pos.succ (Mem.nextblock base).
Proof.
  intros base bytes BOUND.
  destruct (allocated_bytes base bytes) as [allocated [b [after [ALLOC [STORE LOAD]]]]].
  assert (FRESH : ~ Mem.valid_block base b) by (eapply Mem.fresh_block_alloc;exact ALLOC).
  exists after,b;split.
  - eapply Mem.unchanged_on_trans;[eapply Mem.alloc_unchanged_on;exact ALLOC|].
    eapply Mem.storebytes_unchanged_on;[exact STORE|]. intros pos RANGE VALID;contradiction.
  - split.
    + split;[|exact LOAD]. unfold span_bounds;cbn [address_offset].
      change (0<=0<18446744073709551616 /\ 0+Z.of_nat (length bytes)<=18446744073709551616 /\
        Z.of_nat (length bytes)<=18446744073709551615);lia.
    + split;[exact (Mem.alloc_result _ _ _ _ _ ALLOC)|].
      rewrite (Mem.nextblock_storebytes _ _ _ _ _ STORE),(Mem.nextblock_alloc _ _ _ _ _ ALLOC);reflexivity.
Qed.
Lemma allocate_decoder_scalar : forall base chunk value,
  Val.load_result chunk value=value -> exists after b,
  old_memory base after /\ Mem.load chunk after b 0=Some value /\
  b=Mem.nextblock base /\ Mem.nextblock after=Pos.succ (Mem.nextblock base).
Proof.
  intros base chunk value NORMAL.
  destruct (Mem.alloc base 0 (size_chunk chunk)) as [allocated b] eqn:ALLOC.
  assert (ACCESS : Mem.valid_access allocated chunk b 0 Writable).
  { eapply Mem.valid_access_implies with (p1:=Freeable);[|constructor].
    eapply Mem.valid_access_alloc_same;[exact ALLOC|lia|lia|exists 0;lia]. }
  destruct (Mem.valid_access_store _ _ _ _ value ACCESS) as [after STORE].
  exists after,b;split.
  - eapply Mem.unchanged_on_trans;[eapply Mem.alloc_unchanged_on;exact ALLOC|].
    eapply Mem.store_unchanged_on;[exact STORE|]. intros pos RANGE VALID.
    eapply (Mem.fresh_block_alloc _ _ _ _ _ ALLOC);exact VALID.
  - split;[rewrite (Mem.load_store_same _ _ _ _ _ _ STORE),NORMAL;reflexivity|].
    split;[exact (Mem.alloc_result _ _ _ _ _ ALLOC)|].
    rewrite (Mem.nextblock_store _ _ _ _ _ _ STORE),(Mem.nextblock_alloc _ _ _ _ _ ALLOC);reflexivity.
Qed.


Definition sender_literal_location tag : block := match tag with
 |wrong_sequence=>56%positive|bad_reserved=>97%positive|duplicate_frame=>92%positive
 |short_frame=>62%positive|drop_frame=>106%positive end.
Theorem sender_literal_symbols : forall tag,
 Genv.find_symbol result_ge(report_literal tag)=Some(sender_literal_location tag).
Proof. destruct tag;vm_compute;reflexivity. Qed.
Lemma report_name_nonzero : forall tag,Forall(fun b=>b<>Byte.zero)(report_name tag).
Proof. destruct tag;repeat constructor;vm_compute;discriminate. Qed.
Lemma report_name_size : forall tag,(length(report_name tag)<=158)%nat.
Proof. destruct tag;cbn;lia. Qed.
Ltac carry_sender_string := first[assumption|
 lazymatch goal with |-c_string ?m _ _=>
 match goal with OLD:old_memory ?previous m|-_=>eapply old_memory_string;[exact OLD|carry_sender_string]end end].
Ltac carry_sender_bytes := first[assumption|
 lazymatch goal with |-readable_bytes ?m _ _=>
 match goal with OLD:old_memory ?previous m|-_=>eapply old_memory_readable;[exact OLD|carry_sender_bytes]end end].
Theorem allocated_sender_globals : forall mode_bytes,
 Forall(fun b=>b<>Byte.zero)mode_bytes ->(length mode_bytes<=158)%nat ->
 exists cell base mode,sender_selectors cell base mode mode_bytes sender_literal_location /\
 readable_bytes base {|address_block:=137%positive;address_offset:=0|}frame_magic.
Proof.
 intros mode_bytes NONZERO LENGTH.
 set(m0:=vacant_memory 56%positive).
 assert(N0:Mem.nextblock m0=56%positive)by reflexivity.
 set(gap1:=empty_allocations 0 m0).
 assert(OG1:old_memory m0 gap1)by apply empty_allocations_preserve.
 assert(NG1:Mem.nextblock gap1=56%positive).
 { apply Pos2Nat.inj;unfold gap1;rewrite empty_allocations_next,N0;reflexivity. }
 destruct(allocate_failure_string gap1(report_name wrong_sequence)(report_name_nonzero _)(report_name_size _))as[m1[b1[O1[STRING1[B1 N1]]]]].
 rewrite NG1 in B1,N1;subst b1;change(Mem.nextblock m1=57%positive)in N1.
 set(gap2:=empty_allocations 5 m1).
 assert(OG2:old_memory m1 gap2)by apply empty_allocations_preserve.
 assert(NG2:Mem.nextblock gap2=62%positive).
 { apply Pos2Nat.inj;unfold gap2;rewrite empty_allocations_next,N1;reflexivity. }
 destruct(allocate_failure_string gap2(report_name short_frame)(report_name_nonzero _)(report_name_size _))as[m2[b2[O2[STRING2[B2 N2]]]]].
 rewrite NG2 in B2,N2;subst b2;change(Mem.nextblock m2=63%positive)in N2.
 set(gap3:=empty_allocations 29 m2).
 assert(OG3:old_memory m2 gap3)by apply empty_allocations_preserve.
 assert(NG3:Mem.nextblock gap3=92%positive).
 { apply Pos2Nat.inj;unfold gap3;rewrite empty_allocations_next,N2;reflexivity. }
 destruct(allocate_failure_string gap3(report_name duplicate_frame)(report_name_nonzero _)(report_name_size _))as[m3[b3[O3[STRING3[B3 N3]]]]].
 rewrite NG3 in B3,N3;subst b3;change(Mem.nextblock m3=93%positive)in N3.
 set(gap4:=empty_allocations 4 m3).
 assert(OG4:old_memory m3 gap4)by apply empty_allocations_preserve.
 assert(NG4:Mem.nextblock gap4=97%positive).
 { apply Pos2Nat.inj;unfold gap4;rewrite empty_allocations_next,N3;reflexivity. }
 destruct(allocate_failure_string gap4(report_name bad_reserved)(report_name_nonzero _)(report_name_size _))as[m4[b4[O4[STRING4[B4 N4]]]]].
 rewrite NG4 in B4,N4;subst b4;change(Mem.nextblock m4=98%positive)in N4.
 set(gap5:=empty_allocations 8 m4).
 assert(OG5:old_memory m4 gap5)by apply empty_allocations_preserve.
 assert(NG5:Mem.nextblock gap5=106%positive).
 { apply Pos2Nat.inj;unfold gap5;rewrite empty_allocations_next,N4;reflexivity. }
 destruct(allocate_failure_string gap5(report_name drop_frame)(report_name_nonzero _)(report_name_size _))as[m5[b5[O5[STRING5[B5 N5]]]]].
 rewrite NG5 in B5,N5;subst b5;change(Mem.nextblock m5=107%positive)in N5.
 set(gap6:=empty_allocations 30 m5).
 assert(OG6:old_memory m5 gap6)by apply empty_allocations_preserve.
 assert(NG6:Mem.nextblock gap6=137%positive).
 { apply Pos2Nat.inj;unfold gap6;rewrite empty_allocations_next,N5;reflexivity. }
 destruct(allocate_decoder_bytes gap6 frame_magic ltac:(cbn;lia))as[m6[b6[O6[MAGIC[B6 N6]]]]].
 rewrite NG6 in B6,N6;subst b6;change(Mem.nextblock m6=138%positive)in N6.
 set(gap7:=empty_allocations 178 m6).
 assert(OG7:old_memory m6 gap7)by apply empty_allocations_preserve.
 assert(NG7:Mem.nextblock gap7=316%positive).
 { apply Pos2Nat.inj;unfold gap7;rewrite empty_allocations_next,N6;reflexivity. }
 destruct(allocate_decoder_scalar gap7 Mint64(address_value(global_address 317%positive)) eq_refl)as[m7[b7[O7[POINTER[B7 N7]]]]].
 rewrite NG7 in B7,N7;subst b7;change(Mem.nextblock m7=317%positive)in N7.
 set(gap8:=empty_allocations 0 m7).
 assert(OG8:old_memory m7 gap8)by apply empty_allocations_preserve.
 assert(NG8:Mem.nextblock gap8=317%positive).
 { apply Pos2Nat.inj;unfold gap8;rewrite empty_allocations_next,N7;reflexivity. }
 destruct(allocate_failure_string gap8 mode_bytes NONZERO LENGTH)as[m8[b8[O8[MODE[B8 N8]]]]].
 rewrite NG8 in B8,N8;subst b8;change(Mem.nextblock m8=318%positive)in N8.
 destruct(Mem.alloc m8 0 4)as[base eb]eqn:TLSALLOC.
 assert(EB:eb=318%positive)by(rewrite(Mem.alloc_result _ _ _ _ _ TLSALLOC);exact N8);subst eb.
 assert(OB:old_memory m8 base)by(eapply Mem.alloc_unchanged_on;exact TLSALLOC).
 exists {|tls_block:=318%positive;tls_offset:=0|},base,(global_address 317%positive);split.
 - split.
   + unfold tls_ready;cbn;split;[lia|]. split;[change(4<=18446744073709551616);lia|].
     eapply Mem.valid_access_implies with(p1:=Freeable);[|constructor].
     eapply Mem.valid_access_alloc_same;[exact TLSALLOC|cbn;lia|cbn;lia|exists 0;reflexivity].
   + split.
     * exists 316%positive;split;[exact source_mode_symbol|]. split.
       -- eapply old_memory_load;[exact OB|]. eapply old_memory_load;[exact O8|].
          eapply old_memory_load;[exact OG8|exact POINTER].
       -- intros pos RANGE;left;discriminate.
     * split.
       -- split;[carry_sender_string|intros pos RANGE;left;discriminate].
       -- intros tag;split;[apply sender_literal_symbols|]. destruct tag;split;
          first[carry_sender_string|intros pos RANGE;left;discriminate].
 - carry_sender_bytes.
Qed.

Theorem arbitrary_sender_input : forall r digest mode_bytes,
  length digest=32%nat -> Forall (fun b=>b<>Byte.zero) mode_bytes -> (length mode_bytes<=158)%nat ->
  exists cell base input mode,sender_input cell base input 0 r digest mode mode_bytes sender_literal_location.
Proof.
  intros r digest mode_bytes LEN NONZERO SIZE.
  destruct (allocated_sender_globals mode_bytes NONZERO SIZE) as [cell [globals [mode [SELECTORS MAGIC]]]].
  destruct (allocate_frame_record globals r digest LEN) as [base [input [OLD [OWN BLOCK]]]].
  exists cell,base,input,mode;split;[exact OWN|]. split;[eapply sender_selectors_old;eassumption|].
  exists 137%positive;split;[exact source_magic_symbol|eapply old_memory_readable;eassumption].
Qed.
