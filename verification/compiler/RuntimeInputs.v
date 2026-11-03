(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-compiled-reporting.runtime: General allocations inhabit the actual reporting call interface. *)
(* Adapted from the preserved LibraryWitnesses, FailureWitnesses, DecoderAllocation,
   SenderGlobals and SenderWitnesses modules. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Slice IO Machine Readers Library ProcessEffects FreshMemory Fault
 ResultLayout ScalarMemory DecoderValidity FrameRecord FrameAllocation SenderSelectors SenderSource SenderProgram InputWitnesses RuntimeProgram.
Import ListNotations.
Open Scope Z_scope.
Theorem rooted_sender_globals : forall mode_bytes,
 Forall(fun b=>b<>Byte.zero)mode_bytes ->(length mode_bytes<=158)%nat ->
 exists cell base mode,sender_selectors cell base mode mode_bytes sender_literal_location /\
 readable_bytes base {|address_block:=137%positive;address_offset:=0|}frame_magic /\
 tls_block cell=374%positive /\ tls_offset cell=0.
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
 destruct(allocate_decoder_scalar gap7 Mint64(address_value(global_address 375%positive)) eq_refl)as[m7[b7[O7[POINTER[B7 N7]]]]].
 rewrite NG7 in B7,N7;subst b7;change(Mem.nextblock m7=317%positive)in N7.
 set(runtime_gap:=empty_allocations 57 m7).
 assert(OGTLS:old_memory m7 runtime_gap)by apply empty_allocations_preserve.
 assert(NGTLS:Mem.nextblock runtime_gap=374%positive).
 { apply Pos2Nat.inj;unfold runtime_gap;rewrite empty_allocations_next,N7;reflexivity. }
 destruct(Mem.alloc runtime_gap 0 4)as[tlsmem eb]eqn:TLSALLOC.
 assert(EB:eb=374%positive)by(rewrite(Mem.alloc_result _ _ _ _ _ TLSALLOC);exact NGTLS);subst eb.
 assert(OT:old_memory m7 tlsmem).
 { eapply Mem.unchanged_on_trans;[exact OGTLS|eapply Mem.alloc_unchanged_on;exact TLSALLOC]. }
 assert(NT:Mem.nextblock tlsmem=375%positive).
 { rewrite(Mem.nextblock_alloc _ _ _ _ _ TLSALLOC),NGTLS;reflexivity. }
 set(gap8:=empty_allocations 0 tlsmem).
 assert(OG8:old_memory tlsmem gap8)by apply empty_allocations_preserve.
 assert(NG8:Mem.nextblock gap8=375%positive).
 { apply Pos2Nat.inj;unfold gap8;rewrite empty_allocations_next,NT;reflexivity. }
 destruct(allocate_failure_string gap8 mode_bytes NONZERO LENGTH)as[m8[b8[O8[MODE[B8 N8]]]]].
 rewrite NG8 in B8,N8;subst b8;change(Mem.nextblock m8=376%positive)in N8.
 set(base:=m8).
 assert(OB:old_memory tlsmem base)by(eapply Mem.unchanged_on_trans;[exact OG8|exact O8]).
 exists {|tls_block:=374%positive;tls_offset:=0|},base,(global_address 375%positive);split.
 - split.
   + eapply old_memory_tls;[exact OB|]. unfold tls_ready;cbn;split;[lia|]. split;[change(4<=18446744073709551616);lia|].
     eapply Mem.valid_access_implies with(p1:=Freeable);[|constructor].
     eapply Mem.valid_access_alloc_same;[exact TLSALLOC|cbn;lia|cbn;lia|exists 0;reflexivity].
   + split.
     * exists 316%positive;split;[exact source_mode_symbol|]. split.
       -- eapply old_memory_load;[exact OB|]. eapply old_memory_load;[exact OT|exact POINTER].
       -- intros pos RANGE;left;discriminate.
     * split.
       -- split;[carry_sender_string|intros pos RANGE;left;discriminate].
       -- intros tag;split;[apply sender_literal_symbols|]. destruct tag;split;
          first[carry_sender_string|intros pos RANGE;left;discriminate].
 - split;[carry_sender_bytes|split;reflexivity].
Qed.

Theorem rooted_sender_input : forall r digest mode_bytes,
 length digest=32%nat -> Forall(fun b=>b<>Byte.zero)mode_bytes -> (length mode_bytes<=158)%nat ->
 exists cell base input mode,
 sender_input cell base input 0 r digest mode mode_bytes sender_literal_location /\
 errno_root result_ge(tls_block cell)(tls_offset cell).
Proof.
 intros r digest mode_bytes LEN NONZERO SIZE.
 destruct(rooted_sender_globals mode_bytes NONZERO SIZE)
   as[cell[globals[mode[SELECTORS[MAGIC[BLOCK OFFSET]]]]]].
 destruct(allocate_frame_record globals r digest LEN)as[base[input[OLD[OWN FRESH]]]].
 exists cell,base,input,mode;split.
 - split;[exact OWN|]. split;[eapply sender_selectors_old;eassumption|].
   exists 137%positive;split;[exact source_magic_symbol|eapply old_memory_readable;eassumption].
 - unfold errno_root;rewrite BLOCK,OFFSET;split;[exact RuntimeProgram.errno_symbol|].
   split;[reflexivity|exact RuntimeProgram.errno_public].
Qed.
