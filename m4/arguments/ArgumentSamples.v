(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.arguments: Allocated boundaries, rejected prefixes and repeated pointers. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Values Memory Globalenvs Ctypes Clight.
Require Import Machine.
From LeanCageMain Require Import Main MainStructure MainSamples.
From LeanCageBounds Require Import BoundsStructure BoundsSequence.
From LeanCageArguments Require Import StringMachine StringPath ArgumentStructure ArgumentMemory
 ArgumentSource ArgumentWitnesses ArgumentBounds.
Import ListNotations.
Open Scope Z_scope.
Definition shell_bytes:list Byte.int:=map Byte.repr[47;98;105;110;47;115;104].
Definition a_bytes n:=repeat(Byte.repr 97)n.
Definition argument_cases:list(list(list Byte.int)):=
 [[shell_bytes];[a_bytes 1];[[]];[a_bytes 1;[]];[a_bytes 4096];[a_bytes 4097];
  repeat(a_bytes 1)64;repeat(a_bytes 1)65;repeat(a_bytes 4095)4;
  [a_bytes 4095;a_bytes 4095;a_bytes 4095;a_bytes 4096];
  [map Byte.repr[195;169]];[map Byte.repr[255]]].
Definition sources_admissibleb sources:=
 (1<=?Z.of_nat(length sources))&&(Z.of_nat(length sources)<=?2147483647-16)&&
 forallb(fun bytes=>forallb(fun b=>negb(Byte.eq b Byte.zero))bytes&&
 (Z.of_nat(length bytes)+1<=?Int64.max_unsigned))sources.
Lemma sources_admissible_sound sources : sources_admissibleb sources=true -> admissible_guest_sources sources.
Proof.
 intros VALID;unfold sources_admissibleb in VALID;rewrite !andb_true_iff in VALID.
 destruct VALID as[[LOW HIGH]STRINGS];apply Z.leb_le in LOW,HIGH.
 split;[lia|];split;[exact HIGH|];apply Forall_forall;intros bytes IN.
 rewrite forallb_forall in STRINGS;specialize(STRINGS bytes IN);apply andb_true_iff in STRINGS.
 destruct STRINGS as[NONZERO SIZE];split;[|apply Z.leb_le;exact SIZE].
 apply Forall_forall;intros b PRESENT;rewrite forallb_forall in NONZERO;specialize(NONZERO b PRESENT).
 apply negb_true_iff in NONZERO;intro EQ;subst b;rewrite Byte.eq_true in NONZERO;discriminate.
Qed.
Theorem argument_cases_admissible : forallb sources_admissibleb argument_cases=true.
Proof. vm_compute;reflexivity. Qed.
Theorem argument_cases_outcomes : map(argument_scan_bytes 16 0)argument_cases=
 [arguments_accepted 8;arguments_accepted 2;arguments_rejected 16 0;arguments_rejected 17 2;
  arguments_accepted 4097;arguments_rejected 16 0;arguments_accepted 128;arguments_accepted 130;
  arguments_accepted 16384;arguments_accepted 16385;arguments_accepted 3;arguments_accepted 2].
Proof. vm_compute;reflexivity. Qed.
Definition case_rejected sources:=match argument_scan_bytes 16 0 sources with
|arguments_rejected _ _=>true
|arguments_accepted total=>bounds_rejected(16+Z.of_nat(length sources))total minimal_values end.
Theorem argument_cases_combined : map case_rejected argument_cases=
 [false;false;true;true;false;true;false;true;false;true;false;false].
Proof. vm_compute;reflexivity. Qed.
Theorem every_argument_case_allocated cell sources : In sources argument_cases ->
 exists initial m argv inputs count final,
 Genv.init_mem Main.prog=Some initial /\ map guest_bytes inputs=sources /\
 (count<=26*length sources+13)%nat /\ string_path main_ge cell
 (State f_main argument_suffix Kstop(Maps.PTree.empty _)(argument_witness_env argv(16+Z.of_nat(length sources)))m)
 count(argument_endpoint(argument_scan_bytes 16 0 sources)(Maps.PTree.empty _)final Kstop m).
Proof.
 intros IN;pose proof argument_cases_admissible as VALID;rewrite forallb_forall in VALID.
 destruct(allocated_argument_source cell sources(sources_admissible_sound sources(VALID sources IN)))
 as[initial[m[argv[inputs[count[final[INIT[OLD[BYTES[BOUND PATH]]]]]]]]]].
 exists initial,m,argv,inputs,count,final;auto.
Qed.
Theorem repeated_shell_pointer_allocated cell :
 exists initial m argv p count final,
 Genv.init_mem Main.prog=Some initial /\
 guest_arguments_owned m argv Ptrofs.zero 16
 [{|guest_pointer:=p;guest_bytes:=shell_bytes|};{|guest_pointer:=p;guest_bytes:=shell_bytes|}] /\
 (count<=65)%nat /\ string_path main_ge cell
 (State f_main argument_suffix Kstop(Maps.PTree.empty _)(argument_witness_env argv 18)m)count
 (argument_endpoint(arguments_accepted 16)(Maps.PTree.empty _)final Kstop m).
Proof.
 destruct(allocated_aliased_arguments cell shell_bytes)as[initial[m[argv[p[count[final[INIT[OLD[OWN[BOUND PATH]]]]]]]]]].
 - repeat constructor;vm_compute;discriminate.
 - vm_compute;congruence.
 - exists initial,m,argv,p,count,final;auto.
Qed.
Theorem every_combined_case_allocated cell sources : In sources argument_cases ->
 exists initial configured m argv inputs count final,
 Genv.init_mem Main.prog=Some initial /\ map guest_bytes inputs=sources /\
 (count<=26*length sources+154)%nat /\ string_path main_ge cell
 (State f_main argument_suffix Kstop(Maps.PTree.empty _)(argument_witness_env argv(16+Z.of_nat(length sources)))m)
 count(argument_bounds_endpoint(16+Z.of_nat(length sources))inputs minimal_values(Maps.PTree.empty _)final Kstop m) /\
 MainMemory.policy_stores main_policy_block 0 initial minimal_values configured.
Proof.
 intros IN;pose proof argument_cases_admissible as VALID;rewrite forallb_forall in VALID.
 destruct(allocated_argument_bounds cell sources minimal_values(sources_admissible_sound sources(VALID sources IN)))
 as[initial[configured[m[argv[inputs[count[final[INIT[STORES[OLD[BYTES[BOUND PATH]]]]]]]]]]]].
 - reflexivity.
 - repeat constructor;cbn;lia.
 - exists initial,configured,m,argv,inputs,count,final;auto.
Qed.
Theorem every_argument_case_loss cell sources : In sources argument_cases ->
 exists m argv count,
 forall n,(n<=count)%nat -> exists events,string_cost events=n /\
 string_steps main_ge cell
 (live(State f_main argument_suffix Kstop(Maps.PTree.empty _)(argument_witness_env argv(16+Z.of_nat(length sources)))m))
 (events++[string_loss])(dead m).
Proof.
 intros IN;destruct(every_argument_case_allocated cell sources IN)
 as[initial[m[argv[inputs[count[final[INIT[BYTES[BOUND PATH]]]]]]]]].
 exists m,argv,count;intros n N;exact(string_path_loss_every_prefix _ _ _ _ _ PATH n N).
Qed.
