(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.strings: Actual caller checks, owned bytes and explicit execution boundaries. *)
From Stdlib Require Import List ZArith Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Clight.
Require Import Library FreshMemoryDraft Machine.
From LeanCageMain Require Import Main MainStructure.
From LeanCageArguments Require Import StringMachine StringPath ArgumentWitnesses.
From LeanCageDigest Require Import DigestWords DigestWitnesses.
From LeanCageValidation Require Import ValidationStructure ValidationValues ValidationFinish DigestCaller
 ExportCaller ExecutableCaller ModeCaller ValidationAllocation ValidationWitnesses.
Import ListNotations.
Open Scope Z_scope.
Record mode_case := {mode_count:Z;mode_text:list Byte.int;mode_accept:bool}.
Definition mode_cases := [
 Build_mode_case 17 plan_bytes true;Build_mode_case 17 check_bytes true;
 Build_mode_case 16 plan_bytes false;Build_mode_case 0 check_bytes false;
 Build_mode_case(-1)plan_bytes false;Build_mode_case(-2147483648)[]false;
 Build_mode_case 2147483647 plan_bytes true;Build_mode_case 17[]false;
 Build_mode_case 17(map Byte.repr[77;51;80;76;65;78;50])false;
 Build_mode_case 17[Byte.repr 255]false].
Definition export_cases := [(discard_bytes,true);(files_bytes,true);([],false);
 (map Byte.repr[68;105;115;99;97;114;100],false);
 (map Byte.repr[114;101;103;117;108;97;114;45;102;105;108;101],false);
 (files_bytes++[Byte.repr 32],false);([Byte.repr 255],false)].
Definition executable_cases := [(shell_bytes,true);(python_bytes,true);
 (map Byte.repr[47;98;105;110;47;98;97;115;104],false);
 (map Byte.repr[47;117;115;114;47;98;105;110;47;112;121;116;104;111;110;51],false);
 ([],false);(shell_bytes++[Byte.repr 32],false);([Byte.repr 255],false)].
Record digest_case := {tree_text:list Byte.int;stdin_text:list Byte.int;pair_accept:bool}.
Definition digest_cases := [
 Build_digest_case none_bytes none_bytes true;
 Build_digest_case(repeat(Byte.repr 97)64)none_bytes true;
 Build_digest_case none_bytes(repeat(Byte.repr 102)64)true;
 Build_digest_case(repeat(Byte.repr 48)64)(concat(repeat(map Byte.repr[48;57;97;102])16))true;
 Build_digest_case[]none_bytes false;Build_digest_case none_bytes[]false;
 Build_digest_case(repeat(Byte.repr 97)63)(repeat(Byte.repr 97)64)false;
 Build_digest_case(repeat(Byte.repr 97)64)(repeat(Byte.repr 102)65)false;
 Build_digest_case(repeat(Byte.repr 65)64)none_bytes false;
 Build_digest_case none_bytes[Byte.repr 255]false;
 Build_digest_case[][]false;
 Build_digest_case none_bytes(map Byte.repr[78;111;110;101])false].
Lemma mode_cases_checked : Forall(fun c=>
 (Int.min_signed<=?mode_count c)=true /\(mode_count c<=?Int.max_signed)=true /\
 digest_input_admissibleb(mode_text c)=true /\negb(mode_bad(mode_count c)(mode_text c))=mode_accept c)mode_cases.
Proof. repeat(apply Forall_cons;[vm_compute;repeat constructor|]);constructor. Qed.
Lemma export_cases_checked : Forall(fun c=>digest_input_admissibleb(fst c)=true /\negb(export_bad(fst c))=snd c)export_cases.
Proof. repeat(apply Forall_cons;[vm_compute;repeat constructor|]);constructor. Qed.
Lemma executable_cases_checked : Forall(fun c=>digest_input_admissibleb(fst c)=true /\negb(executable_bad(fst c))=snd c)executable_cases.
Proof. repeat(apply Forall_cons;[vm_compute;repeat constructor|]);constructor. Qed.
Lemma digest_cases_checked : Forall(fun c=>digest_input_admissibleb(tree_text c)=true /\
 digest_input_admissibleb(stdin_text c)=true /\
 (Z.of_nat(length(tree_text c)+length(stdin_text c))<=?158)=true /\
 negb(digest_pair_bad(tree_text c)(stdin_text c))=pair_accept c)digest_cases.
Proof. repeat(apply Forall_cons;[vm_compute;repeat constructor|]);constructor. Qed.
Theorem mode_samples_source cell c : In c mode_cases->
 exists initial m argv events endpoint,Genv.init_mem Main.prog=Some initial /\ old_memory initial m /\
 string_steps main_ge cell(live(State f_main(validation_suffix 2)Kstop empty_env(argument_witness_env argv(mode_count c))m))events(live endpoint) /\
 (string_cost events<=31)%nat /\selection_frontier 2 empty_env(argument_witness_env argv(mode_count c))Kstop m(negb(mode_accept c))endpoint.
Proof.
 intros IN;pose proof mode_cases_checked as VALID;rewrite Forall_forall in VALID.
 destruct(VALID c IN)as[LOW[HIGH[OWN RESULT]]];apply Z.leb_le in LOW,HIGH.
 destruct(allocated_mode_check cell(mode_count c)(mode_text c)ltac:(lia)(digest_input_admissible_sound _ OWN))
 as[initial[m[argv[events[endpoint[INIT[OLD[RUN[BOUND END]]]]]]]]].
 exists initial,m,argv,events,endpoint;rewrite<-RESULT,Bool.negb_involutive;auto.
Qed.
Theorem export_samples_source cell c : In c export_cases->
 exists initial m argv events endpoint,Genv.init_mem Main.prog=Some initial /\ old_memory initial m /\
 string_steps main_ge cell(live(State f_main(validation_suffix 16)Kstop empty_env(argument_witness_env argv 17)m))events(live endpoint) /\
 (string_cost events<=26)%nat /\selection_frontier 16 empty_env(argument_witness_env argv 17)Kstop m(negb(snd c))endpoint.
Proof.
 intros IN;pose proof export_cases_checked as VALID;rewrite Forall_forall in VALID.
 destruct(VALID c IN)as[OWN RESULT].
 destruct(allocated_export_check cell(fst c)(digest_input_admissible_sound _ OWN))
 as[initial[m[argv[events[endpoint[INIT[OLD[RUN[BOUND END]]]]]]]]].
 exists initial,m,argv,events,endpoint;rewrite<-RESULT,Bool.negb_involutive;auto.
Qed.
Theorem executable_samples_source cell c : In c executable_cases->
 exists initial configured m argv events endpoint,Genv.init_mem Main.prog=Some initial /\ old_memory initial configured /\
 Mem.store Mptr configured main_policy_block 88(Vptr argv(Ptrofs.repr 128))=Some m /\
 string_steps main_ge cell(live(State f_main(validation_suffix 22)Kstop empty_env(argument_witness_env argv 17)m))events(live endpoint) /\
 (string_cost events<=34)%nat /\selection_frontier 22 empty_env(argument_witness_env argv 17)Kstop m(negb(snd c))endpoint.
Proof.
 intros IN;pose proof executable_cases_checked as VALID;rewrite Forall_forall in VALID.
 destruct(VALID c IN)as[OWN RESULT].
 destruct(allocated_executable_check cell(fst c)(digest_input_admissible_sound _ OWN))
 as[initial[configured[m[argv[events[endpoint[INIT[OLD[STORE[RUN[BOUND END]]]]]]]]]]].
 exists initial,configured,m,argv,events,endpoint;rewrite<-RESULT,Bool.negb_involutive;auto 12.
Qed.
Theorem digest_samples_source cell c : In c digest_cases->
 exists initial m tree stdin events endpoint,Genv.init_mem Main.prog=Some initial /\ digest_pointer_setup initial tree stdin m /\
 string_steps main_ge cell(live(State f_main(validation_suffix 20)Kstop empty_env(create_undef_temps(fn_temps f_main))m))events(live endpoint) /\
 (string_cost events<=4300)%nat /\selection_frontier 20 empty_env(create_undef_temps(fn_temps f_main))Kstop m(negb(pair_accept c))endpoint.
Proof.
 intros IN;pose proof digest_cases_checked as VALID;rewrite Forall_forall in VALID.
 destruct(VALID c IN)as[TREE[STDIN[SIZE RESULT]]];apply Z.leb_le in SIZE.
 destruct(allocated_digest_pair_check cell(tree_text c)(stdin_text c)
 (proj1(digest_input_admissible_sound _ TREE))(proj1(digest_input_admissible_sound _ STDIN))SIZE)
 as[initial[m[tree[stdin[events[endpoint[INIT[SETUP[RUN[BOUND END]]]]]]]]]].
 exists initial,m,tree,stdin,events,endpoint;rewrite<-RESULT,Bool.negb_involutive;auto 12.
Qed.
Theorem validation_sample_counts :
 (length mode_cases,length(filter mode_accept mode_cases))=(10,3)%nat /\
 (length export_cases,length(filter snd export_cases))=(7,2)%nat /\
 (length executable_cases,length(filter snd executable_cases))=(7,2)%nat /\
 (length digest_cases,length(filter pair_accept digest_cases))=(12,4)%nat.
Proof. repeat split;reflexivity. Qed.
