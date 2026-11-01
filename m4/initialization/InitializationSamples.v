(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.initialization: Actual stores, sequential memory and source boundaries. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine Library FreshMemoryDraft.
From LeanCageMain Require Import Main MainStructure MainMemory MainSamples.
From LeanCageBounds Require Import BoundsStructure BoundsSamples.
From LeanCageArguments Require Import StringMachine StringPath ArgumentMemory ArgumentWitnesses ArgumentSamples.
From LeanCageDigest Require Import DigestWitnesses.
From LeanCageValidation Require Import StringRegion ValidationStructure ValidationValues.
From LeanCageInitialization Require Import StoreFrames ConfigurationMemory InitializationSource InitializationWitnesses.
Import ListNotations.
Open Scope Z_scope.
Theorem allocated_initialization_execution cell export_bytes tree_bytes stdin_bytes sources values :
 admissible_guest_sources sources->digest_input_admissible export_bytes->
 digest_input_admissible tree_bytes->digest_input_admissible stdin_bytes->
 length values=10%nat->Forall(fun v=>0<=v<=Int64.max_unsigned)values->
 exists initial numeric before argv flagged tree_set configured after tree stdin events final,
 Genv.init_mem Main.prog=Some initial /\policy_stores main_policy_block 0 initial values numeric /\old_memory numeric before /\
 configuration_stores before flagged tree_set configured(bytes_equal export_bytes files_bytes)tree stdin /\
 Mem.store Mptr configured main_policy_block 88(Vptr argv(Ptrofs.repr 128))=Some after /\
 string_steps main_ge cell(live(State f_main(validation_suffix 16)Kstop empty_env
 (argument_witness_env argv(16+Z.of_nat(length sources)))before))events
 (live(initialization_result_state(initialization_result_of export_bytes tree_bytes stdin_bytes sources values)
 before configured after empty_env final Kstop)) /\
 (string_cost events<=26*length sources+4540)%nat /\
 setup_frame before(memory_of(initialization_result_state(initialization_result_of export_bytes tree_bytes stdin_bytes sources values)
 before configured after empty_env final Kstop)).
Proof.
 intros GUEST EXPORT TREE STDIN LEN RANGE.
 destruct(allocated_initialization_certificate cell export_bytes tree_bytes stdin_bytes sources values GUEST EXPORT TREE STDIN LEN RANGE)
 as[initial[numeric[before[argv[flagged[tree_set[configured[after[tree[stdin[INIT[STORES[OLD[CONFIG[STORE CERT]]]]]]]]]]]]]]].
 destruct(region_actual _ _ _ _ _ _ CERT)as[events[endpoint[RUN[BOUND[MEM[final END]]]]]];subst endpoint.
 exists initial,numeric,before,argv,flagged,tree_set,configured,after,tree,stdin,events,final.
 split;[exact INIT|];split;[exact STORES|];split;[exact OLD|];split;[exact CONFIG|];split;[exact STORE|];split;[exact RUN|];split;[exact BOUND|].
 eapply initialization_prefix_frame;[exact CONFIG|rewrite Ptrofs.add_zero_l;exact STORE|exact MEM].
Qed.
Record initialization_case := {
 export_text:list Byte.int;tree_text:list Byte.int;stdin_text:list Byte.int;
 guest_texts:list(list Byte.int);numeric_values:list Z;expected_result:initialization_result}.
Definition initialization_cases := [
 Build_initialization_case discard_bytes none_bytes none_bytes[ValidationStructure.shell_bytes]minimal_values(initialization_ready 8);
 Build_initialization_case files_bytes none_bytes none_bytes[python_bytes]maximum_values(initialization_ready 23);
 Build_initialization_case files_bytes(a_bytes 64)(repeat(Byte.repr 102)64)[ValidationStructure.shell_bytes;a_bytes 1]minimal_values(initialization_ready 10);
 Build_initialization_case discard_bytes none_bytes none_bytes(ValidationStructure.shell_bytes::repeat(a_bytes 1)63)minimal_values(initialization_ready 134);
 Build_initialization_case files_bytes none_bytes none_bytes[ValidationStructure.shell_bytes;a_bytes 4095;a_bytes 4095;a_bytes 4095;a_bytes 4087]maximum_values(initialization_ready 16384);
 Build_initialization_case files_bytes none_bytes none_bytes[ValidationStructure.shell_bytes;map Byte.repr[195;169];[Byte.repr 255]]minimal_values(initialization_ready 13);
 Build_initialization_case [][][][[]](replace_value 0 0)rejected_export;
 Build_initialization_case discard_bytes []none_bytes[ValidationStructure.shell_bytes]minimal_values rejected_digest;
 Build_initialization_case files_bytes none_bytes(repeat(Byte.repr 65)64)[ValidationStructure.shell_bytes]minimal_values rejected_digest;
 Build_initialization_case files_bytes [][][[]]minimal_values rejected_digest;
 Build_initialization_case files_bytes none_bytes none_bytes[[]]minimal_values rejected_executable;
 Build_initialization_case discard_bytes none_bytes none_bytes[map Byte.repr[47;98;105;110;47;98;97;115;104];[]](replace_value 0 0)rejected_executable;
 Build_initialization_case files_bytes none_bytes none_bytes[ValidationStructure.shell_bytes;[]]minimal_values(rejected_argument 17 8);
 Build_initialization_case discard_bytes none_bytes none_bytes[ValidationStructure.shell_bytes;a_bytes 4097]minimal_values(rejected_argument 17 8);
 Build_initialization_case files_bytes none_bytes none_bytes(ValidationStructure.shell_bytes::repeat(a_bytes 1)64)minimal_values(rejected_policy 136);
 Build_initialization_case files_bytes none_bytes none_bytes[ValidationStructure.shell_bytes;a_bytes 4095;a_bytes 4095;a_bytes 4095;a_bytes 4088]maximum_values(rejected_policy 16385)]++
 map(fun values=>Build_initialization_case files_bytes none_bytes none_bytes[ValidationStructure.shell_bytes]values(rejected_policy 8))rejected_numeric_values.
Definition initialization_case_valid c := sources_admissibleb(guest_texts c)&&
 digest_input_admissibleb(export_text c)&&digest_input_admissibleb(tree_text c)&&digest_input_admissibleb(stdin_text c)&&
 Nat.eqb(length(numeric_values c))10&&forallb(fun v=>(0<=?v)&&(v<=?Int64.max_unsigned))(numeric_values c).
Theorem initialization_cases_valid : Forall(fun c=>initialization_case_valid c=true)initialization_cases.
Proof. repeat(apply Forall_cons;[vm_compute;reflexivity|]);constructor. Qed.
Theorem initialization_cases_results : Forall(fun c=>initialization_result_of(export_text c)(tree_text c)(stdin_text c)(guest_texts c)(numeric_values c)=expected_result c)initialization_cases.
Proof. repeat(apply Forall_cons;[vm_compute;reflexivity|]);constructor. Qed.
Definition initialization_accepted result := match result with initialization_ready _=>true|_=>false end.
Theorem initialization_case_counts :
 (length initialization_cases,length(filter(fun c=>initialization_accepted(expected_result c))initialization_cases))=(35,6)%nat.
Proof. split;reflexivity. Qed.
Theorem initialization_samples_source cell c : In c initialization_cases->
 exists initial numeric before argv flagged tree_set configured after tree stdin events final,
 Genv.init_mem Main.prog=Some initial /\policy_stores main_policy_block 0 initial(numeric_values c)numeric /\old_memory numeric before /\
 configuration_stores before flagged tree_set configured(bytes_equal(export_text c)files_bytes)tree stdin /\
 Mem.store Mptr configured main_policy_block 88(Vptr argv(Ptrofs.repr 128))=Some after /\
 string_steps main_ge cell(live(State f_main(validation_suffix 16)Kstop empty_env
 (argument_witness_env argv(16+Z.of_nat(length(guest_texts c))))before))events
 (live(initialization_result_state(expected_result c)before configured after empty_env final Kstop)) /\
 (string_cost events<=26*length(guest_texts c)+4540)%nat /\
 setup_frame before(memory_of(initialization_result_state(expected_result c)before configured after empty_env final Kstop)).
Proof.
 intros IN;pose proof initialization_cases_valid as VALID;pose proof initialization_cases_results as RESULT.
 rewrite Forall_forall in VALID,RESULT;specialize(VALID c IN);specialize(RESULT c IN).
 unfold initialization_case_valid in VALID;rewrite !andb_true_iff in VALID.
 destruct VALID as[[[[[GUEST EXPORT]TREE]STDIN]LEN]RANGE];apply Nat.eqb_eq in LEN.
 rewrite<-RESULT;apply allocated_initialization_execution.
 - apply sources_admissible_sound;exact GUEST.
 - apply digest_input_admissible_sound;exact EXPORT.
 - apply digest_input_admissible_sound;exact TREE.
 - apply digest_input_admissible_sound;exact STDIN.
 - exact LEN.
 - rewrite Forall_forall;intros v PRESENT;rewrite forallb_forall in RANGE;specialize(RANGE v PRESENT).
   rewrite andb_true_iff,!Z.leb_le in RANGE;exact RANGE.
Qed.
