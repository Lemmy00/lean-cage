(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.initialization: Actual stores, sequential memory and source boundaries. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine Library FreshMemoryDraft WriteAll.
From LeanCageMain Require Import Main MainStructure MainMemory MainSamples.
From LeanCageArguments Require Import StringMachine StringPath ArgumentMemory ArgumentWitnesses.
From LeanCageDigest Require Import DigestWitnesses.
From LeanCageValidation Require Import ValidationStructure ValidationValues ValidationAllocation.
From LeanCageInitialization Require Import FlagStores ConfigurationMemory ConfigurationStages InitializationAllocation.
Import ListNotations.
Open Scope Z_scope.
Theorem allocated_configuration_interruptions cell :
 exists initial numeric before argv flagged tree_set configured tree stdin,
 Genv.init_mem Main.prog=Some initial /\policy_stores main_policy_block 0 initial minimal_values numeric /\old_memory numeric before /\
 configuration_stores before flagged tree_set configured true tree stdin /\
 forall current,In current[before;flagged;tree_set;configured]->exists events endpoint,
 string_steps main_ge cell(live(State f_main(validation_suffix 17)Kstop empty_env(argument_witness_env argv 17)before))events(live endpoint) /\
 memory_of endpoint=current /\(string_cost events<=23)%nat /\
 string_steps main_ge cell(live(State f_main(validation_suffix 17)Kstop empty_env(argument_witness_env argv 17)before))(events++[string_loss])(dead current).
Proof.
 assert(VALID:Forall digest_input_admissible[files_bytes;none_bytes;none_bytes;shell_bytes]).
 { repeat(apply Forall_cons;[apply digest_input_admissible_sound;reflexivity|]);constructor. }
 destruct(allocated_setup_inputs minimal_values[files_bytes;none_bytes;none_bytes;shell_bytes]
 eq_refl ltac:(repeat constructor;cbn;lia)VALID ltac:(cbn;lia))
 as[initial[numeric[before[argv[inputs[INIT[STORES[OLD[BYTES[SPAN[ARGS[ARGVSEP[SEP[IMAGE[LITERALS WRITE]]]]]]]]]]]]]]].
 destruct inputs as[|export inputs];[discriminate BYTES|].
 destruct inputs as[|tree inputs];[discriminate BYTES|].
 destruct inputs as[|stdin inputs];[discriminate BYTES|].
 change(guest_bytes export::guest_bytes tree::guest_bytes stdin::map guest_bytes inputs=
 files_bytes::none_bytes::none_bytes::[shell_bytes])in BYTES.
 injection BYTES as EB TB SB TAIL.
 destruct ARGS as[EO[EL[TO[TL[SO[SL OWN]]]]]];destruct WRITE as[PW[FW[TW[SW AW]]]].
 destruct(configuration_stages cell empty_env(argument_witness_env argv 17)before Kstop argv Ptrofs.zero
 (guest_pointer export)(guest_pointer tree)(guest_pointer stdin)files_bytes
 eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(unfold argument_witness_env;WriteAll.lookup)ARGVSEP
 EL TL SL ltac:(rewrite<-EB;exact EO)ltac:(owned_literal)FW TW SW)
 as[flagged[tree_set[configured[CONFIG RESULT]]]].
 exists initial,numeric,before,argv,flagged,tree_set,configured,(guest_pointer tree),(guest_pointer stdin).
 split;[exact INIT|];split;[exact STORES|];split;[exact OLD|];split;[exact CONFIG|exact RESULT].
Qed.
