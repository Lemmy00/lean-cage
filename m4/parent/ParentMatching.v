(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-parent.history: Preserve actual observations and ordered source memory. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine Library.
From LeanCageMainNumber Require Import NumberMath NumberMemory NumberStorage.
From LeanCageMain Require Import Main MainStructure MainMemory.
From LeanCageBounds Require Import BoundsMemory.
From LeanCageArguments Require Import ArgumentMemory.
From LeanCageValidation Require Import StringRegion ValidationStructure ValidationValues ValidationAllocation.
From LeanCageInitialization Require Import AssemblyRegions StoreFrames ConfigurationMemory InitializationSource.
From LeanCageParent Require Import ParentMachine ParentRegion ParentLift ParentStructure ParentFinish ParentControl
 ParentAfterParse ParentSource ParentMemory ParentFrontier ParentRuns TraceRegion TraceExecution ParentCost.
Import ListNotations.
Open Scope nat_scope.
Theorem parent_initialization_matching cell e le before k argc argv ofs p bytes output export tree stdin export_bytes tree_bytes stdin_bytes x rest values value :
 decimal_number bytes=Some value->(0<value<=2147483647)%Z->
 e!_number=None->(parent_guard_bad(decimal_number bytes)=false->e!_getppid=None)->e!_parent=Some(output,tulong)->
 Mem.loadv Mptr before(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 96)))=Some(address_value p)->
 number_input before(address_block p)(Ptrofs.repr(address_offset p))bytes->number_output before output Ptrofs.zero->
 argv<>output->address_block export<>output->address_block tree<>output->address_block stdin<>output->
 Forall(fun arg=>address_block(guest_pointer arg)<>output)(x::rest)->main_policy_block<>output->parent_literal_separation output->
 (17<=argc<=2147483647)%Z->(16+Z.of_nat(length(x::rest))=argc)%Z->guest_table_span ofs argc->
 guest_arguments_owned before argv ofs 16(x::rest)->setup_separate argv->
 Forall(fun arg=>setup_separate(address_block(guest_pointer arg)))(x::rest)->
 setup_separate(address_block tree)->setup_separate(address_block stdin)->
 policy_image before values->literals_owned before->
 e!_strcmp=None->e!_strlen=None->e!_policy__1=None->e!___stringlit_133=None->e!___stringlit_132=None->
 e!___stringlit_135=None->e!___stringlit_134=None->e!___stringlit_56=None->
 e!_tree_digest=None->e!_stdin_digest=None->e!_digest_text=None->
 le!_argv=Some(Vptr argv ofs)->le!_argc=Some(Vint(Int.repr argc))->
 Mem.loadv Mptr before(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 104)))=Some(address_value export)->
 Mem.loadv Mptr before(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 112)))=Some(address_value tree)->
 Mem.loadv Mptr before(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 120)))=Some(address_value stdin)->
 c_string before export export_bytes->c_string before tree tree_bytes->c_string before stdin stdin_bytes->
 Mem.valid_access before Mint32 main_policy_block 80 Writable->
 Mem.valid_access before Mptr(symbol_block _tree_digest)0 Writable->
 Mem.valid_access before Mptr(symbol_block _stdin_digest)0 Writable->
 Mem.valid_access before Mptr main_policy_block 88 Writable->
 exists middle flagged tree_set configured after events endpoint,
 number_post before output Ptrofs.zero(decimal_number bytes)middle /\
 configuration_stores middle flagged tree_set configured(bytes_equal export_bytes files_bytes)tree stdin /\
 Mem.store Mptr configured main_policy_block 88(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 128)))=Some after /\
 parent_steps main_ge cell(live(State f_main(validation_suffix 15)k e le before))events(live endpoint) /\
 initialization_frontier middle configured after e le k argc export_bytes tree_bytes stdin_bytes x rest values endpoint /\observations events=[Int.repr value].
Proof.
 intros PARSED RANGE NUMBER GETPPID LOCAL PL INPUT OUTPUT PARGV PEXPORT PTREE PSTDIN PGUEST PPOLICY PLITERALS
 COUNT SIZE SPAN OWN ARGVSEP STRINGSEP TREESEP STDINSEP IMAGE LITERALS STRCMP STRLEN POLICY DISCARD FILES SHELL PYTHON NONE TREE STDIN DIGEST ARGV ARGC EL TL SL EO TO SO FW TW SW AW.
 assert(GLOBAL:e!_getppid=None).
 { apply GETPPID;rewrite PARSED;apply parent_guard_valid;exact RANGE. }
 destruct(parent_observation_execution cell e le before k argv ofs p bytes output value NUMBER GLOBAL LOCAL ARGV PL INPUT OUTPUT PARSED RANGE)
 as[prefix_count[middle[POST RUN]]].
 rewrite<-PARSED in POST.
 destruct(RUN(Int.repr value)0)as[mid[suffix[PREFIX[REGS[REG SUFFIX]]]]].
 rewrite Int.eq_true in PREFIX;change(parent_endpoint e mid k middle(negb true))with(State f_main(validation_suffix 16)k e mid middle)in PREFIX.
 assert(MEM:number_memory before output Ptrofs.zero(decimal_number bytes)middle)by(right;exact POST).
 assert(OWN':guest_arguments_owned middle argv ofs 16(x::rest))by(eapply parent_memory_arguments;eassumption).
 assert(IMAGE':policy_image middle values)by(eapply parent_memory_policy;eassumption).
 assert(LITERALS':literals_owned middle)by(eapply parent_memory_literals;eassumption).
 assert(EO':c_string middle export export_bytes)by(eapply parent_memory_string;eassumption).
 assert(TO':c_string middle tree tree_bytes)by(eapply parent_memory_string;eassumption).
 assert(SO':c_string middle stdin stdin_bytes)by(eapply parent_memory_string;eassumption).
 assert(EL':Mem.loadv Mptr middle(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 104)))=Some(address_value export))by(rewrite(number_memory_loadv_other _ _ _ _ _ _ _ _ MEM PARGV);exact EL).
 assert(TL':Mem.loadv Mptr middle(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 112)))=Some(address_value tree))by(rewrite(number_memory_loadv_other _ _ _ _ _ _ _ _ MEM PARGV);exact TL).
 assert(SL':Mem.loadv Mptr middle(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 120)))=Some(address_value stdin))by(rewrite(number_memory_loadv_other _ _ _ _ _ _ _ _ MEM PARGV);exact SL).
 assert(FW':Mem.valid_access middle Mint32 main_policy_block 80 Writable)by(eapply parent_memory_access;eassumption).
 assert(TW':Mem.valid_access middle Mptr(symbol_block _tree_digest)0 Writable)by(eapply parent_memory_access;eassumption).
 assert(SW':Mem.valid_access middle Mptr(symbol_block _stdin_digest)0 Writable)by(eapply parent_memory_access;eassumption).
 assert(AW':Mem.valid_access middle Mptr main_policy_block 88 Writable)by(eapply parent_memory_access;eassumption).
 destruct(initialization_certificate cell e mid middle k argc argv ofs export tree stdin export_bytes tree_bytes stdin_bytes x rest values
 COUNT SIZE SPAN OWN' ARGVSEP STRINGSEP TREESEP STDINSEP IMAGE' LITERALS' STRCMP STRLEN POLICY DISCARD FILES SHELL PYTHON NONE TREE STDIN DIGEST
 ltac:(rewrite(proj1 REGS);exact ARGV)ltac:(rewrite(proj2 REGS);exact ARGC)EL' TL' SL' EO' TO' SO' FW' TW' SW' AW')
 as[flagged[tree_set[configured[after[CONFIG[STORE CERT]]]]]].
 destruct(trace_actual _ _ _ _ _ _ _(trace_from_string _ _ _ _ _ _ [] CERT))as[tail[endpoint[TAIL[COST[MEMORY[OBS END]]]]]].
 cbn in OBS.
 exists middle,flagged,tree_set,configured,after,
 ((repeat parent_internal prefix_count++repeat parent_wait 0++parent_observed(Int.repr value)::repeat parent_internal suffix)++tail),endpoint.
 split;[exact POST|];split;[exact CONFIG|];split;[exact STORE|];split.
 - eapply parent_steps_trans;[exact PREFIX|exact TAIL].
 - split;[eapply initialization_frame;[exact REGS|exact END]|].
   apply parent_observation_trace;exact OBS.
Qed.
