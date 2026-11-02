(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-parent.history: Preserve actual observations and ordered source memory. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine Library LibraryMachine StoreSteps ScalarMemory ClightSteps WriteAll.
From LeanCageMainNumber Require Import NumberMath NumberMemory NumberStorage NumberInitial.
From LeanCageMain Require Import Main MainStructure MainMemory MainValues MainControl MainLoop MainFields MainEntry MainSource.
From LeanCageBounds Require Import BoundsMemory.
From LeanCageArguments Require Import ArgumentMemory StringMachine.
From LeanCageValidation Require Import StringRegion ValidationStructure ValidationValues ValidationAllocation.
From LeanCageInitialization Require Import StoreFrames ConfigurationMemory InitializationSource.
From LeanCageParent Require Import ParentMachine ParentRegion ParentLift ParentPaths ParentStructure ParentSource ParentMemory ParentInitialization ParentMatching ParentRuns ParentFrontier
 NumericFrame NumericSource NumericMemory TraceRegion.
Import ListNotations.
Open Scope nat_scope.
Theorem numeric_validation_matching cell e le before k fields inputs argc argv ofs p bytes output export tree stdin export_bytes tree_bytes stdin_bytes x rest value :
 numeric_complete inputs=true->decimal_number bytes=Some value->(0<value<=2147483647)%Z->
 length inputs=10->numeric_entry_buffers before fields argv ofs inputs->numeric_locals e fields->
 numeric_separate fields(address_block p)->numeric_separate fields(address_block export)->
 numeric_separate fields(address_block tree)->numeric_separate fields(address_block stdin)->
 Forall(fun arg=>numeric_separate fields(address_block(guest_pointer arg)))(x::rest)->numeric_literal_separation fields->
 e!_number=None->(parent_guard_bad(decimal_number bytes)=false->e!_getppid=None)->e!_parent=Some(output,tulong)->
 Mem.loadv Mptr before(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 96)))=Some(address_value p)->
 number_input before(address_block p)(Ptrofs.repr(address_offset p))bytes->number_output before output Ptrofs.zero->
 argv<>output->address_block export<>output->address_block tree<>output->address_block stdin<>output->
 Forall(fun arg=>address_block(guest_pointer arg)<>output)(x::rest)->main_policy_block<>output->parent_literal_separation output->
 (17<=argc<=2147483647)%Z->(16+Z.of_nat(length(x::rest))=argc)%Z->guest_table_span ofs argc->
 guest_arguments_owned before argv ofs 16(x::rest)->setup_separate argv->
 Forall(fun arg=>setup_separate(address_block(guest_pointer arg)))(x::rest)->
 setup_separate(address_block tree)->setup_separate(address_block stdin)->
 literals_owned before->
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
 exists initialized numeric middle flagged tree_set configured after events endpoint,
 scalar_stores fields before(map field_cell policy_fields)initialized /\
 policy_stores main_policy_block 0 initialized(numeric_values inputs)numeric /\
 number_post numeric output Ptrofs.zero(decimal_number bytes)middle /\
 configuration_stores middle flagged tree_set configured(bytes_equal export_bytes files_bytes)tree stdin /\
 Mem.store Mptr configured main_policy_block 88(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 128)))=Some after /\
 parent_steps main_ge cell(live(State f_main numeric_region k e le before))events(live endpoint) /\
 initialization_frontier middle configured after e le k argc export_bytes tree_bytes stdin_bytes x rest(numeric_values inputs)endpoint /\observations events=[Int.repr value].
Proof.
 intros COMPLETE PARSED RANGE LEN BUFFERS LOCALS NINPUT NEXPORT NTREE NSTDIN NGUEST NLITERALS
 NUMBER GETPPID LOCAL PL INPUT OUTPUT PARGV PEXPORT PTREE PSTDIN PGUEST PPOLICY PLITERALS
 COUNT SIZE SPAN OWN ARGVSEP STRINGSEP TREESEP STDINSEP LITERALS STRCMP STRLEN POLICY DISCARD FILES SHELL PYTHON NONE TREE STDIN DIGEST ARGV ARGC EL TL SL EO TO SO FW TW SW AW.
 destruct(numeric_region_framed before fields argv ofs inputs e le k LEN BUFFERS LOCALS POLICY ARGV)
 as[initialized[numeric_count[numeric[final[FIELDS[STORES[REGS[ARGFRAME PATH]]]]]]]].
 assert(FRAME:validation_frame le final).
 { split;[rewrite(proj1 REGS),ARGV;reflexivity|exact ARGFRAME]. }
 assert(NUMFRAME:numeric_write_frame fields before numeric).
   { apply numeric_final_frame with(initialized:=initialized)(values:=numeric_values inputs);[pose proof(numeric_values_length inputs);lia|exact FIELDS|exact STORES]. }
   assert(TABLESEP:numeric_separate fields argv).
   { destruct BUFFERS as[FNE[ANE[AF REST]]];split;assumption. }
   assert(INPUT':number_input numeric(address_block p)(Ptrofs.repr(address_offset p))bytes)by(eapply numeric_frame_input;eassumption).
   assert(OUTPUT':number_output numeric output Ptrofs.zero)by(eapply numeric_frame_output;eassumption).
   assert(PL':Mem.loadv Mptr numeric(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 96)))=Some(address_value p))by(eapply numeric_frame_load;eassumption).
   assert(OWN':guest_arguments_owned numeric argv ofs 16(x::rest))by(eapply numeric_frame_arguments;eassumption).
   assert(IMAGE':policy_image numeric(numeric_values inputs))by(eapply complete_numeric_image;eassumption).
   assert(LITERALS':literals_owned numeric)by(eapply numeric_frame_literals;eassumption).
   assert(EO':c_string numeric export export_bytes)by(eapply numeric_frame_string;eassumption).
   assert(TO':c_string numeric tree tree_bytes)by(eapply numeric_frame_string;eassumption).
   assert(SO':c_string numeric stdin stdin_bytes)by(eapply numeric_frame_string;eassumption).
   assert(EL':Mem.loadv Mptr numeric(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 104)))=Some(address_value export))by(eapply numeric_frame_load;eassumption).
   assert(TL':Mem.loadv Mptr numeric(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 112)))=Some(address_value tree))by(eapply numeric_frame_load;eassumption).
   assert(SL':Mem.loadv Mptr numeric(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 120)))=Some(address_value stdin))by(eapply numeric_frame_load;eassumption).
   assert(FW':Mem.valid_access numeric Mint32 main_policy_block 80 Writable)by(eapply numeric_frame_access;eassumption).
   assert(TW':Mem.valid_access numeric Mptr(symbol_block _tree_digest)0 Writable)by(eapply numeric_frame_access;eassumption).
   assert(SW':Mem.valid_access numeric Mptr(symbol_block _stdin_digest)0 Writable)by(eapply numeric_frame_access;eassumption).
   assert(AW':Mem.valid_access numeric Mptr main_policy_block 88 Writable)by(eapply numeric_frame_access;eassumption).
   destruct(parent_initialization_matching cell e final numeric k argc argv ofs p bytes output export tree stdin export_bytes tree_bytes stdin_bytes x rest(numeric_values inputs)value
    PARSED RANGE NUMBER GETPPID LOCAL PL' INPUT' OUTPUT' PARGV PEXPORT PTREE PSTDIN PGUEST PPOLICY PLITERALS
    COUNT SIZE SPAN OWN' ARGVSEP STRINGSEP TREESEP STDINSEP IMAGE' LITERALS' STRCMP STRLEN POLICY DISCARD FILES SHELL PYTHON NONE TREE STDIN DIGEST
    (proj1 REGS)ltac:(rewrite ARGFRAME;exact ARGC)EL' TL' SL' EO' TO' SO' FW' TW' SW' AW')
 as[middle[flagged[tree_set[configured[after[tail[endpoint[POST[CONFIG[STORE[TAIL[END OBS]]]]]]]]]]]].
 exists initialized,numeric,middle,flagged,tree_set,configured,after,
 (repeat parent_internal numeric_count++parent_internal::tail),endpoint.
 split;[exact FIELDS|];split;[exact STORES|];split;[exact POST|];split;[exact CONFIG|];split;[exact STORE|];split.
 - eapply parent_steps_trans;[eapply parent_store_actual;exact PATH|].
   unfold numeric_endpoint;rewrite COMPLETE;econstructor;[|exact TAIL].
   unfold parent_internal,string_source;apply ParentMachine.previous_step;apply StringMachine.previous_step;apply original_step.
   apply internal;[exact I|apply step_skip_seq].
 - split;[eapply initialization_frame;[exact FRAME|exact END]|].
   rewrite observations_append,(observations_repeat_empty parent_internal numeric_count eq_refl);exact OBS.
Qed.
