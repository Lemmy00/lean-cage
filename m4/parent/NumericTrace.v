(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-parent.history: Preserve actual observations and ordered source memory. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine Library StoreSteps ScalarMemory ClightSteps WriteAll.
From LeanCageMainNumber Require Import NumberMath NumberMemory NumberStorage NumberInitial.
From LeanCageMain Require Import Main MainStructure MainMemory MainValues MainControl MainLoop MainFields MainEntry MainSource.
From LeanCageBounds Require Import BoundsMemory.
From LeanCageArguments Require Import ArgumentMemory.
From LeanCageValidation Require Import StringRegion ValidationStructure ValidationValues ValidationAllocation.
From LeanCageInitialization Require Import StoreFrames ConfigurationMemory InitializationSource.
From LeanCageParent Require Import ParentMachine ParentRegion ParentLift ParentPaths ParentStructure ParentSource ParentMemory ParentInitialization
 NumericFrame NumericSource NumericMemory TraceRegion TraceExecution TraceCut ParentTrace TraceInitialization FrontierShapes.
Import ListNotations.
Open Scope nat_scope.
Definition numeric_trace_contract cell e le before k fields inputs initialized numeric_count numeric final
 argc argv ofs bytes output tree stdin export_bytes tree_bytes stdin_bytes x rest :=
 if numeric_complete inputs then
 exists parser_count middle flagged tree_set configured after,
 number_post numeric output Ptrofs.zero(decimal_number bytes)middle /\
 configuration_stores middle flagged tree_set configured(bytes_equal export_bytes files_bytes)tree stdin /\
 Mem.store Mptr configured main_policy_block 88(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 128)))=Some after /\
 frontier_guarantee cell
 (fun current=>numeric_region_memory before initialized fields inputs current \/
 traced_initialization_memory numeric output(decimal_number bytes)middle flagged tree_set configured after current)
 (traced_initialization_frontier middle configured after e final k argc bytes export_bytes tree_bytes stdin_bytes x rest(numeric_values inputs))
 (numeric_count+1+((9+parser_count+28)+(26*length(x::rest)+4540)))
 (State f_main numeric_region k e le before)
 else frontier_guarantee cell(numeric_region_memory before initialized fields inputs)
 (fun history s=>history=[] /\s=numeric_failure_state e final(Kseq after_numeric k)numeric)numeric_count
 (State f_main numeric_region k e le before).
Theorem numeric_trace_source cell e le before k fields inputs argc argv ofs p bytes output export tree stdin export_bytes tree_bytes stdin_bytes x rest :
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
 exists initialized numeric_count numeric final,
 scalar_stores fields before(map field_cell policy_fields)initialized /\
 policy_stores main_policy_block 0 initialized(numeric_values inputs)numeric /\
 validation_frame le final /\
 numeric_trace_contract cell e le before k fields inputs initialized numeric_count numeric final
 argc argv ofs bytes output tree stdin export_bytes tree_bytes stdin_bytes x rest.
Proof.
 intros LEN BUFFERS LOCALS NINPUT NEXPORT NTREE NSTDIN NGUEST NLITERALS
 NUMBER GETPPID LOCAL PL INPUT OUTPUT PARGV PEXPORT PTREE PSTDIN PGUEST PPOLICY PLITERALS
 COUNT SIZE SPAN OWN ARGVSEP STRINGSEP TREESEP STDINSEP LITERALS STRCMP STRLEN POLICY DISCARD FILES SHELL PYTHON NONE TREE STDIN DIGEST ARGV ARGC EL TL SL EO TO SO FW TW SW AW.
 destruct(numeric_region_framed before fields argv ofs inputs e le k LEN BUFFERS LOCALS POLICY ARGV)
 as[initialized[numeric_count[numeric[final[FIELDS[STORES[REGS[ARGFRAME PATH]]]]]]]].
 assert(FRAME:validation_frame le final).
 { split;[rewrite(proj1 REGS),ARGV;reflexivity|exact ARGFRAME]. }
 exists initialized,numeric_count,numeric,final;split;[exact FIELDS|];split;[exact STORES|];split;[exact FRAME|].
 assert(MEM:numeric_region_memory before initialized fields inputs numeric).
 { right;exists(numeric_values inputs),[];split;[rewrite app_nil_r;reflexivity|exact STORES]. }
 unfold numeric_trace_contract;destruct(numeric_complete inputs)eqn:COMPLETE.
 - assert(NUMFRAME:numeric_write_frame fields before numeric).
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
   destruct(traced_initialization_certificate cell e final numeric k argc argv ofs p bytes output export tree stdin export_bytes tree_bytes stdin_bytes x rest(numeric_values inputs)
    NUMBER GETPPID LOCAL PL' INPUT' OUTPUT' PARGV PEXPORT PTREE PSTDIN PGUEST PPOLICY PLITERALS
    COUNT SIZE SPAN OWN' ARGVSEP STRINGSEP TREESEP STDINSEP IMAGE' LITERALS' STRCMP STRLEN POLICY DISCARD FILES SHELL PYTHON NONE TREE STDIN DIGEST
    (proj1 REGS)ltac:(rewrite ARGFRAME;exact ARGC)EL' TL' SL' EO' TO' SO' FW' TW' SW' AW')
    as[parser_count[middle[flagged[tree_set[configured[after[POST[CONFIG[STORE CERT]]]]]]]]].
   exists parser_count,middle,flagged,tree_set,configured,after;split;[exact POST|];split;[exact CONFIG|];split;[exact STORE|].
   apply frontier_guaranteed;[intros h s END;eapply traced_frontier_selected;exact END|].
   replace(numeric_count+1+((9+parser_count+28)+(26*length(x::rest)+4540)))with
    (numeric_count+S((9+parser_count+28)+(26*length(x::rest)+4540)))by lia.
   eapply trace_store_path.
   + eapply number_path_implication;[intros current GOOD;left;exact GOOD|exact PATH].
   + unfold numeric_endpoint;rewrite COMPLETE;eapply trace_store_path with(count:=1).
     * eapply store_next;[left;exact MEM|apply unchanged_store_edge;WriteAll.structural|].
       apply store_done;left;exact MEM.
     * change after_numeric with(validation_suffix 15);eapply trace_convert;[exact CERT|intros current GOOD;right;exact GOOD|intros h s RESULT;exact RESULT].
 - apply frontier_guaranteed;[intros h s END;eapply numeric_rejection_selected;exact END|].
   replace numeric_count with(numeric_count+0)at 1 by lia.
   eapply trace_store_path;[exact PATH|].
   unfold numeric_endpoint;rewrite COMPLETE;apply trace_stop;[exact MEM|split;reflexivity].
Qed.
