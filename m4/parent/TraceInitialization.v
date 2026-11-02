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
 ParentAfterParse ParentSource ParentMemory ParentFrontier TraceRegion TraceExecution ParentTrace.
Import ListNotations.
Open Scope nat_scope.
Definition traced_initialization_memory before output parsed middle flagged tree_set configured after current :=
 number_memory before output Ptrofs.zero parsed current \/initialization_prefix middle flagged tree_set configured after current.
Definition traced_initialization_frontier middle configured after e le k argc bytes export_bytes tree_bytes stdin_bytes x rest values history s :=
 (traced_parent_frontier e le k middle(decimal_number bytes)history s /\parent_rejection e le k middle(decimal_number bytes)s /\
  ((parent_guard_bad(decimal_number bytes)=true /\history=[]) \/
   (exists observed,history=[observed] /\parent_guard_bad(decimal_number bytes)=false /\
    Int.eq observed(Int.repr(parent_value(decimal_number bytes)))=false))) \/
 (matching_history bytes history /\initialization_frontier middle configured after e le k argc export_bytes tree_bytes stdin_bytes x rest values s).
Theorem traced_initialization_certificate cell e le before k argc argv ofs p bytes output export tree stdin export_bytes tree_bytes stdin_bytes x rest values :
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
 exists parser_count middle flagged tree_set configured after,
 number_post before output Ptrofs.zero(decimal_number bytes)middle /\
 configuration_stores middle flagged tree_set configured(bytes_equal export_bytes files_bytes)tree stdin /\
 Mem.store Mptr configured main_policy_block 88(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 128)))=Some after /\
 trace_certificate main_ge cell
 (traced_initialization_memory before output(decimal_number bytes)middle flagged tree_set configured after)
 (traced_initialization_frontier middle configured after e le k argc bytes export_bytes tree_bytes stdin_bytes x rest values)
 ((9+parser_count+28)+(26*length(x::rest)+4540))[](State f_main(validation_suffix 15)k e le before).
Proof.
 intros NUMBER GETPPID LOCAL PL INPUT OUTPUT PARGV PEXPORT PTREE PSTDIN PGUEST PPOLICY PLITERALS
 COUNT SIZE SPAN OWN ARGVSEP STRINGSEP TREESEP STDINSEP IMAGE LITERALS STRCMP STRLEN POLICY DISCARD FILES SHELL PYTHON NONE TREE STDIN DIGEST ARGV ARGC EL TL SL EO TO SO FW TW SW AW.
 destruct(parent_source_trace_certificate cell e le before k argv ofs p bytes output NUMBER GETPPID LOCAL ARGV PL INPUT OUTPUT)
 as[parser_count[middle[POST PARENT]]].
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
 destruct(configuration_exists middle(bytes_equal export_bytes files_bytes)tree stdin FW' TW' SW')as[flagged[tree_set[configured CONFIG]]].
 pose proof(proj2(proj2(configuration_frames _ _ _ _ _ _ _ CONFIG)))as FRAME.
 assert(AW'':Mem.valid_access configured Mptr main_policy_block 88 Writable)by(eapply setup_access;eassumption).
 destruct(Mem.valid_access_store configured Mptr main_policy_block 88(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 128)))AW'')as[after STORE].
 exists parser_count,middle,flagged,tree_set,configured,after;split;[exact POST|];split;[exact CONFIG|];split;[exact STORE|].
 eapply trace_bind with(R:=traced_parent_frontier e le k middle(decimal_number bytes)).
 - eapply trace_convert;[exact PARENT|unfold traced_initialization_memory;intros;auto|intros h s RESULT;exact RESULT].
 - intros history endpoint END;pose proof END as HISTORY;destruct(traced_parent_split _ _ _ _ _ _ _ END)as[[REJECT OBS]|[ADMIT MATCH]].
   + apply trace_stop.
     * destruct REJECT as[OLD[final LAST]];rewrite LAST;left;exact MEM.
     * left;split;[exact HISTORY|];split;[exact REJECT|exact OBS].
   + destruct ADMIT as[ADMITTED[mid[REGS LAST]]];subst endpoint.
     destruct(initialization_certificate cell e mid middle k argc argv ofs export tree stdin export_bytes tree_bytes stdin_bytes x rest values
      COUNT SIZE SPAN OWN' ARGVSEP STRINGSEP TREESEP STDINSEP IMAGE' LITERALS' STRCMP STRLEN POLICY DISCARD FILES SHELL PYTHON NONE TREE STDIN DIGEST
      ltac:(rewrite(proj1 REGS);exact ARGV)ltac:(rewrite(proj2 REGS);exact ARGC)EL' TL' SL' EO' TO' SO' FW' TW' SW' AW')
      as[f2[t2[c2[a2[CONFIG2[STORE2 CERT]]]]]].
     assert(f2=flagged /\t2=tree_set /\c2=configured /\a2=after)as[E1[E2[E3 E4]]].
     { destruct CONFIG as[A[B C]];destruct CONFIG2 as[D[E F]].
       assert(f2=flagged)by congruence;subst f2;assert(t2=tree_set)by congruence;subst t2;
       assert(c2=configured)by congruence;subst c2;repeat split;congruence. }
     subst f2 t2 c2 a2;eapply trace_convert;[apply trace_from_string with(history:=history);exact CERT| |].
     * unfold traced_initialization_memory;intros;auto.
     * intros h last[HEQ RESULT];subst h;right;split;[exact MATCH|].
       eapply initialization_frame;[exact REGS|exact RESULT].
Qed.
Theorem traced_initialization_source cell e le before k argc argv ofs p bytes output export tree stdin export_bytes tree_bytes stdin_bytes x rest values :
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
 exists parser_count middle flagged tree_set configured after,
 number_post before output Ptrofs.zero(decimal_number bytes)middle /\
 configuration_stores middle flagged tree_set configured(bytes_equal export_bytes files_bytes)tree stdin /\
 Mem.store Mptr configured main_policy_block 88(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 128)))=Some after /\
 trace_guarantee main_ge cell
 (traced_initialization_memory before output(decimal_number bytes)middle flagged tree_set configured after)
 (traced_initialization_frontier middle configured after e le k argc bytes export_bytes tree_bytes stdin_bytes x rest values)
 ((9+parser_count+28)+(26*length(x::rest)+4540))(State f_main(validation_suffix 15)k e le before).
Proof.
 intros NUMBER GETPPID LOCAL PL INPUT OUTPUT PARGV PEXPORT PTREE PSTDIN PGUEST PPOLICY PLITERALS
 COUNT SIZE SPAN OWN ARGVSEP STRINGSEP TREESEP STDINSEP IMAGE LITERALS STRCMP STRLEN POLICY DISCARD FILES SHELL PYTHON NONE TREE STDIN DIGEST ARGV ARGC EL TL SL EO TO SO FW TW SW AW.
 destruct(traced_initialization_certificate cell e le before k argc argv ofs p bytes output export tree stdin export_bytes tree_bytes stdin_bytes x rest values
 NUMBER GETPPID LOCAL PL INPUT OUTPUT PARGV PEXPORT PTREE PSTDIN PGUEST PPOLICY PLITERALS
 COUNT SIZE SPAN OWN ARGVSEP STRINGSEP TREESEP STDINSEP IMAGE LITERALS STRCMP STRLEN POLICY DISCARD FILES SHELL PYTHON NONE TREE STDIN DIGEST ARGV ARGC EL TL SL EO TO SO FW TW SW AW)
 as[count[middle[flagged[tree_set[configured[after[POST[CONFIG[STORE CERT]]]]]]]]].
 exists count,middle,flagged,tree_set,configured,after;split;[exact POST|];split;[exact CONFIG|];split;[exact STORE|].
 apply trace_guaranteed;exact CERT.
Qed.
