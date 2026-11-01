(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.strings: Actual caller checks, owned bytes and explicit execution boundaries. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Library Machine ClightSteps Deterministic.
From LeanCageMain Require Import Main MainStructure.
From LeanCageBounds Require Import BoundsMemory.
From LeanCageArguments Require Import StringMachine StringPath ArgumentStructure ArgumentMemory ArgumentBounds.
From LeanCageValidation Require Import StringRegion ValidationStructure ValidationValues ValidationFinish
 DigestCaller ExportCaller ExecutableCaller ModeCaller ValidationComposition.
Import ListNotations.
Open Scope nat_scope.
Definition region_guarantee ge cell (P:mem->Prop)(R:Clight.state->Prop) n start :=
 (exists events endpoint,string_steps ge cell(live start)events(live endpoint) /\
  string_cost events<=n /\ P(memory_of endpoint) /\ R endpoint) /\
 (forall events target,string_steps ge cell(live start)events target->
  (P(routine_memory target) /\ string_cost events<=S n /\
   (forall s,target=live s->R s \/ exists ev next,string_waiting ev=false /\
    ev<>string_loss /\ string_step ge cell(live s)ev(live next))) \/
  (exists prefix endpoint rest,events=prefix++rest /\ string_cost prefix<=n /\
   string_steps ge cell(live start)prefix(live endpoint) /\ P(memory_of endpoint) /\ R endpoint /\
   string_steps ge cell(live endpoint)rest target)).
Theorem region_guaranteed ge cell P R n start : region_certificate ge cell P R n start->
 region_guarantee ge cell P R n start.
Proof.
 intros CERT;split;[apply region_actual;exact CERT|].
 intros events target RUN;destruct(region_execution_split _ _ _ _ _ _ CERT _ _ RUN)
 as[[MEM[BOUND LIVE]]|CROSSED];[left|right;exact CROSSED].
 split;[exact MEM|];split;[exact BOUND|].
 intros s EQ;destruct(LIVE s EQ)as[remaining TAIL];eapply region_live_progress;exact TAIL.
Qed.
Theorem mode_source cell e le m k argc argv ofs p bytes :
 (Int.min_signed<=argc<=Int.max_signed)%Z->le!_argc=Some(Vint(Int.repr argc))->
 e!_strcmp=None->e!___stringlit_131=None->e!___stringlit_130=None->le!_argv=Some(Vptr argv ofs)->
 Mem.loadv Mptr m(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 8)))=Some(address_value p)->
 c_string m p bytes->c_string m(literal_address ___stringlit_131)plan_bytes->
 c_string m(literal_address ___stringlit_130)check_bytes->
 region_guarantee main_ge cell(fun after=>after=m)(selection_frontier 2 e le k m(mode_bad argc bytes))31
 (State f_main(validation_suffix 2)k e le m).
Proof. intros;apply region_guaranteed;eapply mode_check_certificate;eassumption. Qed.
Theorem mode_short_source cell e le m k argc :
 (Int.min_signed<=argc<17)%Z->le!_argc=Some(Vint(Int.repr argc))->
 region_guarantee main_ge cell(fun after=>after=m)(selection_frontier 2 e le k m true)8
 (State f_main(validation_suffix 2)k e le m).
Proof. intros;apply region_guaranteed;eapply mode_short_arguments;eassumption. Qed.
Theorem export_source cell e le m k argv ofs p bytes :
 e!_strcmp=None->e!___stringlit_133=None->e!___stringlit_132=None->le!_argv=Some(Vptr argv ofs)->
 Mem.loadv Mptr m(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 104)))=Some(address_value p)->
 c_string m p bytes->c_string m(literal_address ___stringlit_133)discard_bytes->
 c_string m(literal_address ___stringlit_132)files_bytes->
 region_guarantee main_ge cell(fun after=>after=m)(selection_frontier 16 e le k m(export_bad bytes))26
 (State f_main(validation_suffix 16)k e le m).
Proof. intros;apply region_guaranteed;eapply export_check_certificate;eassumption. Qed.
Theorem digest_pair_source cell e le m k tree stdin tree_bytes stdin_bytes :
 e!_strcmp=None->e!___stringlit_56=None->e!_tree_digest=None->e!_stdin_digest=None->e!_digest_text=None->
 Mem.loadv Mptr m(Vptr(symbol_block _tree_digest)Ptrofs.zero)=Some(address_value tree)->
 Mem.loadv Mptr m(Vptr(symbol_block _stdin_digest)Ptrofs.zero)=Some(address_value stdin)->
 c_string m tree tree_bytes->c_string m stdin stdin_bytes->c_string m(literal_address ___stringlit_56)none_bytes->
 region_guarantee main_ge cell(fun after=>after=m)(digest_frontier e le k m tree_bytes stdin_bytes)4300
 (State f_main(validation_suffix 20)k e le m).
Proof. intros;apply region_guaranteed;eapply digest_pair_certificate;eassumption. Qed.
Theorem digest_short_source cell e le m k p bytes :
 e!_strcmp=None->e!___stringlit_56=None->e!_tree_digest=None->e!_digest_text=None->
 Mem.loadv Mptr m(Vptr(symbol_block _tree_digest)Ptrofs.zero)=Some(address_value p)->
 c_string m p bytes->c_string m(literal_address ___stringlit_56)none_bytes->option_bad bytes=true->
 region_guarantee main_ge cell(fun after=>after=m)(selection_frontier 20 e le k m true)2120
 (State f_main(validation_suffix 20)k e le m).
Proof. intros;apply region_guaranteed;eapply digest_tree_rejection_without_stdin;eassumption. Qed.
Theorem executable_source cell e le m k argv ofs p bytes :
 e!_strcmp=None->e!___stringlit_135=None->e!___stringlit_134=None->e!_policy__1=None->
 Mem.loadv Mptr m(Vptr main_policy_block(Ptrofs.repr 88))=Some(Vptr argv ofs)->
 Mem.loadv Mptr m(Vptr argv ofs)=Some(address_value p)->
 c_string m p bytes->c_string m(literal_address ___stringlit_135)shell_bytes->
 c_string m(literal_address ___stringlit_134)python_bytes->
 region_guarantee main_ge cell(fun after=>after=m)(selection_frontier 22 e le k m(executable_bad bytes))34
 (State f_main(validation_suffix 22)k e le m).
Proof. intros;apply region_guaranteed;eapply executable_check_certificate;eassumption. Qed.
Theorem executable_bounds_source cell e le m k argc argv ofs x rest values :
 (17<=argc<=2147483647)%Z->(16+Z.of_nat(length(x::rest))=argc)%Z->guest_table_span ofs argc->
 guest_arguments_owned m argv ofs 16(x::rest)->policy_image m values->
 e!_strcmp=None->e!_strlen=None->e!_policy__1=None->e!___stringlit_135=None->e!___stringlit_134=None->
 le!_argv=Some(Vptr argv ofs)->le!_argc=Some(Vint(Int.repr argc))->
 Mem.loadv Mptr m(Vptr main_policy_block(Ptrofs.repr 88))=Some(Vptr argv(Ptrofs.add ofs(Ptrofs.repr 128)))->
 c_string m(literal_address ___stringlit_135)shell_bytes->c_string m(literal_address ___stringlit_134)python_bytes->
 region_guarantee main_ge cell(fun after=>after=m)(executable_bounds_frontier e le k m argc x rest values)
 (34+(26*length(x::rest)+154))(State f_main(validation_suffix 22)k e le m).
Proof. intros;apply region_guaranteed;eapply executable_bounds_certificate;eassumption. Qed.
