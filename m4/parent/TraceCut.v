(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-parent.history: Eliminate unfinished certificates at actual post-bounds acceptance. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine Library LibraryMachine ClightSteps StoreSteps.
From LeanCageMain Require Import Main MainStructure.
From LeanCageBounds Require Import BoundsStructure.
From LeanCageArguments Require Import StringMachine.
From LeanCageValidation Require Import ValidationStructure.
From LeanCageParent Require Import ParentMachine TraceRegion TraceExecution.
Import ListNotations.
Open Scope nat_scope.

Definition selected_stop_shape s :=
 exists f stmt k e le m,s=State f stmt k e le m /\
 (stmt=Sskip \/exists opt ty args,stmt=Scall opt(Evar _result_of ty)args).
Definition getenv_type := Tfunction[tptr tschar](tptr tschar)cc_default.
Definition getenv_call := first_statement(first_statement after_bounds).
Definition getenv_call_cont k := Kseq(second_statement(first_statement after_bounds))
 (Kseq(second_statement after_bounds)k).

Theorem getenv_source_shape :
 after_bounds=validation_suffix 26 /\
 after_bounds=Ssequence(Ssequence getenv_call(second_statement(first_statement after_bounds)))
 (second_statement after_bounds) /\
 getenv_call=Scall(Some _t'56)(Evar _getenv getenv_type)
 [Evar ___stringlit_136(tarray tschar 22)].
Proof. repeat split;reflexivity. Qed.

Theorem main_internal_returns :
 Forall(fun item=>match snd item with Gfun(Internal f)=>fn_return f<>tptr tschar|_=>True end)
 (prog_defs Main.prog).
Proof.
 change(Forall(fun item=>match snd item with Gfun(Internal f)=>fn_return f<>tptr tschar|_=>True end)
 global_definitions).
 unfold global_definitions;repeat(apply Forall_cons;[first[exact I|discriminate]|]);constructor.
Qed.

Definition accepted_prefix_contract cell P R n start :=
 forall events k e le m,
 parent_steps main_ge cell(live start)events(live(State f_main Sskip(Kseq after_bounds k)e le m))->
 exists prefix endpoint rest,events=prefix++rest /\parent_cost prefix<=S n /\
 parent_steps main_ge cell(live start)prefix(live endpoint) /\P(memory_of endpoint) /\
 R(observations prefix)endpoint /\
 parent_steps main_ge cell(live endpoint)rest(live(State f_main Sskip(Kseq after_bounds k)e le m)).

Lemma clight_funct_member p vf fd : Genv.find_funct(Clight.globalenv p)vf=Some fd->
 exists id,In(id,Gfun fd)(prog_defs p).
Proof.
 unfold Clight.globalenv;cbv beta iota zeta delta[genv_genv].
 apply Genv.find_funct_inversion.
Qed.

Lemma getenv_target_external vf fd : Genv.find_funct main_ge vf=Some fd->
 type_of_fundef fd=getenv_type->
 exists ef,fd=External ef[tptr tschar](tptr tschar)cc_default.
Proof.
 intros FIND TYPE;destruct fd as[f|ef args ret cc].
 - destruct(clight_funct_member Main.prog vf(Internal f)FIND)as[id IN].
   pose proof(proj1(Forall_forall _ _)main_internal_returns _ IN)as RETURN.
   unfold type_of_fundef,type_of_function,getenv_type in TYPE;inversion TYPE;subst;contradiction.
 - unfold type_of_fundef,getenv_type in TYPE;inversion TYPE;subst;exists ef;reflexivity.
Qed.

Theorem getenv_local_no_progress ge cell ef args k m ev next :
 ~parent_step ge cell(live(Callstate(External ef[tptr tschar](tptr tschar)cc_default)args k m))ev(live next).
Proof.
 intros STEP;inversion STEP;subst;try discriminate.
 inversion H;subst;try discriminate.
 match goal with STEP:library_step _ _ _ _ _|-_=>inversion STEP;subst;try discriminate end.
 - match goal with STEP:Machine.step _ _ _ _ _|-_=>inversion STEP;subst;cbn in *;try contradiction;try discriminate end.
   match goal with B:boundary _ _ _|-_=>inversion B;subst;discriminate end.
 - match goal with B:library_ready _ _|-_=>inversion B;subst;discriminate end.
Qed.

Lemma trace_internal_follow ge cell P R n history s next :
 trace_certificate ge cell P R n history s->store_edge ge s next->
 R history s \/exists remaining,trace_certificate ge cell P R remaining history next.
Proof.
 intros CERT[IN[REAL UNIQUE]];inversion CERT as[count h ss GOOD RESULT|count h ss GOOD PROGRESS CASES];subst;auto.
 assert(STEP:parent_step ge cell(live s)(previous string_source)(live next)).
 { constructor;constructor;constructor;apply internal;assumption. }
 destruct(CASES _ _ STEP)as[[WAIT SAME]|[[after[SAME REST]]|[last[SAME[ADV TAIL]]]]];try discriminate.
 inversion SAME;subst last;right;exists count;cbn[observation]in TAIL;rewrite app_nil_r in TAIL;exact TAIL.
Qed.

Lemma no_selected_callstate fd args k m : ~selected_stop_shape(Callstate fd args k m).
Proof. intros[f[s[c[e[le[after[EQ SHAPE]]]]]]];discriminate. Qed.

Lemma no_selected_getenv_call k e le m : ~selected_stop_shape(State f_main getenv_call k e le m).
Proof.
 intros[f[s[c[ee[ll[after[EQ SHAPE]]]]]]];inversion EQ;subst.
 destruct SHAPE as[SKIP|[opt[ty[args CALL]]]];change getenv_call with
 (Scall(Some _t'56)(Evar _getenv getenv_type)[Evar ___stringlit_136(tarray tschar 22)])in *;discriminate.
Qed.

Lemma trace_getenv_call_impossible cell P R n history k e le m :
 (forall h s,R h s->selected_stop_shape s)->
 ~trace_certificate main_ge cell P R n history(State f_main getenv_call k e le m).
Proof.
 intros SHAPE CERT;inversion CERT as[count h ss GOOD RESULT|count h ss GOOD PROGRESS CASES];subst.
 - exact(no_selected_getenv_call _ _ _ _(SHAPE _ _ RESULT)).
 - destruct PROGRESS as[ev[next[WAIT[LOSS STEP]]]].
   assert(REAL:exists fd args, next=Callstate fd args(Kcall(Some _t'56)f_main e le k)m /\
     type_of_fundef fd=getenv_type /\exists vf,Genv.find_funct main_ge vf=Some fd).
   { inversion STEP;subst;try discriminate.
     match goal with S:string_step _ _ _ _ _|-_=>inversion S;subst;try discriminate end.
     match goal with S:library_step _ _ _ _ _|-_=>inversion S;subst;try discriminate end.
     match goal with S:Machine.step _ _ _ _ _|-_=>inversion S;subst;try discriminate end.
     match goal with S:step2 _ _ _ _|-_=>
       change getenv_call with(Scall(Some _t'56)(Evar _getenv getenv_type)
        [Evar ___stringlit_136(tarray tschar 22)])in S;inversion S;subst end;
      try match goal with B:_=_\/_=_|-_=>destruct B;discriminate end.
     match goal with TYPE:Cop.classify_fun _=_|-_=>
      cbn[typeof getenv_type Cop.classify_fun]in TYPE;inversion TYPE;subst end.
     repeat eexists;eassumption. }
   destruct REAL as[fd[args[EQ[TYPE[vf FIND]]]]];subst next.
   destruct(CASES _ _ STEP)as[[STILL SAME]|[[after[SAME REST]]|[next[SAME[ADV TAIL]]]]];try congruence.
   inversion SAME;subst next.
   inversion TAIL as[c hh ss GOOD' RESULT|c hh ss GOOD' PROGRESS' CASES'];subst.
   + exact(no_selected_callstate _ _ _ _(SHAPE _ _ RESULT)).
   + destruct(getenv_target_external _ _ FIND TYPE)as[ef DEF];subst fd.
     destruct PROGRESS' as[ev'[next'[W[L REAL']]]];eapply getenv_local_no_progress;exact REAL'.
Qed.

Theorem trace_post_bounds_cut cell P R n history k e le m :
 (forall h s,R h s->selected_stop_shape s)->
 trace_certificate main_ge cell P R n history(State f_main Sskip(Kseq after_bounds k)e le m)->
 R history(State f_main Sskip(Kseq after_bounds k)e le m).
Proof.
 intros SHAPE CERT;destruct(trace_internal_follow _ _ _ _ _ _ _ _ CERT
  (unchanged_store_edge _ _ _(edge_skip_seq _ _ _ _ _ _ _)))as[END|[n1 C1]];[exact END|].
 destruct(trace_internal_follow _ _ _ _ _ _ _ _ C1
  (unchanged_store_edge _ _ _(edge_seq _ _ _ _ _ _ _ _)))as[END|[n2 C2]].
 { exfalso;destruct(SHAPE _ _ END)as(f & s & c & ee & ll & after & EQ & STOP).
   inversion EQ;subst;destruct STOP as[SKIP|[opt[ty[args CALL]]]];discriminate. }
 destruct(trace_internal_follow _ _ _ _ _ _ _ _ C2
  (unchanged_store_edge _ _ _(edge_seq _ _ _ _ _ _ _ _)))as[END|[n3 C3]].
 { exfalso;destruct(SHAPE _ _ END)as(f & s & c & ee & ll & after & EQ & STOP).
   inversion EQ;subst;destruct STOP as[SKIP|[opt[ty[args CALL]]]];discriminate. }
 exfalso;eapply trace_getenv_call_impossible;[exact SHAPE|exact C3].
Qed.

Theorem trace_acceptance_prefix cell P R n start :
 (forall h s,R h s->selected_stop_shape s)->
 trace_certificate main_ge cell P R n [] start->accepted_prefix_contract cell P R n start.
Proof.
 intros SHAPE CERT events k e le m RUN.
 destruct(trace_execution_split _ _ _ _ _ _ _ CERT _ _ RUN)
 as[[MEM[BOUND LIVE]]|[prefix[endpoint[rest[EQ[COST[PRE[GOOD[END POST]]]]]]]]].
 - pose proof(LIVE _ eq_refl)as[remaining TAIL].
   pose proof(trace_post_bounds_cut _ _ _ _ _ _ _ _ _ SHAPE TAIL)as END.
   exists events,(State f_main Sskip(Kseq after_bounds k)e le m),[].
   split;[rewrite app_nil_r;reflexivity|];split;[exact BOUND|];
   split;[exact RUN|];split;[exact MEM|];split;[exact END|constructor].
 - exists prefix,endpoint,rest;split;[exact EQ|];split;[lia|auto].
Qed.

Definition frontier_guarantee cell P R n start :=
 trace_guarantee main_ge cell P R n start /\accepted_prefix_contract cell P R n start.
Theorem frontier_guaranteed cell P R n start :
 (forall h s,R h s->selected_stop_shape s)->trace_certificate main_ge cell P R n [] start->
 frontier_guarantee cell P R n start.
Proof. intros SHAPE CERT;split;[apply trace_guaranteed|apply trace_acceptance_prefix];assumption. Qed.
