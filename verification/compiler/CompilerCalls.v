(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-compiled-reporting.connection: Restart the compiler simulation at a matched reporting call. *)
From Stdlib Require Import List Lia.
From compcert Require Import Coqlib Integers Events Smallstep Behaviors Clight Asm.

Definition at_state (L : Smallstep.semantics) (initial : Smallstep.state L) : Smallstep.semantics :=
 Semantics_gen (Smallstep.step L) (fun s=>s=initial) (Smallstep.final_state L) (Smallstep.globalenv L) (Smallstep.symbolenv L).

Lemma at_state_receptive L initial : receptive L -> receptive(at_state L initial).
Proof. intro REC;constructor;[exact(@sr_receptive L REC)|exact(@sr_traces L REC)]. Qed.

Lemma at_state_determinate L initial : determinate L -> determinate(at_state L initial).
Proof.
 intro DET;constructor.
 - exact(@sd_determ L DET).
 - exact(@sd_traces L DET).
 - intros x y X Y;congruence.
 - exact(@sd_final_nostep L DET).
 - exact(@sd_final_determ L DET).
Qed.

Theorem at_state_forward L1 L2 index order matches
 (PROPS : fsim_properties L1 L2 index order matches) i s1 s2 :
 matches i s1 s2 -> forward_simulation(at_state L1 s1)(at_state L2 s2).
Proof.
 intro MATCH;refine(@Forward_simulation (at_state L1 s1)(at_state L2 s2) index order matches _);constructor.
 - exact(@fsim_order_wf _ _ _ _ _ PROPS).
 - intros source EQ;change(source=s1)in EQ;subst source;exists i,s2;split;[reflexivity|exact MATCH].
 - exact(@fsim_match_final_states _ _ _ _ _ PROPS).
 - exact(@fsim_simulation _ _ _ _ _ PROPS).
 - exact(@fsim_public_preserved _ _ _ _ _ PROPS).
Qed.

(* Clight's published lemma is stated for step1. Function-entry choice does
   not affect external-call receptiveness. This proof checks step2 directly. *)
Lemma clight2_receptive program : receptive(Clight.semantics2 program).
Proof.
 unfold Clight.semantics2;constructor;cbn;intros.
 - assert(SILENT:t1=E0 -> exists s2,Clight.step2 (Clight.globalenv program) s t2 s2).
   { intro EQ;subst t1;inversion H0;subst;exists s1;exact H. }
   inversion H;subst;try(apply SILENT;reflexivity).
   all:match goal with EC:external_call _ _ _ _ _ _ _|-_=>
     destruct(@external_call_receptive _ _ _ _ _ _ _ _ EC H0)as[value[after EXTERNAL]] end.
   + eexists;econstructor;eauto.
   + exists(Returnstate value k after);econstructor;eauto.
 - red;cbn;intros;inversion H;subst;cbn;try lia;
     eapply external_call_trace_length;eassumption.
Qed.

(* Unlike a theorem that assumes source safety as its final premise, this
   lemma accepts local progress for every reachable source prefix. The caller
   below supplies that fact from the established reporting source proof. *)
Theorem matched_compiler_prefix L1 L2 index order matches
 (PROPS : fsim_properties L1 L2 index order matches) i initial compiled trace final :
 receptive L1 -> determinate L2 -> matches i initial compiled ->
 (forall t s,Star L1 initial t s ->
   (exists r,Smallstep.final_state L1 s r) \/ (exists t next,Step L1 s t next)) ->
 Star L2 compiled trace final ->
 exists source,Star L1 initial trace source.
Proof.
 intros REC DET MATCH PROGRESS RUN.
 pose proof(at_state_forward _ _ _ _ _ PROPS _ _ _ MATCH)as FORWARD.
 pose proof(@forward_to_backward_simulation _ _ FORWARD
   (at_state_receptive _ _ REC)(at_state_determinate _ _ DET))as BACKWARD.
 destruct BACKWARD as[back_index back_order back_matches BACK_PROPS].
 destruct(@bsim_match_initial_states _ _ _ _ _ BACK_PROPS initial compiled eq_refl eq_refl)
   as[j[source[INIT RELATED]]];cbn in INIT;subst source.
 assert(ALONG:safe_along_behavior (at_state L1 initial) initial (behavior_app trace (Diverges E0))).
 { intros prefix source remaining SOURCE REST;apply(PROGRESS _ _ SOURCE). }
 destruct(@backward_simulation_star _ _ _ _ _ BACK_PROPS _ _ _ RUN _ _ _ RELATED ALONG)
   as[k[source[SOURCE RELATED']]].
 exists source;exact SOURCE.
Qed.

Theorem matched_compiler_return L1 L2 index order matches
 (PROPS : fsim_properties L1 L2 index order matches) i initial compiled trace final result :
 receptive L1 -> determinate L2 -> matches i initial compiled ->
 (forall t s,Star L1 initial t s ->
   (exists r,Smallstep.final_state L1 s r) \/ (exists t next,Step L1 s t next)) ->
 Star L2 compiled trace final -> Smallstep.final_state L2 final result ->
 exists source,Star L1 initial trace source /\ Smallstep.final_state L1 source result.
Proof.
 intros REC DET MATCH PROGRESS RUN FINAL.
 pose proof(at_state_forward _ _ _ _ _ PROPS _ _ _ MATCH)as FORWARD.
 pose proof(@forward_to_backward_simulation _ _ FORWARD
   (at_state_receptive _ _ REC)(at_state_determinate _ _ DET))as BACKWARD.
 assert(SAFE:forall behavior,program_behaves(at_state L1 initial)behavior->not_wrong behavior).
 { intros behavior BEHAVIOR;inversion BEHAVIOR;subst.
   - cbn in H;subst s;inversion H0;subst;cbn;auto.
     destruct(PROGRESS _ _ H)as[[r FIN]|[progress_trace[next STEP]]];[exfalso;eapply H2;eassumption|].
     exfalso;eapply H1;eassumption.
   - exfalso;eapply H;reflexivity. }
 assert(BEHAVIOR:program_behaves(at_state L2 compiled)(Terminates trace result)).
 { econstructor;[reflexivity|]. econstructor;[exact RUN|exact FINAL]. }
 pose proof(@backward_simulation_same_safe_behavior _ _ BACKWARD SAFE _ BEHAVIOR)as SOURCE.
 inversion SOURCE as[source behavior INIT STATE|NOINIT];subst.
 change(source=initial)in INIT;subst source;inversion STATE;subst.
 eexists;split;eassumption.
Qed.
