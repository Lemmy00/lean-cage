(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-parent.cases: Every actual prefix can lose the process with its precise current memory. *)
From Stdlib Require Import List Lia.
From compcert Require Import Integers AST Values Memory Clight.
Require Import Machine.
From LeanCageParent Require Import ParentMachine TraceRegion.
Import ListNotations.

Lemma parent_steps_append_split ge cell start first rest target : parent_steps ge cell start(first++rest)target->
 exists middle,parent_steps ge cell start first middle /\parent_steps ge cell middle rest target.
Proof.
 revert start;induction first as[|ev first IH];intros start RUN.
 - exists start;split;[constructor|exact RUN].
 - inversion RUN as[|s ev' mid tail last STEP TAIL];subst;destruct(IH _ TAIL)as[middle[PRE POST]].
   exists middle;split;[econstructor;eassumption|exact POST].
Qed.
Theorem composed_prefix_loss ge cell start events endpoint : parent_steps ge cell(live start)events(live endpoint)->
 forall first rest,events=first++rest->exists middle,
 parent_steps ge cell(live start)first(live middle) /\
 parent_steps ge cell(live middle)rest(live endpoint) /\
 parent_steps ge cell(live start)(first++[parent_loss])(dead(memory_of middle)).
Proof.
 intros RUN first rest EQ;subst events.
 destruct(parent_steps_append_split _ _ _ _ _ _ RUN)as[mid[PRE POST]].
 destruct mid as[middle|m].
 - exists middle;split;[exact PRE|];split;[exact POST|].
   eapply parent_steps_trans;[exact PRE|];econstructor;[apply parent_loss_everywhere|constructor].
 - destruct(parent_dead_steps _ _ _ _ _ POST)as[ES BAD];discriminate BAD.
Qed.

Lemma singleton_observation_split events observed : observations events=[observed]->
 exists first rest,events=first++parent_observed observed::rest /\observations first=[] /\observations rest=[].
Proof.
 induction events as[|ev events IH];[discriminate|];destruct ev as[old|value|];cbn[observations flat_map observation].
 - intros OBS;destruct(IH OBS)as[first[rest[ES[PRE POST]]]].
   exists(previous old::first),rest;split;[cbn;rewrite ES;reflexivity|];split;[exact PRE|exact POST].
 - intros OBS;injection OBS as VALUE REST;subst value;exists [],events;auto.
 - intros OBS;destruct(IH OBS)as[first[rest[ES[PRE POST]]]].
   exists(parent_wait::first),rest;split;[cbn;rewrite ES;reflexivity|];split;[exact PRE|exact POST].
Qed.

Theorem actual_observation_loss_boundaries ge cell start first observed rest endpoint :
 parent_steps ge cell(live start)(first++parent_observed observed::rest)(live endpoint)->
 exists k m,
 parent_steps ge cell(live start)first(live(Callstate getppid_definition [] k m)) /\
 parent_steps ge cell(live start)(first++[parent_observed observed])(live(Returnstate(Vint observed)k m)) /\
 parent_steps ge cell(live start)(first++[parent_loss])(dead m) /\
 parent_steps ge cell(live start)(first++[parent_observed observed;parent_loss])(dead m).
Proof.
 intros RUN;destruct(composed_prefix_loss _ _ _ _ _ RUN first(parent_observed observed::rest)eq_refl)
 as[middle[PRE[POST LOSS]]].
 inversion POST;subst;match goal with STEP:parent_step _ _ _ (parent_observed _) _|-_=>inversion STEP;subst end.
 eexists;eexists;split;[exact PRE|];split.
 - eapply parent_steps_trans;[exact PRE|];econstructor;[constructor|constructor].
 - split;[exact LOSS|];eapply parent_steps_trans;[exact PRE|].
   econstructor;[constructor|];econstructor;[apply parent_loss_everywhere|constructor].
Qed.
