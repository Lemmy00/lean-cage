(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.arguments: Actual source, owned argument strings and explicit loss. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import AST Values Memory Events Clight.
Require Import Machine ClightSteps Deterministic StoreSteps Library LibraryMachine.
From LeanCageArguments Require Import StringMachine.
Import ListNotations.
Open Scope nat_scope.
Definition string_cost events := length(filter(fun ev=>negb(string_waiting ev))events).
Definition string_edge ge cell s ev next :=
 string_waiting ev=false /\ ev<>string_loss /\
 string_step ge cell(live s)ev(live next) /\ memory_of next=memory_of s /\
 (forall event target,string_step ge cell(live s)event target ->
 (event=ev /\ target=live next) \/
 (string_waiting event=true /\ target=live s) \/
 (event=string_loss /\ target=dead(memory_of s))).
Inductive string_path ge cell : Clight.state -> nat -> Clight.state -> Prop :=
| string_done : forall s,string_path ge cell s 0 s
| string_next : forall s ev next count last,string_edge ge cell s ev next ->
 string_path ge cell next count last -> string_path ge cell s(S count)last.
Lemma string_path_memory ge cell start count last : string_path ge cell start count last ->
 memory_of last=memory_of start.
Proof. intros PATH;induction PATH;auto;destruct H as[_[_[_[MEM _]]]];congruence. Qed.
Lemma string_path_trans ge cell a n b k c : string_path ge cell a n b ->
 string_path ge cell b k c -> string_path ge cell a(n+k)c.
Proof. intros AB BC;induction AB;cbn;auto;eapply string_next;eauto. Qed.
Lemma string_source_edge ge cell s next : edge ge s next ->
 string_edge ge cell s string_source next.
Proof.
 intros EDGE;pose proof EDGE as[IN[REAL[MEM UNIQUE]]].
 repeat split;try discriminate;auto.
 - constructor;constructor;apply internal;assumption.
 - intros ev target STEP;destruct(string_internal_exact _ _ _ _ _ IN STEP)as[old[EV OLD]];subst.
   destruct(machine_edge_cases _ _ _ _ _ _ EDGE OLD)as[[EV TARGET]|[EV TARGET]];subst;auto.
Qed.
Lemma string_store_path ge cell start count last m :
 store_path ge(fun after=>after=m)start count last ->
 string_path ge cell start count last.
Proof.
 intros PATH;induction PATH;[constructor|].
 eapply string_next;[apply string_source_edge|exact IHPATH].
 destruct H0 as[IN[REAL UNIQUE]];split;[exact IN|];split;[exact REAL|];split.
 - pose proof(store_path_initial _ _ _ _ _ PATH)as MEM;congruence.
 - exact UNIQUE.
Qed.
Lemma string_strlen_edge ge cell m p bytes k : c_string m p bytes ->
 string_edge ge cell(Callstate strlen_definition[address_value p]k m)
 (strlen_returned p(Z.of_nat(length bytes)))(Returnstate(strlen_value bytes)k m).
Proof.
 intros OWN;repeat split;try discriminate;try reflexivity.
 - constructor;exact OWN.
 - intros ev target STEP;destruct(strlen_boundary_cases _ _ _ _ _ _ _ _ OWN STEP)
   as[[EV TARGET]|[[EV TARGET]|[EV TARGET]]];subst;auto.
Qed.
Lemma string_path_actual ge cell start count last : string_path ge cell start count last ->
 exists events,string_cost events=count /\ string_steps ge cell(live start)events(live last).
Proof.
 intros PATH;induction PATH.
 - exists [];split;[reflexivity|constructor].
 - destruct IHPATH as[events[COST RUN]];destruct H as[WAIT[_[STEP _]]].
   exists(ev::events);split.
   + unfold string_cost in *;cbn;rewrite WAIT;cbn;congruence.
   + econstructor;eassumption.
Qed.
Lemma string_path_prefix ge cell start count last events target :
 string_path ge cell start count last -> string_steps ge cell(live start)events target ->
 string_cost events<=count ->
 (exists s rest,target=live s /\ string_path ge cell s rest last /\ string_cost events+rest=count) \/
 (exists m,target=dead m /\ m=memory_of start).
Proof.
 intros SCRIPT RUN;remember(live start)as initial eqn:INIT.
 revert start count INIT SCRIPT;induction RUN as[initial|initial ev mid events target STEP RUN IH];
 intros start count INIT SCRIPT BOUND;subst initial.
 - left;exists start,count;cbn;auto.
 - destruct(string_waiting ev)eqn:WAIT.
   + pose proof(string_wait_identity _ _ _ _ _ STEP WAIT)as SAME;subst mid.
     assert(COST:string_cost(ev::events)=string_cost events)by(unfold string_cost;cbn;rewrite WAIT;reflexivity).
     rewrite COST in *;apply IH with(start:=start)(count:=count);auto.
   + assert(COST:string_cost(ev::events)=S(string_cost events))by(unfold string_cost;cbn;rewrite WAIT;reflexivity).
     inversion SCRIPT as[|s expected next n final EDGE TAIL];subst;[rewrite COST in BOUND;lia|].
     destruct EDGE as[ORD[NOTLOSS[REAL[MEM CASES]]]].
     destruct(CASES _ _ STEP)as[[EV TARGET]|[[W TARGET]|[EV TARGET]]];subst.
     * destruct(IH _ _ eq_refl TAIL ltac:(rewrite COST in BOUND;lia))as
       [[s[rest[TARGET[PATH LEN]]]]|[m[TARGET GOOD]]].
       -- left;exists s,rest;rewrite COST;split;[exact TARGET|];split;[exact PATH|lia].
       -- right;exists m;split;[exact TARGET|congruence].
     * congruence.
     * destruct(string_dead_steps _ _ _ _ _ RUN)as[ES TARGET];subst;right;eexists;auto.
Qed.
Theorem string_path_prefix_memory ge cell start count last events target :
 string_path ge cell start count last -> string_steps ge cell(live start)events target ->
 string_cost events<=count -> routine_memory target=memory_of start.
Proof.
 intros PATH RUN BOUND;destruct(string_path_prefix _ _ _ _ _ _ _ PATH RUN BOUND)
 as[[s[rest[TARGET[TAIL LEN]]]]|[m[TARGET MEM]]];subst;cbn;auto.
 pose proof(string_path_memory _ _ _ _ _ PATH);pose proof(string_path_memory _ _ _ _ _ TAIL);congruence.
Qed.
Theorem string_path_prefix_progress ge cell start count last events s :
 string_path ge cell start count last -> string_steps ge cell(live start)events(live s) ->
 string_cost events<count -> exists ev next,string_waiting ev=false /\ ev<>string_loss /\
 string_step ge cell(live s)ev(live next).
Proof.
 intros PATH RUN BOUND;destruct(string_path_prefix _ _ _ _ _ _ _ PATH RUN ltac:(lia))
 as[[ss[rest[TARGET[TAIL LEN]]]]|[m[TARGET MEM]]];[|discriminate].
 inversion TARGET;subst ss;inversion TAIL;subst;[lia|].
 destruct H as[ORD[NOTLOSS[REAL _]]];eauto.
Qed.
Theorem string_path_prefix_endpoint ge cell start count last events s :
 string_path ge cell start count last -> string_steps ge cell(live start)events(live s) ->
 string_cost events=count -> s=last.
Proof.
 intros PATH RUN COUNT;destruct(string_path_prefix _ _ _ _ _ _ _ PATH RUN ltac:(lia))
 as[[ss[rest[TARGET[TAIL LEN]]]]|[m[TARGET MEM]]];[|discriminate].
 inversion TARGET;subst ss;assert(rest=0)by lia;subst;inversion TAIL;reflexivity.
Qed.
Theorem string_path_loss_every_prefix ge cell start count last :
 string_path ge cell start count last -> forall n,n<=count -> exists events,
 string_cost events=n /\ string_steps ge cell(live start)(events++[string_loss])(dead(memory_of start)).
Proof.
 intros PATH;induction PATH;intros prefix BOUND.
 - assert(prefix=0)by lia;subst;exists [];split;[reflexivity|].
   econstructor;[apply string_loss_everywhere|constructor].
 - destruct prefix.
   + exists [];split;[reflexivity|];econstructor;[apply string_loss_everywhere|constructor].
   + destruct(IHPATH prefix ltac:(lia))as[events[COST RUN]].
     destruct H as[WAIT[_[STEP[MEM _]]]];exists(ev::events);split.
     * unfold string_cost in *;cbn;rewrite WAIT;cbn;congruence.
     * cbn;econstructor;[exact STEP|];rewrite<-MEM;exact RUN.
Qed.
