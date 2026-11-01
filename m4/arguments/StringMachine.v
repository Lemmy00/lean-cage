(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.arguments: Actual source, owned argument strings and explicit loss. *)
From Stdlib Require Import ZArith List String Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import IO Machine Library LibraryMachine.
From LeanCageMain Require Import Main MainStructure.
Import ListNotations.
Open Scope Z_scope.
Definition strlen_definition : Clight.fundef := External
 (EF_external "strlen" (mksignature [Xptr] Xlong cc_default)) [tptr tschar] tulong cc_default.
Definition strlen_value (bytes:list Byte.int) := Vlong(Int64.repr(Z.of_nat(length bytes))).
Inductive string_event :=
| previous_event (event:library_event)
| strlen_returned (pointer:address)(size:Z)
| string_wait.
Inductive string_step ge cell : machine -> string_event -> machine -> Prop :=
| previous_step : forall s ev target, library_step ge cell s ev target ->
 string_step ge cell s(previous_event ev)target
| strlen_step : forall m p bytes k, c_string m p bytes ->
 string_step ge cell(live(Callstate strlen_definition [address_value p]k m))
 (strlen_returned p(Z.of_nat(length bytes)))(live(Returnstate(strlen_value bytes)k m))
| strlen_wait : forall m p bytes k,c_string m p bytes ->
 string_step ge cell(live(Callstate strlen_definition [address_value p]k m))
 string_wait(live(Callstate strlen_definition [address_value p]k m)).
Inductive string_steps ge cell : machine -> list string_event -> machine -> Prop :=
| string_steps_nil : forall s,string_steps ge cell s [] s
| string_steps_cons : forall s ev mid rest last,string_step ge cell s ev mid ->
 string_steps ge cell mid rest last -> string_steps ge cell s(ev::rest)last.
Definition string_loss := previous_event(original_event loss_step).
Definition string_source := previous_event(original_event(source_step E0)).
Theorem strlen_signature :
 Genv.find_funct main_ge(Vptr(match Genv.find_symbol main_ge _strlen with Some b=>b|None=>1%positive end)Ptrofs.zero)=Some strlen_definition.
Proof. reflexivity. Qed.
Theorem string_internal_exact ge cell s ev target : internal_state s ->
 string_step ge cell(live s)ev target ->
 exists original,ev=previous_event(original_event original) /\ Machine.step ge cell(live s)original target.
Proof.
 intros IN STEP;inversion STEP;subst;cbn in IN;try contradiction.
 destruct(internal_boundary_unchanged _ _ _ _ _ IN H)as[old[EV OLD]];subst;eauto.
Qed.
Theorem string_loss_everywhere ge cell s :
 string_step ge cell(live s)string_loss(dead(memory_of s)).
Proof. constructor;constructor;constructor. Qed.
Theorem string_dead_terminal ge cell m ev target : ~string_step ge cell(dead m)ev target.
Proof. intros STEP;inversion STEP;subst;eapply library_dead_cannot_resume;eassumption. Qed.
Theorem string_previous_preserved ge cell s events target :
 library_steps ge cell s events target -> string_steps ge cell s(map previous_event events)target.
Proof. intros RUN;induction RUN;cbn;[constructor|].
 econstructor;[constructor;exact H|exact IHRUN]. Qed.
Lemma strlen_original_only_loss ge cell p k m ev target :
 Machine.step ge cell(live(Callstate strlen_definition [address_value p]k m))ev target ->
 ev=loss_step /\ target=dead m.
Proof.
 intros STEP;inversion STEP;subst;cbn in *;try contradiction;auto;
 match goal with H:boundary _ _ _|-_=>inversion H;subst;destruct(operation q);discriminate end.
Qed.
Lemma strlen_library_only_loss ge cell p k m ev target :
 library_step ge cell(live(Callstate strlen_definition [address_value p]k m))ev target ->
 ev=original_event loss_step /\ target=dead m.
Proof.
 intros STEP;inversion STEP;subst;try discriminate.
 - destruct(strlen_original_only_loss _ _ _ _ _ _ _ H);subst;auto.
 - match goal with H:library_ready _ _|-_=>inversion H end.
Qed.
Lemma c_string_pointer_unique m p q xs ys : c_string m p xs -> c_string m q ys ->
 address_value p=address_value q -> p=q.
Proof.
 intros LEFT RIGHT SAME;unfold address_value in SAME;injection SAME as BLOCK OFFSET.
 eapply readable_address_components;[exact(proj2 LEFT)|exact(proj2 RIGHT)|exact BLOCK|].
 exact OFFSET.
Qed.
Theorem strlen_boundary_cases ge cell p bytes k m ev target : c_string m p bytes ->
 string_step ge cell(live(Callstate strlen_definition [address_value p]k m))ev target ->
 (ev=strlen_returned p(Z.of_nat(length bytes)) /\ target=live(Returnstate(strlen_value bytes)k m)) \/
 (ev=string_wait /\ target=live(Callstate strlen_definition [address_value p]k m)) \/
 (ev=string_loss /\ target=dead m).
Proof.
 intros OWNED STEP;inversion STEP;subst.
 - destruct(strlen_library_only_loss _ _ _ _ _ _ _ H);subst;auto.
 - assert(p0=p) as PTR.
   { eapply readable_address_components;[exact(proj2 H5)|exact(proj2 OWNED)|exact H|exact H1]. }
   subst p0;assert(bytes0=bytes)as BYTES by(eapply c_string_unique;eassumption).
   subst bytes0;auto.
 - assert(p0=p)as PTR.
   { eapply readable_address_components;[exact(proj2 H5)|exact(proj2 OWNED)|exact H|exact H1]. }
   subst p0;auto.
Qed.
Definition string_waiting ev := match ev with
 |string_wait|previous_event library_wait|previous_event(original_event wait_step)=>true|_=>false end.
Lemma string_wait_identity ge cell s ev target : string_step ge cell(live s)ev target ->
 string_waiting ev=true -> target=live s.
Proof.
 intros STEP WAIT;inversion STEP;subst;cbn in WAIT;try discriminate;auto.
 inversion H;subst;cbn in WAIT;try discriminate;auto.
 inversion H0;subst;cbn in WAIT;try discriminate;reflexivity.
Qed.
Lemma string_dead_steps ge cell m events target : string_steps ge cell(dead m)events target ->
 events=[] /\ target=dead m.
Proof. intros RUN;inversion RUN;subst;auto;exfalso;eapply string_dead_terminal;eassumption. Qed.
Theorem strlen_wait_then_loss ge cell p bytes k m n : c_string m p bytes ->
 string_steps ge cell(live(Callstate strlen_definition[address_value p]k m))
 (repeat string_wait n++[string_loss])(dead m).
Proof.
 intros OWN;induction n;cbn.
 - econstructor;[apply string_loss_everywhere|constructor].
 - econstructor;[eapply strlen_wait;exact OWN|exact IHn].
Qed.
Theorem string_no_builtin_bypass ge cell f opt ef types args k e le m ev target :
 string_step ge cell(live(State f(Sbuiltin opt ef types args)k e le m))ev target ->
 ev=string_loss /\ target=dead m.
Proof.
 intros STEP;inversion STEP;subst.
 destruct(no_library_builtin_bypass _ _ _ _ _ _ _ _ _ _ _ _ _ H)as[EV TARGET];subst;auto.
Qed.
Lemma string_steps_trans ge cell a first b second c :
 string_steps ge cell a first b -> string_steps ge cell b second c ->
 string_steps ge cell a(first++second)c.
Proof. intros AB BC;induction AB;cbn;auto;econstructor;eauto. Qed.
