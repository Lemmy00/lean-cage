(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Production fault selection is the actual two-step constant-zero C function. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Slice Machine ClightSteps WriteAll StoreSteps Library LibraryMachine LibraryPreservation LibraryControl CallAccess LocalAccess Deterministic.
Import ListNotations.
Open Scope Z_scope.
Definition fault_symbols(ge:genv):=exists object,Genv.find_symbol ge _strcmp=Some object /\
  Genv.find_funct ge(Vptr object Ptrofs.zero)=Some strcmp_definition.
Definition mode_pointer(ge:genv)m mode:=exists object,Genv.find_symbol ge _mode=Some object /\
  Mem.loadv Mint64 m(Vptr object Ptrofs.zero)=Some(address_value mode).
Definition fault_input ge m mode name xs ys:=mode_pointer ge m mode /\c_string m mode xs /\c_string m name ys.
Definition fault_value(xs ys:list Byte.int):=Vint Int.zero.
Definition fault_initial name k m:=Callstate(Internal f_fault)[address_value name]k m.

Definition fault_strcmp_object:=match Genv.find_symbol(Clight.globalenv Slice.prog)_strcmp with
  |Some object=>object|None=>1%positive end.
Lemma fault_strcmp_symbol:Genv.find_symbol(Clight.globalenv Slice.prog)_strcmp=Some fault_strcmp_object.
Proof. reflexivity. Qed.
Lemma fault_strcmp_function:Genv.find_funct(Clight.globalenv Slice.prog)(Vptr fault_strcmp_object Ptrofs.zero)=Some strcmp_definition.
Proof. reflexivity. Qed.
Local Opaque fault_strcmp_object.
Theorem actual_fault_symbols:fault_symbols(Clight.globalenv Slice.prog).
Proof. exists fault_strcmp_object;split;[exact fault_strcmp_symbol|exact fault_strcmp_function]. Qed.

Theorem production_fault_path ge name k m:
  store_path ge(fun after=>after=m)(fault_initial name k m)2
    (Returnstate(Vint Int.zero)(call_cont k)m).
Proof.
  eapply store_next;[reflexivity|apply function_entry_source_edge|].
  - constructor.
    + constructor.
    + constructor;[cbn;tauto|constructor].
    + unfold list_disjoint,var_names;cbn;tauto.
    + constructor.
    + reflexivity.
  - eapply store_next;[reflexivity|apply unchanged_store_edge|].
    + eapply edge_return;[apply value_int|reflexivity].
    + apply store_done;reflexivity.
Qed.

Theorem fault_source_certificate ge cell m mode name xs ys:
  fault_symbols ge ->fault_input ge m mode name xs ys ->
  control_certificate ge cell(fun after=>after=m)
    (fun value after=>value=fault_value xs ys /\after=m)2(fault_initial name Kstop m).
Proof.
  intros SYMBOLS INPUT;eapply control_source_path with(count:=2%nat)(remaining:=0%nat).
  - apply production_fault_path.
  - apply control_return;[reflexivity|split;reflexivity].
Qed.

Theorem fault_return_exact cell m mode name xs ys events actual after:
  fault_input(Clight.globalenv Slice.prog)m mode name xs ys ->
  library_steps(Clight.globalenv Slice.prog)cell(live(fault_initial name Kstop m))events
    (live(Returnstate actual Kstop after)) ->actual=fault_value xs ys /\after=m.
Proof.
  intros INPUT RUN;exact(control_all_returns _ _ _ _ _ _ _ _ _
    (fault_source_certificate _ cell _ _ _ _ _ actual_fault_symbols INPUT)RUN).
Qed.

Theorem fault_all_prefixes cell m mode name xs ys events target:
  fault_input(Clight.globalenv Slice.prog)m mode name xs ys ->
  library_steps(Clight.globalenv Slice.prog)cell(live(fault_initial name Kstop m))events target ->
  routine_memory target=m /\(control_cost events<=3)%nat.
Proof.
  intros INPUT RUN;pose proof(fault_source_certificate _ cell _ _ _ _ _ actual_fault_symbols INPUT)as CERT.
  destruct(control_all_prefixes _ _ _ _ _ _ CERT _ _ RUN)as[MEM[BOUND REST]];auto.
Qed.

Theorem fault_defined_prefix cell m mode name xs ys events state:
  fault_input(Clight.globalenv Slice.prog)m mode name xs ys ->
  library_steps(Clight.globalenv Slice.prog)cell(live(fault_initial name Kstop m))events(live state) ->
  state=Returnstate(fault_value xs ys)Kstop m \/
  exists event target,control_progress event /\library_step(Clight.globalenv Slice.prog)cell(live state)event target.
Proof.
  intros INPUT RUN;pose proof(fault_source_certificate _ cell _ _ _ _ _ actual_fault_symbols INPUT)as CERT.
  destruct(control_defined_prefix _ _ _ _ _ _ _ _ CERT RUN)
    as[[value[after[STATE[VALUE MEM]]]]|PROGRESS];subst;auto.
Qed.

Lemma library_steps_trans ge cell before middle after first second:
  library_steps ge cell before first middle ->library_steps ge cell middle second after ->
  library_steps ge cell before(first++second)after.
Proof. intros FIRST SECOND;induction FIRST;cbn;[exact SECOND|econstructor;eauto]. Qed.

(* The compatibility argument is deliberately unused: this production function
   has no waiting boundary. The witness and its precise length are two steps. *)
Theorem fault_success_after_waits cell m mode name xs ys k(compatibility:nat):
  fault_input(Clight.globalenv Slice.prog)m mode name xs ys ->
  exists events,library_steps(Clight.globalenv Slice.prog)cell(live(fault_initial name k m))events
    (live(Returnstate(fault_value xs ys)(call_cont k)m)) /\
    length events=2%nat /\control_cost events=2%nat.
Proof.
  intro INPUT;exists(map original_event(repeat(source_step E0)2));split.
  - apply original_runs_preserved;eapply store_path_actual;apply production_fault_path.
  - split;reflexivity.
Qed.
