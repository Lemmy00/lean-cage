(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Scope a source call graph without certifying discarded caller statements. *)
From Stdlib Require Import List Bool String ZArith.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Cop Clight.
Require Import Machine LibraryMachine.
From EntryNative Require Import NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessGlobalCalls ProcessCaller.
From EntryNamespace Require Import NamespaceMachine.
Import ListNotations.

Definition closure_lookup id := match Genv.find_symbol caller_ge id with
  |Some pointer=>Genv.find_funct caller_ge(Vptr pointer Ptrofs.zero)|None=>None end.
Definition closure_member (ids:list ident) id :=existsb(Pos.eqb id)ids.
Definition closure_call ids fn :=match fn with
  |Evar id(Tfunction _ _ _)=>closure_member ids id&&caller_global_id id
  |_=>false end.

Fixpoint closure_statement ids statement : bool :=match statement with
  |Scall _ fn _=>closure_call ids fn
  |Sbuiltin _ _ _ _|Sgoto _=>false
  |Ssequence first rest|Sifthenelse _ first rest|Sloop first rest=>
    closure_statement ids first&&closure_statement ids rest
  |Sswitch _ branches=>closure_branches ids branches
  |Slabel _ body=>closure_statement ids body
  |_=>true end
with closure_branches ids branches : bool :=match branches with
  |LSnil=>true|LScons _ body rest=>closure_statement ids body&&closure_branches ids rest end.

Fixpoint closure_cont ids continuation : Prop :=match continuation with
  |Kstop=>True
  |Kseq body rest=>closure_statement ids body=true /\closure_cont ids rest
  |Kloop1 first second rest|Kloop2 first second rest=>
    closure_statement ids first=true /\closure_statement ids second=true /\closure_cont ids rest
  |Kswitch rest|Kcall _ _ _ _ rest=>closure_cont ids rest end.

Definition closure_function ids fd :=exists id,
  In id ids /\closure_lookup id=Some fd.
Definition closure_control ids state :=match state with
  |State _ body k _ _ _=>closure_statement ids body=true /\closure_cont ids k
  |Callstate fd _ k _=>closure_function ids fd /\closure_cont ids k
  |Returnstate _ k _=>closure_cont ids k end.
Definition closure_state ids state:=caller_state_global state /\closure_control ids state.
Definition closure_machine ids state:=match state with
  |live state=>closure_state ids state|dead _=>True end.

Definition closure_profile ids:=forallb(fun id=>match closure_lookup id with
  |Some(Internal fn)=>closure_statement ids(fn_body fn)
  |Some(External _ _ _ _)=>true|None=>false end)ids.

Lemma closure_function_body ids fn:
  closure_profile ids=true ->closure_function ids(Internal fn) ->
  closure_statement ids(fn_body fn)=true.
Proof.
  intros PROFILE[id[MEMBER LOOKUP]]. unfold closure_profile in PROFILE.
  apply forallb_forall with(x:=id)in PROFILE;[rewrite LOOKUP in PROFILE;exact PROFILE|exact MEMBER].
Qed.

Lemma closure_call_shape ids fn:
  closure_call ids fn=true ->exists id types result cc,
    fn=Evar id(Tfunction types result cc) /\In id ids /\caller_global_id id=true.
Proof.
  destruct fn;cbn[closure_call];try discriminate.
  destruct t;try discriminate;intros GOOD;apply andb_true_iff in GOOD as[MEMBER GLOBAL].
  unfold closure_member in MEMBER;apply existsb_exists in MEMBER as[found[IN EQ]].
  apply Pos.eqb_eq in EQ;subst found;do 4 eexists;auto.
Qed.

Lemma closure_call_cont ids k:closure_cont ids k ->closure_cont ids(call_cont k).
Proof. induction k;cbn;intuition. Qed.

Lemma closure_seq_branches ids branches:
  closure_branches ids branches=true ->closure_statement ids(seq_of_labeled_statement branches)=true.
Proof. induction branches;cbn;auto;rewrite !andb_true_iff;intuition. Qed.
Lemma closure_select_default ids branches:
  closure_branches ids branches=true ->closure_branches ids(select_switch_default branches)=true.
Proof. induction branches;cbn;auto;destruct o;cbn;rewrite ?andb_true_iff;intuition. Qed.
Lemma closure_select_case ids n branches:
  closure_branches ids branches=true ->
  match select_switch_case n branches with Some selected=>closure_branches ids selected=true|None=>True end.
Proof.
  induction branches;cbn;auto;rewrite andb_true_iff;intros[BODY REST].
  destruct o;cbn.
  - destruct(zeq z n);cbn;[rewrite andb_true_iff;auto|exact(IHbranches REST)].
  - exact(IHbranches REST).
Qed.
Lemma closure_select_switch ids n branches:
  closure_branches ids branches=true ->closure_branches ids(select_switch n branches)=true.
Proof.
  intro GOOD;unfold select_switch;pose proof(closure_select_case ids n branches GOOD)as CASE.
  destruct(select_switch_case n branches);auto;apply closure_select_default;exact GOOD.
Qed.

Theorem closure_source_step ids before trace after:
  closure_profile ids=true ->closure_state ids before ->step2 caller_ge before trace after ->
  closure_state ids after.
Proof.
  intros PROFILE[GLOBAL CONTROL]STEP;split;[eapply caller_global_step;eassumption|].
  inversion STEP;subst;cbn[closure_control closure_statement closure_cont]in *;
    repeat rewrite andb_true_iff in *;try solve[intuition discriminate].
  - destruct CONTROL as[CALL CONT].
    destruct(closure_call_shape _ _ CALL)as[id[types[result[cc[SHAPE[MEMBER IDENT]]]]]];subst.
    destruct GLOBAL as[ENV GLOBAL_CONT].
    match goal with VALUE:eval_expr caller_ge _ _ _ (Evar id _) _|-_=>
      destruct(caller_global_function_value _ _ _ _ _ _ _ _ ENV IDENT VALUE)
        as[pointer[SYMBOL FUNCTION]];subst end.
    split;[exists id;split;[exact MEMBER|unfold closure_lookup;rewrite SYMBOL;assumption]|exact CONT].
  - destruct b;cbn;tauto.
  - apply closure_call_cont;tauto.
  - apply closure_call_cont;tauto.
  - destruct CONTROL as[BODY CONT];split.
    + apply closure_seq_branches,closure_select_switch;exact BODY.
    + exact CONT.
  - destruct CONTROL as[FUNCTION CONT];split;[eapply closure_function_body;eassumption|exact CONT].
Qed.

Lemma closure_original_step ids cell before event after:
  closure_profile ids=true ->closure_machine ids before ->Machine.step caller_ge cell before event after ->
  closure_machine ids after.
Proof.
  intros PROFILE GOOD STEP;inversion STEP;subst;cbn[closure_machine closure_state closure_control caller_state_global]in *;try tauto;auto.
  eapply closure_source_step;eassumption.
  all:unfold closure_state,closure_control,caller_state_global in *;cbn in *;tauto.
Qed.
Lemma closure_library_step ids cell before event after:
  closure_profile ids=true ->closure_machine ids before ->library_step caller_ge cell before event after ->
  closure_machine ids after.
Proof.
  intros PROFILE GOOD STEP;inversion STEP;subst;cbn[closure_machine closure_state closure_control caller_state_global]in *;try tauto;auto.
  eapply closure_original_step;eassumption.
  all:unfold closure_state,closure_control,caller_state_global in *;cbn in *;tauto.
Qed.
Lemma closure_entry_step ids cell before event after:
  closure_profile ids=true ->closure_machine ids before ->entry_handoff_step caller_ge cell before event after ->
  closure_machine ids after.
Proof.
  intros PROFILE GOOD STEP;inversion STEP;subst;cbn[closure_machine closure_state closure_control caller_state_global]in *;try tauto;auto.
  eapply closure_library_step;eassumption.
  all:unfold closure_state,closure_control,caller_state_global in *;cbn in *;tauto.
Qed.
Lemma closure_process_step ids cell before event after:
  closure_profile ids=true ->closure_machine ids before ->process_step caller_ge cell before event after ->
  closure_machine ids after.
Proof.
  intros PROFILE GOOD STEP;inversion STEP;subst;cbn[closure_machine closure_state closure_control caller_state_global]in *;try tauto;auto.
  eapply closure_entry_step;eassumption.
  all:unfold closure_state,closure_control,caller_state_global in *;cbn in *;tauto.
Qed.
Theorem closure_namespace_step ids cell before event after:
  closure_profile ids=true ->closure_machine ids before ->namespace_step caller_ge cell before event after ->
  closure_machine ids after.
Proof.
  intros PROFILE GOOD STEP;inversion STEP;subst;cbn[closure_machine closure_state closure_control caller_state_global]in *;try tauto;auto.
  eapply closure_process_step;eassumption.
  all:unfold closure_state,closure_control,caller_state_global in *;cbn in *;tauto.
Qed.
Theorem closure_namespace_prefix ids cell before events after:
  closure_profile ids=true ->closure_machine ids before ->namespace_steps caller_ge cell before events after ->
  closure_machine ids after.
Proof.
  intros PROFILE GOOD RUN;revert GOOD;induction RUN;intros GOOD;auto.
  apply IHRUN;eapply closure_namespace_step;eassumption.
Qed.

Fixpoint closure_id_list_eq (left right:list ident):bool:=match left,right with
  |[],[]=>true
  |first::rest,other::remaining=>Pos.eqb first other&&closure_id_list_eq rest remaining
  |_,_=>false end.

Lemma closure_id_list_eq_reflexive ids:closure_id_list_eq ids ids=true.
Proof. induction ids;cbn;[reflexivity|rewrite Pos.eqb_refl,IHids;reflexivity]. Qed.

(* A finite parameter-identifier fingerprint is enough to exclude a particular
   function. Equality of function records entails equality of the fingerprint;
   this checker makes no claim that distinct bodies always have distinct tags. *)
Definition closure_parameter_excluded (fd:option Clight.fundef) forbidden:=match fd with
  |Some(Internal fn)=>negb(closure_id_list_eq(map fst(fn_params fn))forbidden)
  |Some(External _ _ _ _)=>true|None=>false end.
Definition closure_forbids_parameters ids forbidden:=
  forallb(fun id=>closure_parameter_excluded(closure_lookup id)forbidden)ids.

Local Opaque caller_ge closure_lookup.

Theorem closure_function_excludes_parameters ids forbidden:
  closure_forbids_parameters ids(map fst(fn_params forbidden))=true ->
  ~closure_function ids(Internal forbidden).
Proof.
  intros EXCLUDES[id[MEMBER LOOKUP]]. unfold closure_forbids_parameters in EXCLUDES.
  apply forallb_forall with(x:=id)in EXCLUDES;[|exact MEMBER].
  assert(FINAL:closure_parameter_excluded(Some(Internal forbidden))(map fst(fn_params forbidden))=true).
  { exact(eq_trans(f_equal(fun found=>closure_parameter_excluded found(map fst(fn_params forbidden)))
      (eq_sym LOOKUP))EXCLUDES). }
  change(negb(closure_id_list_eq(map fst(fn_params forbidden))(map fst(fn_params forbidden)))=true)in FINAL.
  rewrite closure_id_list_eq_reflexive in FINAL;discriminate.
Qed.

Theorem closure_namespace_cannot_call ids cell before events forbidden arguments continuation memory:
  closure_profile ids=true ->
  closure_forbids_parameters ids(map fst(fn_params forbidden))=true ->
  closure_machine ids before ->
  ~namespace_steps caller_ge cell before events
    (live(Callstate(Internal forbidden)arguments continuation memory)).
Proof.
  intros PROFILE EXCLUDES GOOD RUN.
  pose proof(closure_namespace_prefix ids cell before events _ PROFILE GOOD RUN)as FINAL.
  destruct FINAL as[GLOBAL[FUNCTION CONT]].
  exact(closure_function_excludes_parameters ids forbidden EXCLUDES FUNCTION).
Qed.
