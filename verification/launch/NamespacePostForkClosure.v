(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Scope a source call graph without certifying discarded caller statements. *)
From Stdlib Require Import List Bool String ZArith.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Cop Clight.
Require Import Machine LibraryMachine.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessGlobalCalls ProcessCaller ProcessDescriptor.
From EntryNamespace Require Import NamespaceMachine NamespaceStructure NamespacePaths NamespaceCaller NamespaceAfterFork.
Import ListNotations.

Definition postfork_lookup id:=NamespaceClosure.closure_lookup id.
Lemma postfork_lookup_same id:postfork_lookup id=NamespaceClosure.closure_lookup id.
Proof. reflexivity. Qed.

Definition postfork_member (ids:list ident) id :=existsb(Pos.eqb id)ids.
Definition postfork_call fn :=match fn with
  |Evar id(Tfunction _ _ _)=>postfork_member after_fork_calls id&&caller_global_id id
  |_=>false end.

Fixpoint postfork_statement statement : bool :=match statement with
  |Scall _ fn _=>postfork_call fn
  |Sgoto id=>Pos.eqb id _report
  |Sbuiltin _ _ _ _=>false
  |Ssequence first rest|Sifthenelse _ first rest|Sloop first rest=>
    postfork_statement first&&postfork_statement rest
  |Sswitch _ branches=>postfork_branches branches
  |Slabel _ body=>postfork_statement body
  |_=>true end
with postfork_branches branches : bool :=match branches with
  |LSnil=>true|LScons _ body rest=>postfork_statement body&&postfork_branches rest end.

Definition postfork_function fd :=exists id,
  In id after_fork_calls /\postfork_lookup id=Some fd.

Definition postfork_fn_tag fn:=postfork_function(Internal fn)\/fn=f_namespace_init\/fn=f_create_entry_child.

Fixpoint postfork_cont continuation : Prop :=match continuation with
  |Kstop=>True
  |Kseq body rest=>postfork_statement body=true /\postfork_cont rest
  |Kloop1 first second rest|Kloop2 first second rest=>
    postfork_statement first=true /\postfork_statement second=true /\postfork_cont rest
  |Kswitch rest=>postfork_cont rest
  |Kcall _ caller _ _ rest=>postfork_fn_tag caller /\postfork_cont rest end.

Definition postfork_control state :=match state with
  |State fn body k _ _ _=>postfork_fn_tag fn /\postfork_statement body=true /\postfork_cont k
  |Callstate fd _ k _=>postfork_function fd /\postfork_cont k
  |Returnstate _ k _=>postfork_cont k end.
Definition postfork_state state:=caller_state_global state /\postfork_control state.
Definition postfork_machine state:=match state with
  |live state=>postfork_state state|dead _=>True end.

Definition postfork_profile:=forallb(fun id=>match postfork_lookup id with
  |Some(Internal fn)=>postfork_statement(fn_body fn)
  |Some(External _ _ _ _)=>true|None=>false end)after_fork_calls.

Local Opaque caller_ge postfork_lookup.

Lemma postfork_function_body fn:
  postfork_profile=true ->postfork_function(Internal fn) ->
  postfork_statement(fn_body fn)=true.
Proof.
  intros PROFILE[id[MEMBER LOOKUP]]. unfold postfork_profile in PROFILE.
  apply forallb_forall with(x:=id)in PROFILE;[rewrite LOOKUP in PROFILE;exact PROFILE|exact MEMBER].
Qed.

Lemma postfork_call_shape fn:
  postfork_call fn=true ->exists id types result cc,
    fn=Evar id(Tfunction types result cc) /\In id after_fork_calls /\caller_global_id id=true.
Proof.
  destruct fn;cbn[postfork_call];try discriminate.
  destruct t;try discriminate;intros GOOD;apply andb_true_iff in GOOD as[MEMBER GLOBAL].
  unfold postfork_member in MEMBER;apply existsb_exists in MEMBER as[found[IN EQ]].
  apply Pos.eqb_eq in EQ;subst found;do 4 eexists;auto.
Qed.

Lemma postfork_call_cont k:postfork_cont k ->postfork_cont(call_cont k).
Proof. induction k;cbn;intuition. Qed.

Lemma postfork_seq_branches branches:
  postfork_branches branches=true ->postfork_statement(seq_of_labeled_statement branches)=true.
Proof. induction branches;cbn;auto;rewrite !andb_true_iff;intuition. Qed.
Lemma postfork_select_default branches:
  postfork_branches branches=true ->postfork_branches(select_switch_default branches)=true.
Proof. induction branches;cbn;auto;destruct o;cbn;rewrite ?andb_true_iff;intuition. Qed.
Lemma postfork_select_case n branches:
  postfork_branches branches=true ->
  match select_switch_case n branches with Some selected=>postfork_branches selected=true|None=>True end.
Proof.
  induction branches;cbn;auto;rewrite andb_true_iff;intros[BODY REST].
  destruct o;cbn.
  - destruct(zeq z n);cbn;[rewrite andb_true_iff;auto|exact(IHbranches REST)].
  - exact(IHbranches REST).
Qed.
Lemma postfork_select_switch n branches:
  postfork_branches branches=true ->postfork_branches(select_switch n branches)=true.
Proof.
  intro GOOD;unfold select_switch;pose proof(postfork_select_case n branches GOOD)as CASE.
  destruct(select_switch_case n branches);auto;apply postfork_select_default;exact GOOD.
Qed.

Local Transparent caller_ge postfork_lookup NamespaceClosure.closure_lookup.
Theorem postfork_source_profile:postfork_profile=true.
Proof. unfold postfork_profile,postfork_lookup,NamespaceClosure.closure_lookup,caller_ge;vm_compute;reflexivity. Qed.

Definition postfork_report_body:=match find_label _report(fn_body f_namespace_init)Kstop with
  |Some(body,_)=>body|None=>Sskip end.
Definition postfork_report_tail:=match find_label _report(fn_body f_namespace_init)Kstop with
  |Some(_,Kseq body Kstop)=>body|_=>Sskip end.
Lemma postfork_report_label k:find_label _report(fn_body f_namespace_init)k=
  Some(postfork_report_body,Kseq postfork_report_tail k).
Proof. vm_compute;reflexivity. Qed.
Lemma postfork_report_closed:postfork_statement postfork_report_body=true.
Proof. vm_compute;reflexivity. Qed.

Lemma postfork_report_tail_closed:postfork_statement postfork_report_tail=true.
Proof. vm_compute;reflexivity. Qed.

Fixpoint postfork_report_free body:=match body with
  |Ssequence first rest|Sifthenelse _ first rest|Sloop first rest=>
    postfork_report_free first&&postfork_report_free rest
  |Sswitch _ branches=>postfork_report_free_branches branches
  |Slabel id body=>negb(Pos.eqb id _report)&&postfork_report_free body
  |_=>true end
with postfork_report_free_branches branches:=match branches with
  |LSnil=>true|LScons _ body rest=>postfork_report_free body&&postfork_report_free_branches rest end.
Lemma postfork_report_free_label body k:
  postfork_report_free body=true ->find_label _report body k=None
with postfork_report_free_label_branches branches k:
  postfork_report_free_branches branches=true ->find_label_ls _report branches k=None.
Proof.
  - destruct body;cbn;intros GOOD;try reflexivity.
    + apply andb_true_iff in GOOD as[FIRST SECOND].
      rewrite(postfork_report_free_label body1(Kseq body2 k)FIRST).
      exact(postfork_report_free_label body2 k SECOND).
    + apply andb_true_iff in GOOD as[FIRST SECOND].
      rewrite(postfork_report_free_label body1 k FIRST).
      exact(postfork_report_free_label body2 k SECOND).
    + apply andb_true_iff in GOOD as[FIRST SECOND].
      rewrite(postfork_report_free_label body1(Kloop1 body1 body2 k)FIRST).
      exact(postfork_report_free_label body2(Kloop2 body1 body2 k)SECOND).
    + exact(postfork_report_free_label_branches l(Kswitch k)GOOD).
    + apply andb_true_iff in GOOD as[DIFFERENT BODY].
      apply negb_true_iff in DIFFERENT.
      destruct(ident_eq _report l)as[SAME|OTHER];
        [subst l;vm_compute in DIFFERENT;discriminate|apply postfork_report_free_label;exact BODY].
  - destruct branches;cbn;intros GOOD;try reflexivity.
    apply andb_true_iff in GOOD as[BODY REST].
    rewrite(postfork_report_free_label s(Kseq(seq_of_labeled_statement branches)k)BODY).
    exact(postfork_report_free_label_branches branches k REST).
Qed.
Definition postfork_report_free_profile:=forallb(fun id=>match postfork_lookup id with
  |Some(Internal fn)=>postfork_report_free(fn_body fn)|_=>true end)after_fork_calls.
Lemma postfork_report_free_source:postfork_report_free_profile=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque caller_ge postfork_lookup.

Lemma postfork_tag_label_safe fn:
  postfork_fn_tag fn ->forall k,postfork_cont k ->forall body rest,
  find_label _report(fn_body fn)k=Some(body,rest) ->
  postfork_statement body=true /\postfork_cont rest.
Proof.
  intros[MEMBER|[SAME|SAME]];subst.
  - destruct MEMBER as[id[MEMBER LOOKUP]].
    pose proof postfork_report_free_source as PROFILE;unfold postfork_report_free_profile in PROFILE.
    apply forallb_forall with(x:=id)in PROFILE;[rewrite LOOKUP in PROFILE|exact MEMBER].
    intros k CONT body rest FOUND;rewrite(postfork_report_free_label _ _ PROFILE)in FOUND;discriminate.
  - intros k CONT body rest FOUND;rewrite postfork_report_label in FOUND;inversion FOUND;subst;
      split;[exact postfork_report_closed|cbn[postfork_cont];split;[exact postfork_report_tail_closed|exact CONT]].
  - intros k CONT body rest FOUND;vm_compute in FOUND;discriminate.
Qed.

Local Opaque caller_ge postfork_lookup.

Lemma postfork_tag_from_function fn:postfork_function(Internal fn)->postfork_fn_tag fn.
Proof. intro MEMBER;left;exact MEMBER. Qed.
Lemma postfork_namespace_tag:postfork_fn_tag f_namespace_init.
Proof. right;left;reflexivity. Qed.
Lemma postfork_creation_tag:postfork_fn_tag f_create_entry_child.
Proof. right;right;reflexivity. Qed.
Local Opaque postfork_fn_tag postfork_profile after_fork_calls.

Lemma postfork_lookup_actual id block definition:
  Genv.find_symbol caller_ge id=Some block ->Genv.find_funct caller_ge(Vptr block Ptrofs.zero)=Some definition ->
  postfork_lookup id=Some definition.
Proof. intros SYMBOL FOUND;apply ProcessDescriptor.descriptor_lookup_actual with(block:=block);assumption. Qed.


Theorem postfork_source_step before trace after:
  postfork_profile=true ->postfork_state before ->step2 caller_ge before trace after ->
  postfork_state after.
Proof.
  intros PROFILE[GLOBAL CONTROL]STEP;split;[eapply caller_global_step;eassumption|].
  inversion STEP;subst.
  all:cbn[postfork_control postfork_statement postfork_cont]in CONTROL|-*.
  all:repeat rewrite andb_true_iff in CONTROL|-*.
  all:try tauto.
  all:try solve[repeat split;try tauto;apply andb_true_iff;tauto].
  all:try solve[destruct CONTROL as[TAG[BOOL CONT]];apply andb_true_iff in BOOL;tauto].
  all:try solve[match type of CONTROL with _ /\ false=true /\ _=>destruct CONTROL as[_[BAD _]];discriminate BAD end].
  - destruct CONTROL as[TAG[CALL CONT]].
    destruct(postfork_call_shape _ CALL)as[id[types[result[cc[SHAPE[MEMBER IDENT]]]]]];subst.
    destruct GLOBAL as[ENV GLOBAL_CONT].
    match goal with VALUE:eval_expr caller_ge _ _ _ (Evar id _) _|-_=>
      destruct(caller_global_function_value _ _ _ _ _ _ _ _ ENV IDENT VALUE)
        as[pointer[SYMBOL FUNCTION]];subst end.
    split;[exists id;split;[exact MEMBER|eapply postfork_lookup_actual;eassumption]|split;[exact TAG|exact CONT]].

  - destruct CONTROL as[TAG[BOOL CONT]];apply andb_true_iff in BOOL;destruct b;cbn;tauto.
  - apply postfork_call_cont;tauto.
  - apply postfork_call_cont;tauto.
  - destruct CONTROL as[TAG[BODY CONT]];split;[exact TAG|];split.
    + apply postfork_seq_branches,postfork_select_switch;exact BODY.
    + exact CONT.
  - destruct CONTROL as[TAG[ALLOWED CONT]].
    match goal with FOUND:find_label ?label _ _=Some _|-_=>
      assert(SAME:label=_report)by(apply Pos.eqb_eq;change(Pos.eqb label _report=true)in ALLOWED;exact ALLOWED);
      rewrite SAME in FOUND end.
    split;[exact TAG|].
    eapply postfork_tag_label_safe;[exact TAG|apply postfork_call_cont;exact CONT|eassumption].
  - destruct CONTROL as[FUNCTION CONT];split;[apply postfork_tag_from_function;exact FUNCTION|];split;[eapply postfork_function_body;eassumption|exact CONT].
Qed.

Lemma postfork_original_step cell before event after:
  postfork_profile=true ->postfork_machine before ->Machine.step caller_ge cell before event after ->
  postfork_machine after.
Proof.
  intros PROFILE GOOD STEP;inversion STEP;subst;cbn[postfork_machine postfork_state postfork_control caller_state_global]in *;try tauto;auto.
  eapply postfork_source_step;eassumption.
  all:unfold postfork_state,postfork_control,caller_state_global in *;cbn in *;tauto.
Qed.
Lemma postfork_library_step cell before event after:
  postfork_profile=true ->postfork_machine before ->library_step caller_ge cell before event after ->
  postfork_machine after.
Proof.
  intros PROFILE GOOD STEP;inversion STEP;subst;cbn[postfork_machine postfork_state postfork_control caller_state_global]in *;try tauto;auto.
  eapply postfork_original_step;eassumption.
  all:unfold postfork_state,postfork_control,caller_state_global in *;cbn in *;tauto.
Qed.
Lemma postfork_entry_step cell before event after:
  postfork_profile=true ->postfork_machine before ->entry_handoff_step caller_ge cell before event after ->
  postfork_machine after.
Proof.
  intros PROFILE GOOD STEP;inversion STEP;subst;cbn[postfork_machine postfork_state postfork_control caller_state_global]in *;try tauto;auto.
  eapply postfork_library_step;eassumption.
  all:unfold postfork_state,postfork_control,caller_state_global in *;cbn in *;tauto.
Qed.
Lemma postfork_process_step cell before event after:
  postfork_profile=true ->postfork_machine before ->process_step caller_ge cell before event after ->
  postfork_machine after.
Proof.
  intros PROFILE GOOD STEP;inversion STEP;subst;cbn[postfork_machine postfork_state postfork_control caller_state_global]in *;try tauto;auto.
  eapply postfork_entry_step;eassumption.
  all:unfold postfork_state,postfork_control,caller_state_global in *;cbn in *;tauto.
Qed.
Theorem postfork_namespace_step cell before event after:
  postfork_profile=true ->postfork_machine before ->namespace_step caller_ge cell before event after ->
  postfork_machine after.
Proof.
  intros PROFILE GOOD STEP;inversion STEP;subst;cbn[postfork_machine postfork_state postfork_control caller_state_global]in *;try tauto;auto.
  eapply postfork_process_step;eassumption.
  all:unfold postfork_state,postfork_control,caller_state_global in *;cbn in *;tauto.
Qed.
Theorem postfork_namespace_prefix cell before events after:
  postfork_profile=true ->postfork_machine before ->namespace_steps caller_ge cell before events after ->
  postfork_machine after.
Proof.
  intros PROFILE GOOD RUN;revert GOOD;induction RUN;intros GOOD;auto.
  apply IHRUN;eapply postfork_namespace_step;eassumption.
Qed.



Lemma postfork_definition_allowed definition:
  postfork_function definition ->after_fork_external_allowed definition=true.
Proof.
  intros[id[MEMBER LOOKUP]];apply after_fork_definition_allowed.
  exists id;split;[exact MEMBER|rewrite <-postfork_lookup_same;exact LOOKUP].
Qed.
Theorem postfork_actual_event cell before event after:
  postfork_machine before ->namespace_step caller_ge cell before event after ->
  NamespaceDescriptorFrame.namespace_after_fork_event event=true.
Proof.
  intros GOOD STEP;inversion STEP;subst;try reflexivity.
  all:cbn[postfork_machine postfork_state postfork_control]in GOOD;
    destruct GOOD as[GLOBAL[FUNCTION CONT]];
    pose proof(postfork_definition_allowed _ FUNCTION)as EXCLUDED;discriminate.
Qed.
Theorem postfork_actual_events cell before events after:
  postfork_machine before ->namespace_steps caller_ge cell before events after ->
  Forall(fun event=>NamespaceDescriptorFrame.namespace_after_fork_event event=true)events.
Proof.
  intros INITIAL RUN;revert INITIAL;induction RUN;intros INITIAL;[constructor|].
  constructor;[eapply postfork_actual_event;eassumption|].
  apply IHRUN;eapply postfork_namespace_step;[exact postfork_source_profile|exact INITIAL|exact H].
Qed.

Local Transparent after_fork_calls.
Lemma postfork_actual_continuation_statements:
  postfork_statement child_fork_set=true /\
  postfork_statement(child_tail 8(fn_body f_create_entry_child))=true /\
  postfork_statement namespace_creation_set=true /\postfork_statement(namespace_tail 10)=true.
Proof. vm_compute;repeat split;reflexivity. Qed.
Local Opaque after_fork_calls.

Theorem actual_fork_return_source_closed pair child_temps e le memory child:
  caller_env_global e ->postfork_machine
    (live(Returnstate(Vint child)(child_fork_cont pair child_temps(namespace_creation_cont e le Kstop))memory)).
Proof.
  intro GLOBAL;split.
  - cbn[caller_state_global child_fork_cont namespace_creation_cont caller_cont_global].
    repeat split;try exact GLOBAL;try apply after_fork_child_environment_global;exact I.
  - cbn[postfork_control child_fork_cont namespace_creation_cont postfork_cont].
    destruct postfork_actual_continuation_statements as[CHILD_SET[CHILD_TAIL[CREATION_SET NAMESPACE_TAIL]]].
    repeat first[assumption|apply postfork_creation_tag|apply postfork_namespace_tag|split|exact I].
Qed.
Theorem actual_fork_return_no_capability_export cell pair child_temps e le memory child events target:
  caller_env_global e ->namespace_steps namespace_ge cell
    (live(Returnstate(Vint child)(child_fork_cont pair child_temps(namespace_creation_cont e le Kstop))memory))events target ->
  Forall(fun event=>NamespaceDescriptorFrame.namespace_after_fork_event event=true)events.
Proof.
  intros GLOBAL RUN;eapply postfork_actual_events;
    [apply actual_fork_return_source_closed;exact GLOBAL|exact RUN].
Qed.

Theorem actual_creation_return_source_closed e le memory returned:
  caller_env_global e ->postfork_machine
    (live(Returnstate returned(namespace_creation_cont e le Kstop)memory)).
Proof.
  intro GLOBAL;split.
  - cbn[caller_state_global namespace_creation_cont caller_cont_global];split;[exact GLOBAL|exact I].
  - cbn[postfork_control namespace_creation_cont postfork_cont].
    destruct postfork_actual_continuation_statements as[A[B[SET TAIL]]].
    repeat first[assumption|apply postfork_namespace_tag|split|exact I].
Qed.

Theorem postfork_cannot_call_fork cell before events k memory:
  postfork_machine before ->
  ~namespace_steps caller_ge cell before events(live(Callstate namespace_fork_definition[]k memory)).
Proof.
  intros INITIAL RUN.
  pose proof(postfork_namespace_prefix _ _ _ _ postfork_source_profile INITIAL RUN)as FINAL.
  destruct FINAL as[GLOBAL[FUNCTION CONT]].
  pose proof(postfork_definition_allowed _ FUNCTION)as EXCLUDED;discriminate.
Qed.
