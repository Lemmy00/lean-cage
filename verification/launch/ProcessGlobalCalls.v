(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-entry.provenance: Direct calls resolve to the global function without local aliases. *)
From Stdlib Require Import ZArith List Bool String.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
From EntryNative Require Import EntrySource.
From EntryProcess Require Import ProcessControl ProcessMachine.
Import ListNotations.
Local Open Scope Z_scope.

Definition caller_ge:=Clight.globalenv EntrySource.prog.
Definition caller_function_ids:=map fst(filter(fun item=>
  match snd item with Gfun _=>true|_=>false end)(prog_defs EntrySource.prog)).
Definition caller_global_id id:=existsb(Pos.eqb id)caller_function_ids.
Definition caller_global_call fn(args:list expr):=match fn with
  |Evar id(Tfunction _ _ _)=>caller_global_id id|_=>false end.
Definition caller_vars_safe fn:=forallb(fun item=>negb(caller_global_id(fst item)))(fn_vars fn).
Definition caller_globals_checked:=forallb(fun item=>match snd item with
  |Gfun(Internal fn)=>caller_vars_safe fn&&checked_statement caller_global_call(fn_body fn)
  |_=>true end)(prog_defs EntrySource.prog).

Theorem caller_globals_source_checked:caller_globals_checked=true.
Proof. vm_compute;reflexivity. Qed.

Definition caller_ptrace_binding_checked:=forallb(fun id=>match Genv.find_symbol caller_ge id with
  |Some pointer=>match Genv.find_funct caller_ge(Vptr pointer Ptrofs.zero)with
    |Some(External(EF_external name _) _ _ _)=>
      if String.eqb name "entry_ptrace4" then Pos.eqb id _entry_ptrace4 else true
    |_=>true end
  |_=>true end)caller_function_ids.

Theorem caller_ptrace_binding_source:caller_ptrace_binding_checked=true.
Proof. vm_compute;reflexivity. Qed.

Theorem caller_namespace_binding:exists pointer,
  Genv.find_symbol caller_ge _namespace_init=Some pointer /\
  Genv.find_funct caller_ge(Vptr pointer Ptrofs.zero)=Some(Internal f_namespace_init).
Proof. eexists;split;vm_compute;reflexivity. Qed.

Local Opaque EntrySource.prog.

Lemma caller_global_id_member id:caller_global_id id=true ->In id caller_function_ids.
Proof.
  unfold caller_global_id;rewrite existsb_exists;intros[other[MEMBER SAME]].
  apply Pos.eqb_eq in SAME;subst other;exact MEMBER.
Qed.

Theorem caller_ptrace_unique id pointer:
  caller_global_id id=true ->Genv.find_symbol caller_ge id=Some pointer ->
  Genv.find_funct caller_ge(Vptr pointer Ptrofs.zero)=Some process_ptrace_definition ->id=_entry_ptrace4.
Proof.
  intros GLOBAL SYMBOL FUNCTION;pose proof caller_ptrace_binding_source as CHECK.
  unfold caller_ptrace_binding_checked in CHECK;apply forallb_forall with(x:=id)in CHECK;
    [|apply caller_global_id_member;exact GLOBAL].
  rewrite SYMBOL,FUNCTION in CHECK;cbn in CHECK;apply Pos.eqb_eq;exact CHECK.
Qed.

Theorem caller_function_source address fn:
  Genv.find_funct caller_ge address=Some(Internal fn) ->
  caller_vars_safe fn=true /\checked_statement caller_global_call(fn_body fn)=true.
Proof.
  intro FOUND;destruct(Genv.find_funct_inversion EntrySource.prog address FOUND)as[id MEMBER].
  pose proof caller_globals_source_checked as CHECK;unfold caller_globals_checked in CHECK.
  apply forallb_forall with(x:=(id,Gfun(Internal fn)))in CHECK;[|exact MEMBER].
  apply andb_true_iff in CHECK;exact CHECK.
Qed.

Local Opaque caller_global_id caller_function_ids.

Lemma caller_global_call_shape expression arguments:caller_global_call expression arguments=true ->
  exists id types result cc,expression=Evar id(Tfunction types result cc) /\caller_global_id id=true.
Proof.
  intro GLOBAL;destruct expression;cbn[caller_global_call]in GLOBAL;try discriminate GLOBAL.
  destruct t.
  - discriminate GLOBAL.
  - discriminate GLOBAL.
  - discriminate GLOBAL.
  - discriminate GLOBAL.
  - discriminate GLOBAL.
  - discriminate GLOBAL.
  - do 4 eexists;split;[reflexivity|exact GLOBAL].
  - discriminate GLOBAL.
  - discriminate GLOBAL.
Qed.



Definition caller_env_global(e:env):=forall id,caller_global_id id=true ->e!id=None.
Fixpoint caller_cont_global(k:cont):Prop:=match k with
  |Kstop=>True
  |Kseq _ rest|Kloop1 _ _ rest|Kloop2 _ _ rest|Kswitch rest=>caller_cont_global rest
  |Kcall _ _ e _ rest=>caller_env_global e /\caller_cont_global rest end.
Definition caller_state_global(state:Clight.state):Prop:=match state with
  |State _ _ k e _ _=>caller_env_global e /\caller_cont_global k
  |Callstate(Internal fn)_ k _=>caller_vars_safe fn=true /\caller_cont_global k
  |Callstate(External _ _ _ _)_ k _|Returnstate _ k _=>caller_cont_global k end.

Lemma caller_global_call_cont k:caller_cont_global k ->caller_cont_global(call_cont k).
Proof. induction k;cbn;intuition. Qed.

Lemma caller_alloc_env ge before vars e memory original:
  alloc_variables ge original before vars e memory ->caller_env_global original ->
  forallb(fun item=>negb(caller_global_id(fst item)))vars=true ->caller_env_global e.
Proof.
  intro ALLOC;induction ALLOC;intros ENV SAFE;[exact ENV|].
  change(negb(caller_global_id id)&&forallb(fun item=>negb(caller_global_id(fst item)))vars=true)in SAFE.
  apply andb_true_iff in SAFE as[FIRST REST].
  apply IHALLOC;[|exact REST]. intros wanted GLOBAL.
  rewrite PTree.gso;[apply ENV;exact GLOBAL|].
  intro SAME;subst wanted;apply Bool.negb_true_iff in FIRST;congruence.
Qed.

Lemma caller_internal_entry_global fn values before e le after:
  caller_vars_safe fn=true ->function_entry2 caller_ge fn values before e le after ->caller_env_global e.
Proof.
  intros SAFE ENTRY;inversion ENTRY;subst.
  eapply caller_alloc_env;[eassumption| |exact SAFE].
  intros id GLOBAL;apply PTree.gempty.
Qed.

Lemma caller_find_label label body k found rest:
  find_label label body k=Some(found,rest) ->caller_cont_global k ->caller_cont_global rest
with caller_find_label_branches label branches k found rest:
  find_label_ls label branches k=Some(found,rest) ->caller_cont_global k ->caller_cont_global rest.
Proof.
  - destruct body;cbn;intros FOUND CONT;try discriminate.
    + destruct(find_label label body1(Kseq body2 k))as[[statement next]|]eqn:FIRST.
      * inversion FOUND;subst;eapply caller_find_label;[exact FIRST|exact CONT].
      * eapply caller_find_label;[exact FOUND|exact CONT].
    + destruct(find_label label body1 k)as[[statement next]|]eqn:FIRST.
      * inversion FOUND;subst;eapply caller_find_label;[exact FIRST|exact CONT].
      * eapply caller_find_label;[exact FOUND|exact CONT].
    + destruct(find_label label body1(Kloop1 body1 body2 k))as[[statement next]|]eqn:FIRST.
      * inversion FOUND;subst;eapply caller_find_label;[exact FIRST|exact CONT].
      * eapply caller_find_label;[exact FOUND|exact CONT].
    + eapply caller_find_label_branches;[exact FOUND|exact CONT].
    + destruct(ident_eq label l).
      * inversion FOUND;subst;exact CONT.
      * eapply caller_find_label;[exact FOUND|exact CONT].
  - destruct branches;cbn;intros FOUND CONT;try discriminate.
    destruct(find_label label s(Kseq(seq_of_labeled_statement branches)k))as[[statement next]|]eqn:FIRST.
    + inversion FOUND;subst;eapply caller_find_label;[exact FIRST|exact CONT].
    + eapply caller_find_label_branches;[exact FOUND|exact CONT].
Qed.

Theorem caller_global_step before trace after:
  caller_state_global before ->step2 caller_ge before trace after ->caller_state_global after.
Proof.
  intros GLOBAL STEP;inversion STEP;subst;cbn in *;try tauto.
  - destruct fd;cbn;[split;[eapply caller_function_source;eassumption|]|];tauto.
  - apply caller_global_call_cont;tauto.
  - apply caller_global_call_cont;tauto.
  - split;[tauto|]. eapply caller_find_label;[eassumption|apply caller_global_call_cont;tauto].
  - destruct GLOBAL as[SAFE CONT];split;[eapply caller_internal_entry_global;eassumption|exact CONT].
Qed.

Lemma caller_function_reference types result cc memory block offset value:
  deref_loc(Tfunction types result cc)memory block offset Full value ->value=Vptr block offset.
Proof. intro LOAD;inversion LOAD;subst;try discriminate;reflexivity. Qed.

Theorem caller_global_function_value e le memory id types result cc value:
  caller_env_global e ->caller_global_id id=true ->
  eval_expr caller_ge e le memory(Evar id(Tfunction types result cc))value ->
  exists pointer,Genv.find_symbol caller_ge id=Some pointer /\value=Vptr pointer Ptrofs.zero.
Proof.
  intros ENV GLOBAL VALUE;inversion VALUE;subst.
  match goal with LVALUE:eval_lvalue _ _ _ _ _ _ _ _|-_=>inversion LVALUE;subst end.
  - match goal with LOCAL:e!id=Some _|-_=>rewrite(ENV _ GLOBAL)in LOCAL;discriminate end.
  - match goal with LOAD:deref_loc _ _ ?location ?offset _ ?loaded|-_=>
      pose proof(caller_function_reference _ _ _ _ _ _ _ LOAD)as SAME;
      exists location;split;[assumption|exact SAME]end.
Qed.
