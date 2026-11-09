(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Namespace local allocation seeds provenance at the prepared frontier. *)
From Stdlib Require Import List Bool.
From compcert Require Import Maps AST Values Memory Clight.
Require Import Machine.
From EntryNative Require Import EntrySource.
From EntryProcess Require Import ProcessControl ProcessTrace ProcessStructure ProcessGlobalCalls ProcessCaller.

Lemma caller_checked_tail permitted :forall index body,
  checked_statement permitted body=true ->checked_statement permitted(admission_tail index body)=true.
Proof.
  intro index;induction index;intros body CHECKED;[exact CHECKED|].
  destruct body;cbn[admission_tail];try reflexivity.
  apply IHindex;apply Bool.andb_true_iff in CHECKED;exact(proj2 CHECKED).
Qed.

Theorem caller_namespace_allocated_environment before e after:
  alloc_variables caller_ge empty_env before(fn_vars f_namespace_init)e after ->caller_env_global e.
Proof.
  intro ALLOC;destruct caller_namespace_binding as[pointer[SYMBOL FUNCTION]].
  destruct(caller_function_source _ _ FUNCTION)as[VARIABLES BODY].
  eapply caller_alloc_env;[exact ALLOC| |exact VARIABLES]. intros id GLOBAL;apply PTree.gempty.
Qed.

Theorem caller_namespace_prepared_frontier index before e after le memory:
  alloc_variables caller_ge empty_env before(fn_vars f_namespace_init)e after ->
  caller_source_machine(live(State f_namespace_init(admission_tail index(fn_body f_namespace_init))
    Kstop e le memory)).
Proof.
  intro ALLOC;destruct caller_namespace_binding as[pointer[SYMBOL FUNCTION]].
  destruct(caller_function_source _ _ FUNCTION)as[VARIABLES BODY].
  pose proof(namespace_init_checked nil memory)as[TRACER TERMINAL].
  split.
  - split;[eapply caller_namespace_allocated_environment;exact ALLOC|exact I].
  - split.
    + split;[exact BODY|]. split;[apply caller_checked_tail;exact BODY|exact I].
    + split;[|exact I]. split;[exact TRACER|]. split;[apply caller_checked_tail;exact TRACER|exact I].
Qed.
