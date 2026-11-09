(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-entry.provenance: Namespace primitive prefixes retain the source tracer restrictions. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs
  Ctypes Ctypesdefs Cop Clight.
Require Import Machine LibraryMachine.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessControl ProcessControlMachine ProcessMachine ProcessTrace
  ProcessLineage ProcessConnection.
From EntryNamespace Require Import NamespaceMachine NamespaceControlMachine.
Import ListNotations.
Open Scope Z_scope.

Theorem namespace_source_tracer_callsite cell start events fn opt args k env temps memory ty :
  checked_machine tracer_call_allowed start ->
  namespace_steps(Clight.globalenv EntrySource.prog)cell start events
    (live(State fn(Scall opt(Evar _entry_ptrace4 ty)args)k env temps memory)) ->
  exists request child address data,args=[Econst_int request tint;child;address;data] /\
    ty=tracer_signature /\typeof child=tint /\
    (request=Int.repr 7 \/request=Int.repr 16896 \/request=Int.repr 16898) /\
    (request=Int.repr 16896 ->data=tracer_options).
Proof.
  intros INITIAL RUN.
  pose proof(checked_namespace_prefix tracer_call_allowed _ _ helper_function_checked
    _ _ _ INITIAL RUN)as[_[CALL _]].
  apply tracer_call_shape;exact CALL.
Qed.

Theorem namespace_source_request_word cell start events fn opt args k env temps memory ty
    event definition request child address data next :
  checked_machine tracer_call_allowed start ->
  namespace_steps(Clight.globalenv EntrySource.prog)cell start events
    (live(State fn(Scall opt(Evar _entry_ptrace4 ty)args)k env temps memory)) ->
  namespace_step(Clight.globalenv EntrySource.prog)cell
    (live(State fn(Scall opt(Evar _entry_ptrace4 ty)args)k env temps memory))event
    (live(Callstate definition[Vint request;Vint child;address;data]next memory)) ->
  tracer_request_allowed request=true.
Proof.
  intros INITIAL RUN STEP.
  destruct(namespace_source_tracer_callsite _ _ _ _ _ _ _ _ _ _ _ INITIAL RUN)
    as[word[child_expression[pointer[payload[ARGS[TYPE[CHILDTYPE[REQUEST OPTIONS]]]]]]]].
  subst args ty.
  assert(INTERNAL:internal_state(State fn
    (Scall opt(Evar _entry_ptrace4 tracer_signature)
      [Econst_int word tint;child_expression;pointer;payload])k env temps memory))by exact I.
  destruct(namespace_internal_step_exact _ _ _ _ _ INTERNAL STEP)as[original[EVENT REAL]].
  inversion REAL;subst;try match goal with BOUND:boundary _ _ _|-_=>inversion BOUND end.
  match goal with SOURCE:step2 _ _ _ _|-_=>inversion SOURCE;subst end.
  match goal with CLASS:classify_fun(typeof(Evar _entry_ptrace4 tracer_signature))=_|-_=>
    cbn[tracer_signature typeof classify_fun]in CLASS;inversion CLASS;subst end.
  match goal with VALUES:eval_exprlist _ _ _ _ _ _ _|-_=>
    destruct(tracer_argument_values _ _ _ _ _ _ _ _ _ VALUES)
      as[actual_child[actual_address[actual_data SAME]]]end.
  inversion SAME;subst word.
  destruct REQUEST as[ALLOWED|[ALLOWED|ALLOWED]];subst request;reflexivity.
Qed.

From LeanImport Require Import Lean.
From EntryProcess Require Import ProcessImport.
Local Close Scope lean_scope.
Local Open Scope Z_scope.

Theorem namespace_source_request_ordinary_Lean cell start events fn opt args k env temps memory ty
    event definition request child address data next :
  checked_machine tracer_call_allowed start ->
  namespace_steps(Clight.globalenv EntrySource.prog)cell start events
    (live(State fn(Scall opt(Evar _entry_ptrace4 ty)args)k env temps memory)) ->
  namespace_step(Clight.globalenv EntrySource.prog)cell
    (live(State fn(Scall opt(Evar _entry_ptrace4 ty)args)k env temps memory))event
    (live(Callstate definition[Vint request;Vint child;address;data]next memory)) ->
  LeanCage_Entry_NonSubstitutingRequest(Nat_of_nat(Z.to_nat(Int.unsigned request))).
Proof.
  intros INITIAL RUN STEP;apply checked_tracer_request_word.
  eapply namespace_source_request_word;eassumption.
Qed.

Theorem namespace_source_prctl_no_install cell start events fn opt args k env temps memory ty :
  checked_machine lineage_call_allowed start ->
  namespace_steps(Clight.globalenv EntrySource.prog)cell start events
    (live(State fn(Scall opt(Evar _entry_prctl5 ty)args)k env temps memory)) ->
  exists request request_type rest,args=Econst_int request request_type::rest /\request<>Int.repr 22.
Proof.
  intros INITIAL RUN.
  pose proof(checked_namespace_prefix lineage_call_allowed _ _ helper_lineage_function_checked
    _ _ _ INITIAL RUN)as[_[CALL _]].
  change(avoids_requests[22]args=true)in CALL.
  destruct(avoids_requests_exact _ _ CALL)as[request[request_type[rest[ARGS AVOIDS]]]].
  exists request,request_type,rest;split;[exact ARGS|apply AVOIDS;cbn;auto].
Qed.

Theorem namespace_source_syscall_no_bypass cell start events fn opt args k env temps memory ty :
  checked_machine lineage_call_allowed start ->
  namespace_steps(Clight.globalenv EntrySource.prog)cell start events
    (live(State fn(Scall opt(Evar _syscall ty)args)k env temps memory)) ->
  exists request request_type rest,args=Econst_int request request_type::rest /\
    request<>Int.repr 101 /\request<>Int.repr 157 /\request<>Int.repr 317.
Proof.
  intros INITIAL RUN.
  pose proof(checked_namespace_prefix lineage_call_allowed _ _ helper_lineage_function_checked
    _ _ _ INITIAL RUN)as[_[CALL _]].
  destruct args as[|first supplied];[discriminate CALL|].
  destruct first;try discriminate CALL.
  change((Int.unsigned i <?1073741824)&&avoids_requests[101;157;317](Econst_int i t::supplied)=true)in CALL.
  apply Bool.andb_true_iff in CALL as[CANONICAL CALL].
  destruct(avoids_requests_exact _ _ CALL)as[request[request_type[rest[ARGS AVOIDS]]]].
  exists request,request_type,rest;split;[exact ARGS|]. repeat split;apply AVOIDS;cbn;auto.
Qed.
