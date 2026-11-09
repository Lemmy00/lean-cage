(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.origin: The actual fork continuations cannot acquire, transfer, or fork descriptor capabilities. *)
From Stdlib Require Import ZArith List Bool String.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine LibraryMachine.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessGlobalCalls ProcessCaller.
From EntryNamespace Require Import NamespaceMachine NamespaceClosure NamespaceStructure NamespacePaths NamespaceCaller
  NamespaceDescriptorFrame NamespaceMemory NamespaceChildResult NamespaceAllocation.
Import ListNotations.

Definition after_fork_calls:=
  [_guest;_strcmp;_fail_child;_entry_decimal;_error_number;_number;_entry_descriptor_flags;_execve;
   _put32;_fault;_write_all;_write;___errno_location;__exit;_memcpy;
   _close;_admit_child;_release_child;_now_ms;_clock_gettime;_entry_ptrace4;_waitpid;
   _result_of;_send_frame;_put64;_get32;_kill;_read;_usleep].
Definition after_fork_external_allowed(definition:Clight.fundef):=match definition with
  |External(EF_external name _) _ _ _=>
    negb(String.eqb name "socketpair"||String.eqb name "entry_duplicate_above"||
      String.eqb name "entry_signal_mask"||String.eqb name "entry_signal_default"||String.eqb name "fork")
  |Internal _=>true|_=>false end.
Definition after_fork_profile:=forallb(fun id=>match closure_lookup id with
  |Some definition=>after_fork_external_allowed definition|None=>false end)after_fork_calls.
Theorem after_fork_source_closed:closure_profile after_fork_calls=true.
Proof. vm_compute;reflexivity. Qed.
Theorem after_fork_source_profile:after_fork_profile=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque caller_ge closure_lookup.
Lemma after_fork_definition_allowed definition:
  closure_function after_fork_calls definition ->after_fork_external_allowed definition=true.
Proof.
  intros[id[MEMBER LOOKUP]];pose proof after_fork_source_profile as PROFILE.
  unfold after_fork_profile in PROFILE;apply forallb_forall with(x:=id)in PROFILE;
    [rewrite LOOKUP in PROFILE;exact PROFILE|exact MEMBER].
Qed.

Theorem after_fork_actual_step cell before event after:
  closure_machine after_fork_calls before ->namespace_step caller_ge cell before event after ->
  namespace_after_fork_event event=true.
Proof.
  intros GOOD STEP;inversion STEP;subst;try reflexivity.
  all:cbn[closure_machine closure_state closure_control]in GOOD;
    destruct GOOD as[GLOBAL[FUNCTION CONT]];
    pose proof(after_fork_definition_allowed _ FUNCTION)as EXCLUDED;discriminate.
Qed.
Theorem after_fork_actual_events cell before events after:
  closure_machine after_fork_calls before ->namespace_steps caller_ge cell before events after ->
  Forall(fun event=>namespace_after_fork_event event=true)events.
Proof.
  intros INITIAL RUN;induction RUN;[constructor|].
  constructor;[eapply after_fork_actual_step;eassumption|].
  apply IHRUN;eapply closure_namespace_step;[exact after_fork_source_closed|exact INITIAL|exact H].
Qed.

Lemma after_fork_child_environment_global pair:caller_env_global(child_env pair).
Proof.
  intros id GLOBAL;apply child_nonlocal_bindings;intro SAME;subst id;vm_compute in GLOBAL;discriminate.
Qed.
