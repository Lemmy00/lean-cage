(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-entry.provenance: Pending and issued tracer requests retain checked source arguments. *)
From Stdlib Require Import List ZArith Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine LibraryMachine.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessControl ProcessControlMachine ProcessMachine ProcessTrace ProcessGlobalCalls ProcessOptions.
From EntryNamespace Require Import NamespaceMachine NamespaceControlMachine.
Import ListNotations.
Local Opaque EntrySource.prog caller_ge caller_global_id caller_function_ids.

Definition caller_pending_request(state:Clight.state):Prop:=match state with
  |Callstate definition arguments _ _=>definition=process_ptrace_definition ->
    exists request child address data,arguments=[Vint request;child;address;data] /\
      tracer_request_allowed request=true /\
      (request=Int.repr 16896 ->data=Vlong(Int64.repr 1048592))
  |_=>True end.

Theorem caller_source_trace_arguments e le memory expression arguments types result cc
    pointer values:
  caller_env_global e ->caller_global_call expression arguments=true ->
  tracer_call_allowed expression arguments=true ->
  eval_expr caller_ge e le memory expression pointer ->
  eval_exprlist caller_ge e le memory arguments types values ->
  Genv.find_funct caller_ge pointer=Some process_ptrace_definition ->
  type_of_fundef process_ptrace_definition=Tfunction types result cc ->
  exists request child address data,values=[Vint request;child;address;data] /\
    tracer_request_allowed request=true /\
    (request=Int.repr 16896 ->data=Vlong(Int64.repr 1048592)).
Proof.
  intros ENV GLOBAL TRACE FUNCTION ARGUMENTS FOUND TYPE.
  destruct(caller_global_call_shape _ _ GLOBAL)as[id[formal_types[formal_result[formal_cc[SHAPE GLOBAL_ID]]]]];subst expression.
  destruct(caller_global_function_value _ _ _ _ _ _ _ _ ENV GLOBAL_ID FUNCTION)as[block[SYMBOL VALUE]];subst pointer.
  pose proof(caller_ptrace_unique _ _ GLOBAL_ID SYMBOL FOUND)as IDENTIFIER;subst id.
  destruct(tracer_call_shape _ _ TRACE)as[request[child[address[data[ARGS[SIGNATURE[CHILDTYPE[REQUEST OPTIONS]]]]]]]].
  subst arguments.
  change(Tfunction[tint;tint;tptr tvoid;tptr tvoid]tlong cc_default=Tfunction types result cc)in TYPE.
  inversion TYPE;subst types result cc.
  destruct(tracer_argument_values _ _ _ _ _ _ _ _ _ ARGUMENTS)
    as[actual_child[actual_address[actual_data VALUES]]].
  exists request,actual_child,actual_address,actual_data;split;[exact VALUES|]. split.
  - destruct REQUEST as[SAME|[SAME|SAME]];subst request;reflexivity.
  - intro SETOPTIONS;specialize(OPTIONS SETOPTIONS);subst data.
    destruct(caller_options_argument_values _ _ _ _ _ _ _ _ ARGUMENTS)
      as[child_value[address_value EXACT]].
    rewrite VALUES in EXACT;inversion EXACT;reflexivity.
Qed.

Theorem caller_pending_source_step before trace after:
  caller_state_global before ->checked_state caller_global_call before ->
  checked_state tracer_call_allowed before ->caller_pending_request before ->
  step2 caller_ge before trace after ->caller_pending_request after.
Proof.
  intros GLOBAL CALLS TRACER PENDING STEP;inversion STEP;subst;
    cbn[caller_pending_request]in *;try exact I.
  intro SAME;subst fd.
  destruct GLOBAL as[ENV CONT];destruct CALLS as[FUNCTIONS[CALL CALL_CONT]];
    destruct TRACER as[FUNCTIONS'[TRACE TRACE_CONT]].
  eapply caller_source_trace_arguments;eassumption.
Qed.

Definition caller_machine_global machine:=match machine with live state=>caller_state_global state|dead _=>True end.

Lemma caller_global_original_step cell before event after:
  caller_machine_global before ->Machine.step caller_ge cell before event after ->caller_machine_global after.
Proof.
  intros GLOBAL STEP;inversion STEP;subst;
    cbn[caller_machine_global caller_state_global]in *;auto.
  eapply caller_global_step;eassumption.
Qed.

Lemma caller_global_library_step cell before event after:
  caller_machine_global before ->library_step caller_ge cell before event after ->caller_machine_global after.
Proof.
  intros GLOBAL STEP;inversion STEP;subst;
    cbn[caller_machine_global caller_state_global]in *;auto.
  eapply caller_global_original_step;eassumption.
Qed.

Lemma caller_global_entry_step cell before event after:
  caller_machine_global before ->entry_handoff_step caller_ge cell before event after ->caller_machine_global after.
Proof.
  intros GLOBAL STEP;inversion STEP;subst;
    cbn[caller_machine_global caller_state_global]in *;auto.
  eapply caller_global_library_step;eassumption.
Qed.

Lemma caller_global_process_step cell before event after:
  caller_machine_global before ->process_step caller_ge cell before event after ->caller_machine_global after.
Proof.
  intros GLOBAL STEP;inversion STEP;subst;
    cbn[caller_machine_global caller_state_global]in *;auto.
  eapply caller_global_entry_step;eassumption.
Qed.

Theorem caller_global_namespace_step cell before event after:
  caller_machine_global before ->namespace_step caller_ge cell before event after ->caller_machine_global after.
Proof.
  intros GLOBAL STEP;inversion STEP;subst;
    cbn[caller_machine_global caller_state_global]in *;auto.
  eapply caller_global_process_step;eassumption.
Qed.

Definition caller_source_machine machine:=match machine with
  |live state=>caller_state_global state /\checked_state caller_global_call state /\
    checked_state tracer_call_allowed state /\caller_pending_request state
  |dead _=>True end.

Lemma caller_pending_original_step cell before event after:
  caller_source_machine before ->Machine.step caller_ge cell before event after ->
  match after with live state=>caller_pending_request state|dead _=>True end.
Proof.
  intros SOURCE STEP;inversion STEP;subst;
    cbn[caller_source_machine caller_pending_request]in *;try exact I;try tauto.
  destruct SOURCE as[GLOBAL[CALLS[TRACER PENDING]]];eapply caller_pending_source_step;eassumption.
Qed.

Lemma caller_pending_library_step cell before event after:
  caller_source_machine before ->library_step caller_ge cell before event after ->
  match after with live state=>caller_pending_request state|dead _=>True end.
Proof.
  intros SOURCE STEP;inversion STEP;subst;
    cbn[caller_source_machine caller_pending_request]in *;try exact I;try tauto.
  eapply caller_pending_original_step;eassumption.
Qed.

Lemma caller_pending_entry_step cell before event after:
  caller_source_machine before ->entry_handoff_step caller_ge cell before event after ->
  match after with live state=>caller_pending_request state|dead _=>True end.
Proof.
  intros SOURCE STEP;inversion STEP;subst;
    cbn[caller_source_machine caller_pending_request]in *;try exact I;try tauto.
  eapply caller_pending_library_step;eassumption.
Qed.

Lemma caller_pending_process_step cell before event after:
  caller_source_machine before ->process_step caller_ge cell before event after ->
  match after with live state=>caller_pending_request state|dead _=>True end.
Proof.
  intros SOURCE STEP;inversion STEP;subst;
    cbn[caller_source_machine caller_pending_request]in *;try exact I;try tauto.
  eapply caller_pending_entry_step;eassumption.
Qed.

Theorem caller_pending_namespace_step cell before event after:
  caller_source_machine before ->namespace_step caller_ge cell before event after ->
  match after with live state=>caller_pending_request state|dead _=>True end.
Proof.
  intros SOURCE STEP;inversion STEP;subst;
    cbn[caller_source_machine caller_pending_request]in *;try exact I;try tauto.
  eapply caller_pending_process_step;eassumption.
Qed.

Theorem caller_source_namespace_step cell before event after:
  caller_source_machine before ->namespace_step caller_ge cell before event after ->caller_source_machine after.
Proof.
  intros SOURCE STEP;pose proof(caller_pending_namespace_step _ _ _ _ SOURCE STEP)as PENDING.
  destruct after as[state|memory];[|exact I].
  assert(GLOBAL:caller_machine_global(live state)).
  { eapply caller_global_namespace_step;[|exact STEP]. destruct before;cbn[caller_source_machine]in SOURCE;tauto. }
  split;[exact GLOBAL|]. split.
  - change(checked_machine caller_global_call(live state)).
    eapply checked_namespace_step with(permitted:=caller_global_call);[| |exact STEP].
    + intros address fn FOUND;exact(proj2(caller_function_source _ _ FOUND)).
    + destruct before;cbn[caller_source_machine]in SOURCE;tauto.
  - split;[|exact PENDING].
    change(checked_machine tracer_call_allowed(live state)).
    eapply checked_namespace_step with(permitted:=tracer_call_allowed);[exact helper_function_checked| |exact STEP].
    destruct before;cbn[caller_source_machine]in SOURCE;tauto.
Qed.

Theorem caller_source_namespace_prefix cell before events after:
  caller_source_machine before ->namespace_steps caller_ge cell before events after ->caller_source_machine after.
Proof.
  intros SOURCE RUN;revert SOURCE;induction RUN;intros SOURCE;[exact SOURCE|].
  apply IHRUN;eapply caller_source_namespace_step;eassumption.
Qed.

Theorem caller_namespace_initial arguments memory:
  caller_source_machine(live(Callstate(Internal f_namespace_init)arguments Kstop memory)).
Proof.
  destruct caller_namespace_binding as[pointer[SYMBOL FOUND]].
  destruct(caller_function_source _ _ FOUND)as[VARIABLES CALLS].
  split;[split;[exact VARIABLES|exact I]|]. split;[split;[exact CALLS|exact I]|].
  split;[apply namespace_init_checked|]. intro IMPOSSIBLE;discriminate.
Qed.

Theorem caller_internal_initial address fn arguments memory :
  Genv.find_funct caller_ge address=Some(Internal fn) ->
  caller_source_machine(live(Callstate(Internal fn)arguments Kstop memory)).
Proof.
  intro FOUND;destruct(caller_function_source _ _ FOUND)as[VARIABLES CALLS].
  pose proof(helper_function_checked _ _ FOUND)as TRACER.
  split;[split;[exact VARIABLES|exact I]|]. split;[split;[exact CALLS|exact I]|].
  split;[split;[exact TRACER|exact I]|]. intro IMPOSSIBLE;discriminate.
Qed.

Lemma caller_pending_trace_word child request address data k memory:
  caller_source_machine(live(Callstate process_ptrace_definition[Vint request;Vint child;address;data]k memory)) ->
  tracer_request_allowed request=true.
Proof.
  intros[GLOBAL[CALLS[TRACER PENDING]]].
  destruct(PENDING eq_refl)as[word[child_value[address_value[data_value[VALUES[ALLOWED OPTIONS]]]]]].
  inversion VALUES;subst word;exact ALLOWED.
Qed.

Theorem caller_pending_options_value child address data k memory:
  caller_source_machine(live(Callstate process_ptrace_definition
    [Vint(Int.repr 16896);Vint child;address;data]k memory)) ->
  data=Vlong(Int64.repr 1048592).
Proof.
  intros[GLOBAL[CALLS[TRACER PENDING]]].
  destruct(PENDING eq_refl)as[word[child_value[address_value[data_value[VALUES[ALLOWED OPTIONS]]]]]].
  inversion VALUES;subst word data_value;apply OPTIONS;reflexivity.
Qed.

Definition caller_event_requests event:list int:=match event with
  |namespace_process(process_traced request _ _ _ _)=>[request]
  |namespace_process(process_trace_lost request _ _ _)=>[request]
  |_=>[] end.

Theorem caller_event_request_checked cell before event after request:
  caller_source_machine before ->namespace_step caller_ge cell before event after ->
  In request(caller_event_requests event) ->tracer_request_allowed request=true.
Proof.
  intros SOURCE STEP MEMBER;inversion STEP;subst;cbn[caller_event_requests]in MEMBER;try contradiction.
  match goal with PROCESS:process_step _ _ _ _ _|-_=>inversion PROCESS;subst end;
    cbn[caller_event_requests]in MEMBER;try contradiction;
    destruct MEMBER as[SAME|NONE];try contradiction;subst request;
    eapply caller_pending_trace_word;exact SOURCE.
Qed.

Theorem caller_actual_request_history cell before events after:
  caller_source_machine before ->namespace_steps caller_ge cell before events after ->
  Forall(fun request=>tracer_request_allowed request=true)(flat_map caller_event_requests events).
Proof.
  intros SOURCE RUN;revert SOURCE;induction RUN;intros SOURCE;cbn;[constructor|].
  apply Forall_app;split.
  - apply Forall_forall;intros request MEMBER;eapply caller_event_request_checked;eassumption.
  - apply IHRUN;eapply caller_source_namespace_step;eassumption.
Qed.

Theorem caller_actual_pending_request cell before events child request address data k memory:
  caller_source_machine before ->namespace_steps caller_ge cell before events
    (live(Callstate process_ptrace_definition[Vint request;Vint child;address;data]k memory)) ->
  tracer_request_allowed request=true.
Proof.
  intros SOURCE RUN;eapply caller_pending_trace_word;eapply caller_source_namespace_prefix;eassumption.
Qed.

Definition caller_event_options event:Prop:=match event with
  |namespace_process(process_traced request _ _ data _)=>
      request=Int.repr 16896 ->data=Vlong(Int64.repr 1048592)
  |namespace_process(process_trace_lost request _ _ data)=>
      request=Int.repr 16896 ->data=Vlong(Int64.repr 1048592)
  |_=>True end.

Theorem caller_event_options_checked cell before event after:
  caller_source_machine before ->namespace_step caller_ge cell before event after ->caller_event_options event.
Proof.
  intros SOURCE STEP;inversion STEP;subst;cbn[caller_event_options];try exact I.
  match goal with PROCESS:process_step _ _ _ _ _|-_=>inversion PROCESS;subst end;
    cbn[caller_event_options];try exact I;intro SETOPTIONS;subst request;
    eapply caller_pending_options_value;exact SOURCE.
Qed.

Theorem caller_actual_options_history cell before events after:
  caller_source_machine before ->namespace_steps caller_ge cell before events after ->Forall caller_event_options events.
Proof.
  intros SOURCE RUN;revert SOURCE;induction RUN;intros SOURCE;[constructor|].
  constructor;[eapply caller_event_options_checked;eassumption|].
  apply IHRUN;eapply caller_source_namespace_step;eassumption.
Qed.

Theorem caller_actual_pending_options cell before events child address data k memory:
  caller_source_machine before ->namespace_steps caller_ge cell before events
    (live(Callstate process_ptrace_definition[Vint(Int.repr 16896);Vint child;address;data]k memory)) ->
  data=Vlong(Int64.repr 1048592).
Proof.
  intros SOURCE RUN;eapply caller_pending_options_value;eapply caller_source_namespace_prefix;eassumption.
Qed.
