(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.origin: Reporting writes retain the actual non-address-taken fd parameter. *)
From Stdlib Require Import ZArith List Bool String.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs
  Ctypes Ctypesdefs Cop Clight.
Require Import IO Machine LibraryMachine.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessControl ProcessGlobalCalls ProcessCaller.
From EntryNamespace Require Import NamespaceMachine NamespaceClosure.
Import ListNotations.

Definition descriptor_calls := [_send_frame;_put32;_put64;_memcpy;_fault;_write_all;_write;___errno_location].
Definition descriptor_mode fn := match fn_params fn with
  | (id,_)::_ => Pos.eqb id _fd | []=>false end.
Definition descriptor_required definition := match definition with
  | Internal fn=>descriptor_mode fn
  | External (EF_external name _) _ _ _=>String.eqb name "write"
  | _=>false end.
Definition descriptor_signature definition := match type_of_fundef definition with
  | Tfunction (Tint I32 Signed _::_) _ _=>true|_=>false end.
Definition descriptor_first arguments := match arguments with
  | Etempvar id (Tint I32 Signed _)::_=>Pos.eqb id _fd|_=>false end.
Definition descriptor_sensitive id :=
  Pos.eqb id _send_frame||Pos.eqb id _write_all||Pos.eqb id _write.
Definition descriptor_call mode expression arguments := match expression with
  | Evar id (Tfunction _ _ _) =>
      if descriptor_sensitive id then mode&&descriptor_first arguments else true
  |_=>false end.
Definition descriptor_opt option := match option with Some id=>negb(Pos.eqb id _fd)|None=>true end.
Fixpoint descriptor_immutable body := match body with
  | Sset id _=>negb(Pos.eqb id _fd)
  | Scall opt _ _=>descriptor_opt opt
  | Ssequence first rest|Sifthenelse _ first rest|Sloop first rest=>
      descriptor_immutable first&&descriptor_immutable rest
  | Sbuiltin _ _ _ _|Sgoto _|Sswitch _ _|Slabel _ _=>false
  |_=>true end.
Definition descriptor_function fn :=
  descriptor_immutable (fn_body fn)=true /\
  checked_statement (descriptor_call (descriptor_mode fn)) (fn_body fn)=true.
Definition descriptor_profile := forallb (fun id=>match closure_lookup id with
  |Some definition=>
    Bool.eqb(descriptor_required definition)(descriptor_sensitive id)&&
    (if descriptor_required definition then descriptor_signature definition else true)&&
    match definition with
    |Internal fn=>descriptor_immutable(fn_body fn)&&
      checked_statement(descriptor_call(descriptor_mode fn))(fn_body fn)
    |_=>true end
  |None=>false end)descriptor_calls.

Theorem descriptor_source_profile : descriptor_profile=true.
Proof. vm_compute;reflexivity. Qed.
Theorem descriptor_source_closure : closure_profile descriptor_calls=true.
Proof. vm_compute;reflexivity. Qed.

Theorem descriptor_sender_binding : closure_function descriptor_calls(Internal f_send_frame).
Proof. exists _send_frame;split;[unfold descriptor_calls;left;reflexivity|vm_compute;reflexivity]. Qed.
Theorem descriptor_write_all_binding : closure_function descriptor_calls(Internal f_write_all).
Proof. exists _write_all;split;[unfold descriptor_calls;do 5 right;left;reflexivity|vm_compute;reflexivity]. Qed.

Local Opaque EntrySource.prog caller_ge.

Lemma descriptor_lookup_actual id block definition :
  Genv.find_symbol caller_ge id=Some block ->
  Genv.find_funct caller_ge(Vptr block Ptrofs.zero)=Some definition ->
  closure_lookup id=Some definition.
Proof. intros SYMBOL FOUND;unfold closure_lookup;rewrite SYMBOL;exact FOUND. Qed.

Lemma descriptor_lookup_global id fn : closure_lookup id=Some(Internal fn) ->
  caller_vars_safe fn=true.
Proof.
  unfold closure_lookup;destruct(Genv.find_symbol caller_ge id)as[block|]eqn:SYMBOL;[|discriminate].
  intro FOUND;exact(proj1(caller_function_source _ _ FOUND)).
Qed.

Local Opaque closure_lookup descriptor_calls.

Lemma descriptor_function_checked fn : closure_function descriptor_calls (Internal fn) ->
  descriptor_function fn.
Proof.
  intros [id[MEMBER LOOKUP]];pose proof descriptor_source_profile as PROFILE.
  unfold descriptor_profile in PROFILE;apply forallb_forall with(x:=id)in PROFILE;[|exact MEMBER].
  rewrite LOOKUP in PROFILE;cbn -[descriptor_required descriptor_mode descriptor_signature descriptor_sensitive descriptor_immutable checked_statement] in PROFILE;repeat rewrite andb_true_iff in PROFILE;unfold descriptor_function;tauto.
Qed.

Lemma descriptor_function_signature definition : closure_function descriptor_calls definition ->
  descriptor_required definition=true ->descriptor_signature definition=true.
Proof.
  intros [id[MEMBER LOOKUP]] REQUIRED;pose proof descriptor_source_profile as PROFILE.
  unfold descriptor_profile in PROFILE;apply forallb_forall with(x:=id)in PROFILE;[|exact MEMBER].
  rewrite LOOKUP,REQUIRED in PROFILE;repeat rewrite andb_true_iff in PROFILE;tauto.
Qed.

Definition descriptor_temp fd fn le := descriptor_mode fn=true -> le!_fd=Some(Vint fd).
Definition descriptor_arguments fd definition arguments := descriptor_required definition=true ->
  exists rest,arguments=Vint fd::rest.
Fixpoint descriptor_cont fd mode continuation : Prop := match continuation with
  |Kstop=>True
  |Kseq body rest=>descriptor_immutable body=true /\
    checked_statement(descriptor_call mode)body=true /\descriptor_cont fd mode rest
  |Kloop1 first second rest|Kloop2 first second rest=>
    descriptor_immutable first=true /\descriptor_immutable second=true /\
    checked_statement(descriptor_call mode)first=true /\
    checked_statement(descriptor_call mode)second=true /\descriptor_cont fd mode rest
  |Kswitch _=>False
  |Kcall opt caller _ le rest=>descriptor_function caller /\descriptor_temp fd caller le /\
    descriptor_opt opt=true /\descriptor_cont fd (descriptor_mode caller) rest
  end.
Definition descriptor_control fd state : Prop := match state with
  |State fn body k _ le _=>descriptor_function fn /\descriptor_immutable body=true /\
    checked_statement(descriptor_call(descriptor_mode fn))body=true /\
    descriptor_temp fd fn le /\descriptor_cont fd (descriptor_mode fn)k
  |Callstate definition arguments k _=>descriptor_arguments fd definition arguments /\
    is_call_cont k /\descriptor_cont fd (descriptor_required definition)k
  |Returnstate _ k _=>is_call_cont k /\descriptor_cont fd false k
  end.
Definition descriptor_state fd state:=closure_state descriptor_calls state /\descriptor_control fd state.
Definition descriptor_machine fd state:=match state with live source=>descriptor_state fd source|dead _=>True end.

Lemma descriptor_call_cont fd mode target k : descriptor_cont fd mode k ->
  descriptor_cont fd target (call_cont k).
Proof. induction k;cbn;intuition. Qed.

Lemma descriptor_cont_call_mode fd mode target k : is_call_cont k ->
  descriptor_cont fd mode k ->descriptor_cont fd target k.
Proof. destruct k;cbn;intuition. Qed.

Lemma descriptor_call_cont_is_call k : is_call_cont(call_cont k).
Proof. induction k;cbn;auto. Qed.

Lemma descriptor_temp_set fd fn le id value : descriptor_temp fd fn le ->id<>_fd ->
  descriptor_temp fd fn(PTree.set id value le).
Proof. intros TEMP OTHER MODE;rewrite PTree.gso by congruence;apply TEMP;exact MODE. Qed.

Lemma descriptor_temp_optional fd fn le opt value : descriptor_temp fd fn le ->descriptor_opt opt=true ->
  descriptor_temp fd fn(set_opttemp opt value le).
Proof.
  intros TEMP OPTIONAL;destruct opt as[id|];[|exact TEMP].
  unfold descriptor_opt in OPTIONAL;apply negb_true_iff,Pos.eqb_neq in OPTIONAL.
  apply descriptor_temp_set;assumption.
Qed.

Lemma descriptor_bind_other formals arguments before after :
  ~In _fd(map fst formals) ->bind_parameter_temps formals arguments before=Some after ->
  after!_fd=before!_fd.
Proof.
  revert arguments before after;induction formals as[|[id ty]rest IH];
    intros arguments before after ABSENT BIND;destruct arguments;cbn in BIND;try discriminate.
  - inversion BIND;reflexivity.
  - rewrite (IH _ _ _ ltac:(cbn in ABSENT;intuition) BIND).
    rewrite PTree.gso;[reflexivity|];cbn in ABSENT;intuition.
Qed.

Lemma descriptor_function_entry fd fn args before e le after :
  descriptor_arguments fd(Internal fn)args ->
  function_entry2 caller_ge fn args before e le after ->descriptor_temp fd fn le.
Proof.
  intros ARGUMENTS ENTRY MODE.
  inversion ENTRY as[VARS PARAMETER_NAMES DISJOINT ALLOC BIND];subst.
  unfold descriptor_mode in MODE;destruct(fn_params fn)as[|[id ty]rest]eqn:PARAMS;[discriminate|].
  apply Pos.eqb_eq in MODE;subst id.
  destruct(ARGUMENTS ltac:(unfold descriptor_required,descriptor_mode;rewrite PARAMS;apply Pos.eqb_refl))
    as[remaining VALUES];subst args.
  assert(ABSENT:~In _fd(map fst rest)).
  { unfold var_names in PARAMETER_NAMES;try rewrite PARAMS in PARAMETER_NAMES.
    inversion PARAMETER_NAMES;subst;assumption. }
  try rewrite PARAMS in BIND;cbn in BIND.
  rewrite (descriptor_bind_other rest remaining _ _ ABSENT BIND);apply PTree.gss.
Qed.

Lemma descriptor_first_shape arguments : descriptor_first arguments=true ->
  exists attr rest,arguments=Etempvar _fd(Tint I32 Signed attr)::rest.
Proof.
  destruct arguments as[|argument rest];[discriminate|].
  destruct argument;cbn[descriptor_first];try discriminate.
  destruct t;try discriminate.
  match goal with size:intsize|-_=>destruct size end;try discriminate.
  match goal with sign:signedness|-_=>destruct sign end;try discriminate.
  intro IDENTIFIER;apply Pos.eqb_eq in IDENTIFIER;subst;eauto.
Qed.

Lemma descriptor_signature_shape definition : descriptor_signature definition=true ->
  exists attr rest result cc,type_of_fundef definition=Tfunction(Tint I32 Signed attr::rest)result cc.
Proof.
  unfold descriptor_signature;destruct(type_of_fundef definition);try discriminate.
  destruct l as[|first rest];[discriminate|].
  destruct first;try discriminate.
  match goal with size:intsize|-_=>destruct size end;try discriminate.
  match goal with sign:signedness|-_=>destruct sign end;try discriminate.
  intros;do 4 eexists;reflexivity.
Qed.

Lemma descriptor_argument_values ge e le memory fd expressions attr types values :
  le!_fd=Some(Vint fd) ->descriptor_first expressions=true ->
  eval_exprlist ge e le memory expressions(Tint I32 Signed attr::types)values ->
  exists rest,values=Vint fd::rest.
Proof.
  intros REGISTER FIRST ARGUMENTS.
  destruct(descriptor_first_shape _ FIRST)as[actual[rest SHAPE]];subst expressions.
  inversion ARGUMENTS;subst.
  match goal with VALUE:eval_expr _ _ _ _ (Etempvar _fd _) _|-_=>inversion VALUE;subst end.
  match goal with LOOKUP:le!_fd=Some ?value|-_=>
    assert(value=Vint fd)by congruence;subst value end.
  match goal with CAST:sem_cast _ _ _ _=Some _|-_=>cbn[sem_cast classify_cast]in CAST;inversion CAST;subst end.
  eexists;reflexivity.
  all:match goal with LOCATION:eval_lvalue _ _ _ _ (Etempvar _ _) _ _ _|-_=>inversion LOCATION end.
Qed.

Lemma descriptor_actual_call fd fn e le memory expression expressions types result cc
    pointer values definition :
  caller_env_global e ->closure_call descriptor_calls expression=true ->
  descriptor_call(descriptor_mode fn)expression expressions=true ->descriptor_temp fd fn le ->
  eval_expr caller_ge e le memory expression pointer ->
  eval_exprlist caller_ge e le memory expressions types values ->
  Genv.find_funct caller_ge pointer=Some definition ->
  type_of_fundef definition=Tfunction types result cc ->descriptor_arguments fd definition values.
Proof.
  intros GLOBAL CLOSED ALLOWED REGISTER FUNCTION ARGUMENTS FOUND TYPE REQUIRED.
  destruct(closure_call_shape _ _ CLOSED)as[id[formal[result_type[convention[EXPRESSION[MEMBER IDENTIFIER]]]]]];
    subst expression.
  destruct(caller_global_function_value _ _ _ _ _ _ _ _ GLOBAL IDENTIFIER FUNCTION)
    as[block[SYMBOL POINTER]];subst pointer.
  assert(LOOKUP:closure_lookup id=Some definition)by(eapply descriptor_lookup_actual;eassumption).
  assert(CALLEE:closure_function descriptor_calls definition)by(exists id;auto).
  pose proof(descriptor_function_signature _ CALLEE REQUIRED)as SIGNATURE.
  destruct(descriptor_signature_shape _ SIGNATURE)as[attr[rest[returned[cconv SIGNED]]]].
  rewrite TYPE in SIGNED;inversion SIGNED;subst types returned cconv.
  pose proof descriptor_source_profile as PROFILE.
  unfold descriptor_profile in PROFILE;apply forallb_forall with(x:=id)in PROFILE;[|exact MEMBER].
  rewrite LOOKUP,REQUIRED in PROFILE;repeat rewrite andb_true_iff in PROFILE.
  assert(SENSITIVE:descriptor_sensitive id=true).
  { destruct(descriptor_sensitive id);cbn in PROFILE;tauto. }
  cbn[descriptor_call]in ALLOWED;rewrite SENSITIVE in ALLOWED.
  apply andb_true_iff in ALLOWED as[MODE FIRST].
  eapply descriptor_argument_values;[apply REGISTER;exact MODE|exact FIRST|exact ARGUMENTS].
Qed.

Theorem descriptor_source_step fd before trace after :
  descriptor_state fd before ->step2 caller_ge before trace after ->descriptor_state fd after.
Proof.
  intros [CLOSED CONTROL] STEP;split.
  - eapply closure_source_step;[exact descriptor_source_closure|exact CLOSED|exact STEP].
  - inversion STEP;subst;
      cbn[descriptor_control descriptor_immutable descriptor_cont checked_statement]in *;
      repeat rewrite andb_true_iff in *;try solve[intuition discriminate].
    + destruct CONTROL as[FUNCTION[IMMUTABLE[CALLS[REGISTER CONT]]]].
      refine(conj FUNCTION(conj eq_refl(conj eq_refl(conj _ CONT)))).
      apply descriptor_temp_set;[exact REGISTER|].
      apply negb_true_iff,Pos.eqb_neq in IMMUTABLE;exact IMMUTABLE.
    + destruct CONTROL as[FUNCTION[IMMUTABLE[CALLS[REGISTER CONT]]]].
      destruct CLOSED as[[ENV GLOBAL_CONT][CALL CLOSED_CONT]].
      split.
      * eapply descriptor_actual_call;eassumption.
      * split;[exact I|]. cbn;exact(conj FUNCTION(conj REGISTER(conj IMMUTABLE CONT))).
    + destruct b;cbn;tauto.
    + destruct CONTROL as[FUNCTION[IMMUTABLE[CALLS[REGISTER CONT]]]].
      split;[apply descriptor_call_cont_is_call|].
      exact(descriptor_call_cont fd(descriptor_mode f)false k CONT).
    + destruct CONTROL as[FUNCTION[IMMUTABLE[CALLS[REGISTER CONT]]]].
      split;[apply descriptor_call_cont_is_call|].
      exact(descriptor_call_cont fd(descriptor_mode f)false k CONT).
    + destruct CONTROL as[FUNCTION[IMMUTABLE[CALLS[REGISTER CONT]]]].
      split;[assumption|]. eapply descriptor_cont_call_mode;[assumption|exact CONT].
    + destruct CONTROL as[ARGUMENTS[CALL CONT]].
      destruct CLOSED as[GLOBAL[FUNCTION CLOSED_CONT]].
      pose proof(descriptor_function_checked _ FUNCTION)as CHECKED.
      refine(conj CHECKED(conj(proj1 CHECKED)(conj(proj2 CHECKED)(conj _ CONT)))).
      eapply descriptor_function_entry;eassumption.
    + destruct CONTROL as[ARGUMENTS[CALL CONT]].
      split;[exact CALL|]. eapply descriptor_cont_call_mode;[exact CALL|exact CONT].
    + destruct CONTROL as[CALL CONT].
      destruct CONT as[FUNCTION[REGISTER[OPTIONAL CONT]]].
      refine(conj FUNCTION(conj eq_refl(conj eq_refl(conj _ CONT)))).
      eapply descriptor_temp_optional;eassumption.
Qed.

Lemma descriptor_external_return fd definition args k before value after :
  descriptor_control fd(Callstate definition args k before) ->
  descriptor_control fd(Returnstate value k after).
Proof.
  intros[ARGS[CALL CONT]];split;[exact CALL|].
  eapply descriptor_cont_call_mode;eassumption.
Qed.

Lemma descriptor_original_step fd cell before event after :
  descriptor_machine fd before ->Machine.step caller_ge cell before event after ->
  descriptor_machine fd after.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn[descriptor_machine]in *;try exact I;try exact GOOD.
  all:try solve[eapply descriptor_source_step;eassumption].
  all:destruct GOOD as[CLOSED CONTROL];split;
    [match type of STEP with Machine.step _ _ ?first ?current ?last=>
      exact(closure_original_step descriptor_calls cell first current last descriptor_source_closure CLOSED STEP)end|
      exact(descriptor_external_return fd _ _ _ _ _ _ CONTROL)].
Qed.

Lemma descriptor_library_step fd cell before event after :
  descriptor_machine fd before ->library_step caller_ge cell before event after ->
  descriptor_machine fd after.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn[descriptor_machine]in *;try exact I;try exact GOOD.
  all:try solve[eapply descriptor_original_step;eassumption].
  all:destruct GOOD as[CLOSED CONTROL];split;
    [match type of STEP with library_step _ _ ?first ?current ?last=>
      exact(closure_library_step descriptor_calls cell first current last descriptor_source_closure CLOSED STEP)end|
      exact(descriptor_external_return fd _ _ _ _ _ _ CONTROL)].
Qed.

Lemma descriptor_entry_step fd cell before event after :
  descriptor_machine fd before ->entry_handoff_step caller_ge cell before event after ->
  descriptor_machine fd after.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn[descriptor_machine]in *;try exact I;try exact GOOD.
  all:try solve[eapply descriptor_library_step;eassumption].
  all:destruct GOOD as[CLOSED CONTROL];split;
    [match type of STEP with entry_handoff_step _ _ ?first ?current ?last=>
      exact(closure_entry_step descriptor_calls cell first current last descriptor_source_closure CLOSED STEP)end|
      exact(descriptor_external_return fd _ _ _ _ _ _ CONTROL)].
Qed.

Lemma descriptor_process_step fd cell before event after :
  descriptor_machine fd before ->process_step caller_ge cell before event after ->
  descriptor_machine fd after.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn[descriptor_machine]in *;try exact I;try exact GOOD.
  all:try solve[eapply descriptor_entry_step;eassumption].
  all:destruct GOOD as[CLOSED CONTROL];split;
    [match type of STEP with process_step _ _ ?first ?current ?last=>
      exact(closure_process_step descriptor_calls cell first current last descriptor_source_closure CLOSED STEP)end|
      exact(descriptor_external_return fd _ _ _ _ _ _ CONTROL)].
Qed.

Theorem descriptor_namespace_step fd cell before event after :
  descriptor_machine fd before ->namespace_step caller_ge cell before event after ->
  descriptor_machine fd after.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn[descriptor_machine]in *;try exact I;try exact GOOD.
  all:try solve[eapply descriptor_process_step;eassumption].
  all:destruct GOOD as[CLOSED CONTROL];split;
    [match type of STEP with namespace_step _ _ ?first ?current ?last=>
      exact(closure_namespace_step descriptor_calls cell first current last descriptor_source_closure CLOSED STEP)end|
      exact(descriptor_external_return fd _ _ _ _ _ _ CONTROL)].
Qed.

Theorem descriptor_namespace_prefix fd cell before events after :
  descriptor_machine fd before ->namespace_steps caller_ge cell before events after ->
  descriptor_machine fd after.
Proof.
  intros GOOD RUN;revert GOOD;induction RUN;intro GOOD;[exact GOOD|].
  apply IHRUN;eapply descriptor_namespace_step;eassumption.
Qed.

Definition descriptor_io_event fd event : Prop := match event with
  |io_step q _|partial_loss q _ _=>operation q=writing ->descriptor q=fd
  |_=>True end.
Definition descriptor_library_event fd event := match event with
  |original_event event=>descriptor_io_event fd event|_=>True end.
Definition descriptor_entry_event fd event := match event with
  |entry_library event=>descriptor_library_event fd event|_=>True end.
Definition descriptor_process_event fd event := match event with
  |process_entry event=>descriptor_entry_event fd event|_=>True end.
Definition descriptor_namespace_event fd event := match event with
  |namespace_process event=>descriptor_process_event fd event|_=>True end.

Lemma descriptor_io_boundary fd cell state q : descriptor_control fd state ->boundary cell state q ->
  operation q=writing ->descriptor q=fd.
Proof.
  intros CONTROL BOUNDARY WRITING;inversion BOUNDARY;subst.
  destruct CONTROL as[ARGS[CALL CONT]].
  unfold descriptor_arguments in ARGS;rewrite WRITING in ARGS.
  destruct(ARGS eq_refl)as[rest VALUES];inversion VALUES;reflexivity.
Qed.

Lemma descriptor_original_event fd cell before event after :
  descriptor_machine fd before ->Machine.step caller_ge cell before event after ->descriptor_io_event fd event.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn[descriptor_io_event];try exact I.
  all:intro WRITING;eapply descriptor_io_boundary;[exact(proj2 GOOD)|eassumption|exact WRITING].
Qed.
Lemma descriptor_library_event_checked fd cell before event after :
  descriptor_machine fd before ->library_step caller_ge cell before event after ->descriptor_library_event fd event.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn[descriptor_library_event];try exact I.
  eapply descriptor_original_event;eassumption.
Qed.
Lemma descriptor_entry_event_checked fd cell before event after :
  descriptor_machine fd before ->entry_handoff_step caller_ge cell before event after ->descriptor_entry_event fd event.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn[descriptor_entry_event];try exact I.
  eapply descriptor_library_event_checked;eassumption.
Qed.
Lemma descriptor_process_event_checked fd cell before event after :
  descriptor_machine fd before ->process_step caller_ge cell before event after ->descriptor_process_event fd event.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn[descriptor_process_event];try exact I.
  eapply descriptor_entry_event_checked;eassumption.
Qed.
Lemma descriptor_namespace_event_checked fd cell before event after :
  descriptor_machine fd before ->namespace_step caller_ge cell before event after ->descriptor_namespace_event fd event.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn[descriptor_namespace_event];try exact I.
  eapply descriptor_process_event_checked;eassumption.
Qed.

Theorem descriptor_actual_namespace_writes fd cell before events after :
  descriptor_machine fd before ->namespace_steps caller_ge cell before events after ->
  Forall(descriptor_namespace_event fd)events.
Proof.
  intros GOOD RUN;revert GOOD;induction RUN;intro GOOD;constructor.
  - eapply descriptor_namespace_event_checked;eassumption.
  - apply IHRUN;eapply descriptor_namespace_step;eassumption.
Qed.

Theorem descriptor_initial fd fn arguments memory :
  closure_function descriptor_calls(Internal fn) ->descriptor_arguments fd(Internal fn)arguments ->
  descriptor_machine fd(live(Callstate(Internal fn)arguments Kstop memory)).
Proof.
  intros FUNCTION ARGUMENTS;split.
  - split.
    + split;[destruct FUNCTION as[id[MEMBER LOOKUP]];eapply descriptor_lookup_global;exact LOOKUP|exact I].
    + split;[exact FUNCTION|exact I].
  - split;[exact ARGUMENTS|split;exact I].
Qed.

Theorem actual_sender_namespace_write_descriptors cell fd sequence result memory events after :
  namespace_steps caller_ge cell
    (live(Callstate(Internal f_send_frame)[Vint fd;Vlong sequence;result]Kstop memory))events after ->
  Forall(descriptor_namespace_event fd)events.
Proof.
  intro RUN;eapply descriptor_actual_namespace_writes;[|exact RUN].
  apply descriptor_initial;[exact descriptor_sender_binding|].
  intro REQUIRED;eexists;reflexivity.
Qed.

Theorem actual_write_all_namespace_write_descriptors cell fd data count memory events after :
  namespace_steps caller_ge cell
    (live(Callstate(Internal f_write_all)[Vint fd;data;count]Kstop memory))events after ->
  Forall(descriptor_namespace_event fd)events.
Proof.
  intro RUN;eapply descriptor_actual_namespace_writes;[|exact RUN].
  apply descriptor_initial;[exact descriptor_write_all_binding|].
  intro REQUIRED;eexists;reflexivity.
Qed.
