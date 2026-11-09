(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.origin: Guest and failure writes retain their actual failure socket across all source calls. *)
From Stdlib Require Import ZArith List Bool String.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs
  Ctypes Ctypesdefs Cop Clight.
Require Import IO Machine LibraryMachine.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffArguments NativeHandoffInput.
From EntryProcess Require Import ProcessMachine ProcessControl ProcessGlobalCalls ProcessCaller.
From EntryNamespace Require Import NamespaceMachine NamespaceClosure NamespaceStructure NamespacePaths NamespaceCaller.
From EntryProcess Require Import ProcessDescriptor.
Import ListNotations.

Definition guest_descriptor_calls :=
  [_guest;_strcmp;_fail_child;_entry_decimal;_error_number;_number;_entry_descriptor_flags;_execve;
   _put32;_fault;_write_all;_write;___errno_location;__exit;_memcpy].
Definition guest_descriptor_mode fn := match fn_params fn with
  |(id,_)::rest=>if Pos.eqb id _fd then Some _fd else
    match rest with _::_::(id,_)::_=>if Pos.eqb id _failure then Some _failure else None|_=>None end
  |[]=>None end.
Definition guest_descriptor_required definition :=match definition with
  |Internal fn=>match guest_descriptor_mode fn with Some id=>Pos.eqb id _fd|None=>false end
  |External(EF_external name _)_ _ _=>String.eqb name "write"|_=>false end.
Definition guest_descriptor_failure definition :=match definition with
  |Internal fn=>match guest_descriptor_mode fn with Some id=>Pos.eqb id _failure|None=>false end
  |_=>false end.
Definition guest_descriptor_signature definition := match type_of_fundef definition with
  | Tfunction (Tint I32 Signed _::_) _ _=>true|_=>false end.
Definition guest_descriptor_first mode arguments:=match mode,arguments with
  |Some wanted,Etempvar id(Tint I32 Signed _)::_=>Pos.eqb id wanted|_,_=>false end.
Definition guest_descriptor_sensitive id:=Pos.eqb id _fail_child||Pos.eqb id _write_all||Pos.eqb id _write.
Definition guest_descriptor_call mode expression arguments:=match expression with
  |Evar id(Tfunction _ _ _)=>if Pos.eqb id _guest then false else
    if guest_descriptor_sensitive id then guest_descriptor_first mode arguments else true
  |_=>false end.
Definition guest_descriptor_opt option:=match option with
  |Some id=>negb(Pos.eqb id _fd||Pos.eqb id _failure)|None=>true end.
Fixpoint guest_descriptor_immutable body := match body with
  | Sset id _=>negb(Pos.eqb id _fd||Pos.eqb id _failure)
  | Scall opt _ _=>guest_descriptor_opt opt
  | Ssequence first rest|Sifthenelse _ first rest|Sloop first rest=>
      guest_descriptor_immutable first&&guest_descriptor_immutable rest
  | Slabel _ body=>guest_descriptor_immutable body
  | Sgoto _=>true
  | Sbuiltin _ _ _ _|Sswitch _ _=>false
  |_=>true end.
Definition guest_descriptor_function fn :=
  guest_descriptor_immutable (fn_body fn)=true /\
  checked_statement (guest_descriptor_call (guest_descriptor_mode fn)) (fn_body fn)=true.
Definition guest_descriptor_profile := forallb (fun id=>match closure_lookup id with
  |Some definition=>
    Bool.eqb(guest_descriptor_required definition)(guest_descriptor_sensitive id)&&
    Bool.eqb(guest_descriptor_failure definition)(Pos.eqb id _guest)&&
    (if guest_descriptor_required definition then guest_descriptor_signature definition else true)&&
    match definition with
    |Internal fn=>guest_descriptor_immutable(fn_body fn)&&
      checked_statement(guest_descriptor_call(guest_descriptor_mode fn))(fn_body fn)
    |_=>true end
  |None=>false end)guest_descriptor_calls.

Theorem guest_descriptor_source_profile : guest_descriptor_profile=true.
Proof. vm_compute;reflexivity. Qed.
Theorem guest_descriptor_source_closure : closure_profile guest_descriptor_calls=true.
Proof. vm_compute;reflexivity. Qed.

Local Opaque EntrySource.prog caller_ge.

Lemma guest_descriptor_lookup_actual id block definition :
  Genv.find_symbol caller_ge id=Some block ->
  Genv.find_funct caller_ge(Vptr block Ptrofs.zero)=Some definition ->
  closure_lookup id=Some definition.
Proof. intros SYMBOL FOUND;unfold closure_lookup;rewrite SYMBOL;exact FOUND. Qed.

Lemma guest_descriptor_lookup_global id fn : closure_lookup id=Some(Internal fn) ->
  caller_vars_safe fn=true.
Proof.
  unfold closure_lookup;destruct(Genv.find_symbol caller_ge id)as[block|]eqn:SYMBOL;[|discriminate].
  intro FOUND;exact(proj1(caller_function_source _ _ FOUND)).
Qed.

Local Opaque closure_lookup guest_descriptor_calls.

Lemma guest_descriptor_function_checked fn : closure_function guest_descriptor_calls (Internal fn) ->
  guest_descriptor_function fn.
Proof.
  intros [id[MEMBER LOOKUP]];pose proof guest_descriptor_source_profile as PROFILE.
  unfold guest_descriptor_profile in PROFILE;apply forallb_forall with(x:=id)in PROFILE;[|exact MEMBER].
  rewrite LOOKUP in PROFILE;cbn -[guest_descriptor_required guest_descriptor_mode guest_descriptor_signature guest_descriptor_sensitive guest_descriptor_immutable checked_statement] in PROFILE;repeat rewrite andb_true_iff in PROFILE;unfold guest_descriptor_function;tauto.
Qed.

Lemma guest_descriptor_function_signature definition : closure_function guest_descriptor_calls definition ->
  guest_descriptor_required definition=true ->guest_descriptor_signature definition=true.
Proof.
  intros [id[MEMBER LOOKUP]] REQUIRED;pose proof guest_descriptor_source_profile as PROFILE.
  unfold guest_descriptor_profile in PROFILE;apply forallb_forall with(x:=id)in PROFILE;[|exact MEMBER].
  rewrite LOOKUP,REQUIRED in PROFILE;repeat rewrite andb_true_iff in PROFILE;tauto.
Qed.

Definition guest_descriptor_temp fd fn le:=match guest_descriptor_mode fn with
  |Some id=>le!id=Some(Vint fd)|None=>True end.
Definition guest_descriptor_arguments fd definition arguments:=
  (guest_descriptor_required definition=true->exists rest,arguments=Vint fd::rest) /\
  (guest_descriptor_failure definition=true->exists first second third rest,arguments=first::second::third::Vint fd::rest).
Fixpoint guest_descriptor_cont fd mode continuation : Prop := match continuation with
  |Kstop=>True
  |Kseq body rest=>guest_descriptor_immutable body=true /\
    checked_statement(guest_descriptor_call mode)body=true /\guest_descriptor_cont fd mode rest
  |Kloop1 first second rest|Kloop2 first second rest=>
    guest_descriptor_immutable first=true /\guest_descriptor_immutable second=true /\
    checked_statement(guest_descriptor_call mode)first=true /\
    checked_statement(guest_descriptor_call mode)second=true /\guest_descriptor_cont fd mode rest
  |Kswitch _=>False
  |Kcall opt caller _ le rest=>guest_descriptor_function caller /\guest_descriptor_temp fd caller le /\
    guest_descriptor_opt opt=true /\guest_descriptor_cont fd (guest_descriptor_mode caller) rest
  end.
Definition guest_descriptor_control fd state : Prop := match state with
  |State fn body k _ le _=>guest_descriptor_function fn /\guest_descriptor_immutable body=true /\
    checked_statement(guest_descriptor_call(guest_descriptor_mode fn))body=true /\
    guest_descriptor_temp fd fn le /\guest_descriptor_cont fd (guest_descriptor_mode fn)k
  |Callstate definition arguments k _=>guest_descriptor_arguments fd definition arguments /\
    is_call_cont k /\guest_descriptor_cont fd None k
  |Returnstate _ k _=>is_call_cont k /\guest_descriptor_cont fd None k
  end.
Definition guest_descriptor_state fd state:=closure_state guest_descriptor_calls state /\guest_descriptor_control fd state.
Definition guest_descriptor_machine fd state:=match state with live source=>guest_descriptor_state fd source|dead _=>True end.

Lemma guest_descriptor_call_cont fd mode target k : guest_descriptor_cont fd mode k ->
  guest_descriptor_cont fd target (call_cont k).
Proof. induction k;cbn;intuition. Qed.

Lemma guest_descriptor_cont_call_mode fd mode target k : is_call_cont k ->
  guest_descriptor_cont fd mode k ->guest_descriptor_cont fd target k.
Proof. destruct k;cbn;intuition. Qed.

Lemma guest_descriptor_call_cont_is_call k : is_call_cont(call_cont k).
Proof. induction k;cbn;auto. Qed.

Lemma guest_descriptor_mode_range fn id:guest_descriptor_mode fn=Some id->id=_fd\/id=_failure.
Proof.
  unfold guest_descriptor_mode;destruct(fn_params fn)as[|[first ty]rest];[discriminate|].
  destruct(Pos.eqb first _fd);[intros SAME;inversion SAME;auto|].
  destruct rest as[|[second ty2]rest];[discriminate|].
  destruct rest as[|[third ty3]rest];[discriminate|].
  destruct rest as[|[fourth ty4]rest];[discriminate|].
  destruct(Pos.eqb fourth _failure);intros SAME;inversion SAME;auto.
Qed.

Lemma guest_descriptor_temp_set fd fn le id value:
  guest_descriptor_temp fd fn le->id<>_fd->id<>_failure->
  guest_descriptor_temp fd fn(PTree.set id value le).
Proof.
  unfold guest_descriptor_temp;intros TEMP FD CG.
  destruct(guest_descriptor_mode fn)as[wanted|]eqn:MODE;[|exact I].
  rewrite PTree.gso;[exact TEMP|]. destruct(guest_descriptor_mode_range _ _ MODE);congruence.
Qed.
Lemma guest_descriptor_temp_optional fd fn le opt value:
  guest_descriptor_temp fd fn le->guest_descriptor_opt opt=true->
  guest_descriptor_temp fd fn(set_opttemp opt value le).
Proof.
  intros TEMP OPTIONAL;destruct opt as[id|];[|exact TEMP].
  unfold guest_descriptor_opt in OPTIONAL;apply negb_true_iff,orb_false_iff in OPTIONAL as[FD CG].
  apply Pos.eqb_neq in FD,CG;apply guest_descriptor_temp_set;assumption.
Qed.
Lemma guest_descriptor_bind_other protected formals arguments before after:
  ~In protected(map fst formals)->bind_parameter_temps formals arguments before=Some after->after!protected=before!protected.
Proof.
  revert arguments before after;induction formals as[|[id ty]rest IH];
    intros arguments before after ABSENT BIND;destruct arguments;cbn in BIND;try discriminate.
  - inversion BIND;reflexivity.
  - rewrite(IH _ _ _ ltac:(cbn in ABSENT;intuition)BIND).
    rewrite PTree.gso;[reflexivity|];cbn in ABSENT;intuition.
Qed.
Lemma guest_descriptor_function_entry fd fn args before e le after:
  guest_descriptor_arguments fd(Internal fn)args->
  function_entry2 caller_ge fn args before e le after->guest_descriptor_temp fd fn le.
Proof.
  intros[FIRST SECOND]ENTRY;inversion ENTRY as[VARS NAMES DISJOINT ALLOC BIND];subst.
  unfold guest_descriptor_temp,guest_descriptor_mode.
  destruct(fn_params fn)as[|[id ty]rest]eqn:PARAMS;[exact I|].
  destruct(Pos.eqb id _fd)eqn:FD.
  - apply Pos.eqb_eq in FD;subst id.
    assert(REQUIRED:guest_descriptor_required(Internal fn)=true).
    { unfold guest_descriptor_required,guest_descriptor_mode;rewrite PARAMS;reflexivity. }
    destruct(FIRST REQUIRED)as[remaining VALUES];subst args.
    assert(ABSENT:~In _fd(map fst rest)).
    { unfold var_names in NAMES;try rewrite PARAMS in NAMES;inversion NAMES;assumption. }
    try rewrite PARAMS in BIND;cbn in BIND.
    rewrite(guest_descriptor_bind_other _fd rest remaining _ _ ABSENT BIND);apply PTree.gss.
  - destruct rest as[|[second ty2]rest];[exact I|].
    destruct rest as[|[third ty3]rest];[exact I|].
    destruct rest as[|[fourth ty4]remaining];[exact I|].
    destruct(Pos.eqb fourth _failure)eqn:CG;[|exact I].
    apply Pos.eqb_eq in CG;subst fourth.
    assert(REQUIRED:guest_descriptor_failure(Internal fn)=true).
    { unfold guest_descriptor_failure,guest_descriptor_mode;rewrite PARAMS,FD;reflexivity. }
    destruct(SECOND REQUIRED)as[first[second_value[third_value[values VALUES]]]];subst args.
    assert(ABSENT:~In _failure(map fst remaining)).
    { unfold var_names in NAMES;try rewrite PARAMS in NAMES;cbn in NAMES.
      repeat match goal with N:list_norepet(_::_)|-_=>inversion N;subst;clear N end;assumption. }
    try rewrite PARAMS in BIND;cbn in BIND.
    rewrite(guest_descriptor_bind_other _failure remaining values _ _ ABSENT BIND);apply PTree.gss.
Qed.

Lemma guest_descriptor_first_shape protected arguments : guest_descriptor_first(Some protected)arguments=true ->
  exists attr rest,arguments=Etempvar protected(Tint I32 Signed attr)::rest.
Proof.
  destruct arguments as[|argument rest];[discriminate|].
  destruct argument;cbn[guest_descriptor_first];try discriminate.
  destruct t;try discriminate.
  match goal with size:intsize|-_=>destruct size end;try discriminate.
  match goal with sign:signedness|-_=>destruct sign end;try discriminate.
  intro IDENTIFIER;apply Pos.eqb_eq in IDENTIFIER;subst;eauto.
Qed.

Lemma guest_descriptor_signature_shape definition : guest_descriptor_signature definition=true ->
  exists attr rest result cc,type_of_fundef definition=Tfunction(Tint I32 Signed attr::rest)result cc.
Proof.
  unfold guest_descriptor_signature;destruct(type_of_fundef definition);try discriminate.
  destruct l as[|first rest];[discriminate|].
  destruct first;try discriminate.
  match goal with size:intsize|-_=>destruct size end;try discriminate.
  match goal with sign:signedness|-_=>destruct sign end;try discriminate.
  intros;do 4 eexists;reflexivity.
Qed.

Lemma guest_descriptor_argument_values ge e le memory fd protected expressions attr types values :
  le!protected=Some(Vint fd) ->guest_descriptor_first(Some protected)expressions=true ->
  eval_exprlist ge e le memory expressions(Tint I32 Signed attr::types)values ->
  exists rest,values=Vint fd::rest.
Proof.
  intros REGISTER FIRST ARGUMENTS.
  destruct(guest_descriptor_first_shape protected _ FIRST)as[actual[rest SHAPE]];subst expressions.
  inversion ARGUMENTS;subst.
  match goal with VALUE:eval_expr _ _ _ _ (Etempvar protected _) _|-_=>inversion VALUE;subst end.
  match goal with LOOKUP:le!protected=Some ?value|-_=>
    assert(value=Vint fd)by congruence;subst value end.
  match goal with CAST:sem_cast _ _ _ _=Some _|-_=>cbn[sem_cast classify_cast]in CAST;inversion CAST;subst end.
  eexists;reflexivity.
  all:match goal with LOCATION:eval_lvalue _ _ _ _ (Etempvar _ _) _ _ _|-_=>inversion LOCATION end.
Qed.

Lemma guest_descriptor_allowed mode id formal result convention expressions:
  guest_descriptor_call mode(Evar id(Tfunction formal result convention))expressions=true ->
  Pos.eqb id _guest=false /\
    (guest_descriptor_sensitive id=true->guest_descriptor_first mode expressions=true).
Proof.
  unfold guest_descriptor_call;destruct(Pos.eqb id _guest);[discriminate|].
  destruct(guest_descriptor_sensitive id);intuition discriminate.
Qed.
Lemma guest_descriptor_first_mode mode expressions:
  guest_descriptor_first mode expressions=true->exists protected,mode=Some protected.
Proof. destruct mode;[eauto|destruct expressions;discriminate]. Qed.

Lemma guest_descriptor_actual_call fd fn e le memory expression expressions types result cc pointer values definition:
  caller_env_global e->closure_call guest_descriptor_calls expression=true->
  guest_descriptor_call(guest_descriptor_mode fn)expression expressions=true->guest_descriptor_temp fd fn le->
  eval_expr caller_ge e le memory expression pointer->eval_exprlist caller_ge e le memory expressions types values->
  Genv.find_funct caller_ge pointer=Some definition->type_of_fundef definition=Tfunction types result cc->
  guest_descriptor_arguments fd definition values.
Proof.
  intros GLOBAL CLOSED ALLOWED REGISTER FUNCTION ARGUMENTS FOUND TYPE.
  destruct(closure_call_shape _ _ CLOSED)as[id[formal[result_type[convention[EXPRESSION[MEMBER IDENTIFIER]]]]]];subst expression.
  destruct(caller_global_function_value _ _ _ _ _ _ _ _ GLOBAL IDENTIFIER FUNCTION)
    as[block[SYMBOL POINTER]];subst pointer.
  assert(LOOKUP:closure_lookup id=Some definition)by(eapply guest_descriptor_lookup_actual;eassumption).
  assert(CALLEE:closure_function guest_descriptor_calls definition)by(exists id;auto).
  pose proof guest_descriptor_source_profile as PROFILE.
  unfold guest_descriptor_profile in PROFILE;apply forallb_forall with(x:=id)in PROFILE;[|exact MEMBER].
  rewrite LOOKUP in PROFILE;repeat rewrite andb_true_iff in PROFILE.
  destruct(guest_descriptor_allowed _ _ _ _ _ _ ALLOWED)as[NONRECURSIVE FIRST].
  unfold guest_descriptor_arguments;split.
  - intro REQUIRED.
    pose proof(guest_descriptor_function_signature _ CALLEE REQUIRED)as SIGNATURE.
    destruct(guest_descriptor_signature_shape _ SIGNATURE)as[attr[rest[returned[cconv SIGNED]]]].
    rewrite TYPE in SIGNED;inversion SIGNED;subst types returned cconv.
    assert(SENSITIVE:guest_descriptor_sensitive id=true).
    { rewrite REQUIRED in PROFILE;destruct(guest_descriptor_sensitive id);cbn in PROFILE;tauto. }
    pose proof(FIRST SENSITIVE)as FIRST_ARGUMENT.
    destruct(guest_descriptor_first_mode _ _ FIRST_ARGUMENT)as[protected MODE].
    rewrite MODE in FIRST_ARGUMENT.
    unfold guest_descriptor_temp in REGISTER;rewrite MODE in REGISTER.
    eapply guest_descriptor_argument_values;eassumption.
  - intro CGROUP.
    assert(CHECK:Bool.eqb(guest_descriptor_failure definition)(Pos.eqb id _guest)=true)by tauto.
    rewrite CGROUP,NONRECURSIVE in CHECK;discriminate.
Qed.

Theorem guest_descriptor_source_step fd before trace after :
  guest_descriptor_state fd before ->step2 caller_ge before trace after ->guest_descriptor_state fd after.
Proof.
  intros [CLOSED CONTROL] STEP;split.
  - eapply closure_source_step;[exact guest_descriptor_source_closure|exact CLOSED|exact STEP].
  - inversion STEP;subst;
      cbn[guest_descriptor_control guest_descriptor_immutable guest_descriptor_cont checked_statement]in *;
      repeat rewrite andb_true_iff in *;try solve[intuition discriminate].
    all:try solve[exfalso;destruct CLOSED as[GLOBAL[BODY CONT]];change(false=true)in BODY;discriminate].
    + destruct CONTROL as[FUNCTION[IMMUTABLE[CALLS[REGISTER CONT]]]].
      refine(conj FUNCTION(conj eq_refl(conj eq_refl(conj _ CONT)))).
      apply guest_descriptor_temp_set;[exact REGISTER| |].
      all:apply negb_true_iff,orb_false_iff in IMMUTABLE as[FD CG];
        apply Pos.eqb_neq in FD,CG;assumption.
    + destruct CONTROL as[FUNCTION[IMMUTABLE[CALLS[REGISTER CONT]]]].
      destruct CLOSED as[[ENV GLOBAL_CONT][CALL CLOSED_CONT]].
      split.
      * eapply guest_descriptor_actual_call;eassumption.
      * split;[exact I|]. cbn;exact(conj FUNCTION(conj REGISTER(conj IMMUTABLE CONT))).
    + destruct b;cbn;tauto.
    + destruct CONTROL as[FUNCTION[IMMUTABLE[CALLS[REGISTER CONT]]]].
      split;[apply guest_descriptor_call_cont_is_call|].
      exact(guest_descriptor_call_cont fd(guest_descriptor_mode f)None k CONT).
    + destruct CONTROL as[FUNCTION[IMMUTABLE[CALLS[REGISTER CONT]]]].
      split;[apply guest_descriptor_call_cont_is_call|].
      exact(guest_descriptor_call_cont fd(guest_descriptor_mode f)None k CONT).
    + destruct CONTROL as[FUNCTION[IMMUTABLE[CALLS[REGISTER CONT]]]].
      split;[assumption|]. eapply guest_descriptor_cont_call_mode;[assumption|exact CONT].
    + destruct CONTROL as[ARGUMENTS[CALL CONT]].
      destruct CLOSED as[GLOBAL[FUNCTION CLOSED_CONT]].
      pose proof(guest_descriptor_function_checked _ FUNCTION)as CHECKED.
      assert(CONT':guest_descriptor_cont fd(guest_descriptor_mode f)k).
      { eapply guest_descriptor_cont_call_mode;[exact CALL|exact CONT]. }
      refine(conj CHECKED(conj(proj1 CHECKED)(conj(proj2 CHECKED)(conj _ CONT')))).
      eapply guest_descriptor_function_entry;eassumption.
    + destruct CONTROL as[CALL CONT].
      destruct CONT as[FUNCTION[REGISTER[OPTIONAL CONT]]].
      refine(conj FUNCTION(conj eq_refl(conj eq_refl(conj _ CONT)))).
      eapply guest_descriptor_temp_optional;eassumption.
Qed.

Lemma guest_descriptor_external_return fd definition args k before value after :
  guest_descriptor_control fd(Callstate definition args k before) ->
  guest_descriptor_control fd(Returnstate value k after).
Proof.
  intros[ARGS[CALL CONT]];split;[exact CALL|].
  eapply guest_descriptor_cont_call_mode;eassumption.
Qed.

Lemma guest_descriptor_original_step fd cell before event after :
  guest_descriptor_machine fd before ->Machine.step caller_ge cell before event after ->
  guest_descriptor_machine fd after.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn[guest_descriptor_machine]in *;try exact I;try exact GOOD.
  all:try solve[eapply guest_descriptor_source_step;eassumption].
  all:destruct GOOD as[CLOSED CONTROL];split;
    [match type of STEP with Machine.step _ _ ?first ?current ?last=>
      exact(closure_original_step guest_descriptor_calls cell first current last guest_descriptor_source_closure CLOSED STEP)end|
      exact(guest_descriptor_external_return fd _ _ _ _ _ _ CONTROL)].
Qed.

Lemma guest_descriptor_library_step fd cell before event after :
  guest_descriptor_machine fd before ->library_step caller_ge cell before event after ->
  guest_descriptor_machine fd after.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn[guest_descriptor_machine]in *;try exact I;try exact GOOD.
  all:try solve[eapply guest_descriptor_original_step;eassumption].
  all:destruct GOOD as[CLOSED CONTROL];split;
    [match type of STEP with library_step _ _ ?first ?current ?last=>
      exact(closure_library_step guest_descriptor_calls cell first current last guest_descriptor_source_closure CLOSED STEP)end|
      exact(guest_descriptor_external_return fd _ _ _ _ _ _ CONTROL)].
Qed.

Lemma guest_descriptor_entry_step fd cell before event after :
  guest_descriptor_machine fd before ->entry_handoff_step caller_ge cell before event after ->
  guest_descriptor_machine fd after.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn[guest_descriptor_machine]in *;try exact I;try exact GOOD.
  all:try solve[eapply guest_descriptor_library_step;eassumption].
  all:destruct GOOD as[CLOSED CONTROL];split;
    [match type of STEP with entry_handoff_step _ _ ?first ?current ?last=>
      exact(closure_entry_step guest_descriptor_calls cell first current last guest_descriptor_source_closure CLOSED STEP)end|
      exact(guest_descriptor_external_return fd _ _ _ _ _ _ CONTROL)].
Qed.

Lemma guest_descriptor_process_step fd cell before event after :
  guest_descriptor_machine fd before ->process_step caller_ge cell before event after ->
  guest_descriptor_machine fd after.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn[guest_descriptor_machine]in *;try exact I;try exact GOOD.
  all:try solve[eapply guest_descriptor_entry_step;eassumption].
  all:destruct GOOD as[CLOSED CONTROL];split;
    [match type of STEP with process_step _ _ ?first ?current ?last=>
      exact(closure_process_step guest_descriptor_calls cell first current last guest_descriptor_source_closure CLOSED STEP)end|
      exact(guest_descriptor_external_return fd _ _ _ _ _ _ CONTROL)].
Qed.

Theorem guest_descriptor_namespace_step fd cell before event after :
  guest_descriptor_machine fd before ->namespace_step caller_ge cell before event after ->
  guest_descriptor_machine fd after.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn[guest_descriptor_machine]in *;try exact I;try exact GOOD.
  all:try solve[eapply guest_descriptor_process_step;eassumption].
  all:destruct GOOD as[CLOSED CONTROL];split;
    [match type of STEP with namespace_step _ _ ?first ?current ?last=>
      exact(closure_namespace_step guest_descriptor_calls cell first current last guest_descriptor_source_closure CLOSED STEP)end|
      exact(guest_descriptor_external_return fd _ _ _ _ _ _ CONTROL)].
Qed.

Theorem guest_descriptor_namespace_prefix fd cell before events after :
  guest_descriptor_machine fd before ->namespace_steps caller_ge cell before events after ->
  guest_descriptor_machine fd after.
Proof.
  intros GOOD RUN;revert GOOD;induction RUN;intro GOOD;[exact GOOD|].
  apply IHRUN;eapply guest_descriptor_namespace_step;eassumption.
Qed.

Definition guest_descriptor_io_event fd event : Prop := match event with
  |io_step q _|partial_loss q _ _=>operation q=writing ->descriptor q=fd
  |_=>True end.
Definition guest_descriptor_library_event fd event := match event with
  |original_event event=>guest_descriptor_io_event fd event|_=>True end.
Definition guest_descriptor_entry_event fd event := match event with
  |entry_library event=>guest_descriptor_library_event fd event|_=>True end.
Definition guest_descriptor_process_event fd event := match event with
  |process_entry event=>guest_descriptor_entry_event fd event|_=>True end.
Definition guest_descriptor_namespace_event fd event := match event with
  |namespace_process event=>guest_descriptor_process_event fd event|_=>True end.

Lemma guest_descriptor_io_boundary fd cell state q : guest_descriptor_control fd state ->boundary cell state q ->
  operation q=writing ->descriptor q=fd.
Proof.
  intros CONTROL BOUNDARY WRITING;inversion BOUNDARY;subst.
  destruct CONTROL as[ARGS[CALL CONT]].
  destruct ARGS as[ARGS CGROUP];unfold guest_descriptor_required in ARGS;rewrite WRITING in ARGS.
  destruct(ARGS eq_refl)as[rest VALUES];inversion VALUES;reflexivity.
Qed.

Lemma guest_descriptor_original_event fd cell before event after :
  guest_descriptor_machine fd before ->Machine.step caller_ge cell before event after ->guest_descriptor_io_event fd event.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn[guest_descriptor_io_event];try exact I.
  all:intro WRITING;eapply guest_descriptor_io_boundary;[exact(proj2 GOOD)|eassumption|exact WRITING].
Qed.
Lemma guest_descriptor_library_event_checked fd cell before event after :
  guest_descriptor_machine fd before ->library_step caller_ge cell before event after ->guest_descriptor_library_event fd event.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn[guest_descriptor_library_event];try exact I.
  eapply guest_descriptor_original_event;eassumption.
Qed.
Lemma guest_descriptor_entry_event_checked fd cell before event after :
  guest_descriptor_machine fd before ->entry_handoff_step caller_ge cell before event after ->guest_descriptor_entry_event fd event.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn[guest_descriptor_entry_event];try exact I.
  eapply guest_descriptor_library_event_checked;eassumption.
Qed.
Lemma guest_descriptor_process_event_checked fd cell before event after :
  guest_descriptor_machine fd before ->process_step caller_ge cell before event after ->guest_descriptor_process_event fd event.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn[guest_descriptor_process_event];try exact I.
  eapply guest_descriptor_entry_event_checked;eassumption.
Qed.
Lemma guest_descriptor_namespace_event_checked fd cell before event after :
  guest_descriptor_machine fd before ->namespace_step caller_ge cell before event after ->guest_descriptor_namespace_event fd event.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn[guest_descriptor_namespace_event];try exact I.
  eapply guest_descriptor_process_event_checked;eassumption.
Qed.

Theorem guest_descriptor_actual_namespace_writes fd cell before events after :
  guest_descriptor_machine fd before ->namespace_steps caller_ge cell before events after ->
  Forall(guest_descriptor_namespace_event fd)events.
Proof.
  intros GOOD RUN;revert GOOD;induction RUN;intro GOOD;constructor.
  - eapply guest_descriptor_namespace_event_checked;eassumption.
  - apply IHRUN;eapply guest_descriptor_namespace_step;eassumption.
Qed.

Theorem guest_descriptor_initial fd fn arguments memory :
  closure_function guest_descriptor_calls(Internal fn) ->guest_descriptor_arguments fd(Internal fn)arguments ->
  guest_descriptor_machine fd(live(Callstate(Internal fn)arguments Kstop memory)).
Proof.
  intros FUNCTION ARGUMENTS;split.
  - split.
    + split;[destruct FUNCTION as[id[MEMBER LOOKUP]];eapply guest_descriptor_lookup_global;exact LOOKUP|exact I].
    + split;[exact FUNCTION|exact I].
  - split;[exact ARGUMENTS|split;exact I].
Qed.

Theorem actual_namespace_guest_write_descriptors cell input output errors failure memory events after:
  namespace_steps caller_ge cell
    (live(Callstate(Internal f_guest)[Vint input;Vint output;Vint errors;Vint failure]Kstop memory))events after ->
  Forall(descriptor_namespace_event failure)events.
Proof.
  intro RUN;change(Forall(guest_descriptor_namespace_event failure)events).
  eapply guest_descriptor_actual_namespace_writes;[|exact RUN].
  apply guest_descriptor_initial.
  - exists _guest;split;[left;reflexivity|vm_compute;reflexivity].
  - split;[intro REQUIRED;discriminate REQUIRED|].
    intro REQUIRED;exists(Vint input),(Vint output),(Vint errors),[];reflexivity.
Qed.

From EntryNamespace Require Import NamespaceGuest NamespaceEntry NamespaceContexts.
Require Import CallContexts LibraryControl.

Lemma namespace_stopped_return_no_entry_progress ge cell value k memory event target:
  k=Kstop ->entry_handoff_step ge cell(live(Returnstate value k memory))event target ->
  ~namespace_entry_progress event.
Proof.
  intros SAME STEP PROGRESS;subst k;inversion STEP;subst;try discriminate.
  match goal with L:library_step _ _ _ _ _|-_=>inversion L;subst;try discriminate end.
  match goal with M:Machine.step _ _ _ _ _|-_=>inversion M;subst;try discriminate end.
  all:try match goal with S:step2 _ (Returnstate _ Kstop _) _ _|-_=>inversion S end.
  all:unfold namespace_entry_progress,control_progress,control_wait in PROGRESS;cbn in PROGRESS;intuition discriminate.
Qed.

Theorem actual_namespace_guest_never_returns cell input memory input_fd output_fd errors_fd failure events returned after:
  NativeHandoffInput.handoff_borrowed_input cell memory input ->
  ~namespace_steps handoff_ge cell
    (live(Callstate(Internal f_guest)[Vint input_fd;Vint output_fd;Vint errors_fd;Vint failure]Kstop memory))events
    (live(Returnstate returned Kstop after)).
Proof.
  intros INPUT RUN.
  destruct(actual_namespace_guest_projects _ _ _ _ _ _ _ _ _ _ INPUT RUN)as[actual[EVENTS REAL]].
  destruct(namespace_guest_is_entry_defined _ _ _ _ _ _ _ _ INPUT actual(Returnstate returned Kstop after)REAL)
    as[event[target[PROGRESS STEP]]].
  eapply namespace_stopped_return_no_entry_progress;[reflexivity|exact STEP|exact PROGRESS].
Qed.

Theorem actual_namespace_guest_caller_write_descriptors cell input memory input_fd output_fd errors_fd failure k events target:
  NativeHandoffInput.handoff_borrowed_input cell memory input ->is_call_cont k ->
  namespace_steps handoff_ge cell
    (live(Callstate(Internal f_guest)[Vint input_fd;Vint output_fd;Vint errors_fd;Vint failure]k memory))events target ->
  Forall(descriptor_namespace_event failure)events.
Proof.
  intros INPUT CALL RUN.
  destruct(namespace_caller_run_decomposition handoff_ge cell k
    (Callstate(Internal f_guest)[Vint input_fd;Vint output_fd;Vint errors_fd;Vint failure]Kstop memory)events target CALL RUN)
    as[[local[LOCAL SAME]]|[prefix[rest[returned[after[EVENTS[LOCAL CONTINUE]]]]]]].
  - eapply actual_namespace_guest_write_descriptors;exact LOCAL.
  - exfalso;eapply actual_namespace_guest_never_returns;[exact INPUT|exact LOCAL].
Qed.
