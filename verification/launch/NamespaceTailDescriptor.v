(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.origin: Tail reporting preserves its immutable caller and callee descriptor slots. *)
From Stdlib Require Import ZArith List Bool String.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs
  Ctypes Ctypesdefs Cop Clight.
Require Import IO Machine LibraryMachine.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessControl ProcessGlobalCalls ProcessCaller.
From EntryNamespace Require Import NamespaceMachine NamespaceClosure NamespaceStructure NamespacePaths NamespaceCaller.
From EntryProcess Require Import ProcessDescriptor.
Import ListNotations.

Definition tail_descriptor_calls :=
  [_waitpid;_entry_ptrace4;_send_frame;_result_of;_get32;_kill;_read;_close;_fault;_usleep;__exit;
   _put32;_put64;_write_all;_write;_error_number;___errno_location;_memcpy;_strcmp].
Definition tail_descriptor_mode fn := match fn_params fn with
  |(id,_)::rest=>if Pos.eqb id _fd then Some _fd else
    match rest with (id,_)::_=>if Pos.eqb id _report then Some _report else None|[]=>None end
  |[]=>None end.
Definition tail_descriptor_required definition :=match definition with
  |Internal fn=>match tail_descriptor_mode fn with Some id=>Pos.eqb id _fd|None=>false end
  |External(EF_external name _)_ _ _=>String.eqb name "write"|_=>false end.
Definition tail_descriptor_report definition :=match definition with
  |Internal fn=>match tail_descriptor_mode fn with Some id=>Pos.eqb id _report|None=>false end
  |_=>false end.
Definition tail_descriptor_signature definition := match type_of_fundef definition with
  | Tfunction (Tint I32 Signed _::_) _ _=>true|_=>false end.
Definition tail_descriptor_first mode arguments:=match mode,arguments with
  |Some wanted,Etempvar id(Tint I32 Signed _)::_=>Pos.eqb id wanted|_,_=>false end.
Definition tail_descriptor_sensitive id:=Pos.eqb id _send_frame||Pos.eqb id _write_all||Pos.eqb id _write.
Definition tail_descriptor_call mode expression arguments:=match expression with
  |Evar id(Tfunction _ _ _)=>if Pos.eqb id _namespace_init then false else
    if tail_descriptor_sensitive id then tail_descriptor_first mode arguments else true
  |_=>false end.
Definition tail_descriptor_opt option:=match option with
  |Some id=>negb(Pos.eqb id _fd||Pos.eqb id _report)|None=>true end.
Fixpoint tail_descriptor_immutable body := match body with
  | Sset id _=>negb(Pos.eqb id _fd||Pos.eqb id _report)
  | Scall opt _ _=>tail_descriptor_opt opt
  | Ssequence first rest|Sifthenelse _ first rest|Sloop first rest=>
      tail_descriptor_immutable first&&tail_descriptor_immutable rest
  | Slabel _ body=>tail_descriptor_immutable body
  | Sgoto _=>true
  | Sbuiltin _ _ _ _|Sswitch _ _=>false
  |_=>true end.
Definition tail_descriptor_function fn :=
  tail_descriptor_immutable (fn_body fn)=true /\
  checked_statement (tail_descriptor_call (tail_descriptor_mode fn)) (fn_body fn)=true.
Definition tail_descriptor_profile := forallb (fun id=>match closure_lookup id with
  |Some definition=>
    Bool.eqb(tail_descriptor_required definition)(tail_descriptor_sensitive id)&&
    Bool.eqb(tail_descriptor_report definition)(Pos.eqb id _namespace_init)&&
    (if tail_descriptor_required definition then tail_descriptor_signature definition else true)&&
    match definition with
    |Internal fn=>tail_descriptor_immutable(fn_body fn)&&
      checked_statement(tail_descriptor_call(tail_descriptor_mode fn))(fn_body fn)
    |_=>true end
  |None=>false end)tail_descriptor_calls.

Theorem tail_descriptor_source_profile : tail_descriptor_profile=true.
Proof. vm_compute;reflexivity. Qed.
Theorem tail_descriptor_source_closure : closure_profile tail_descriptor_calls=true.
Proof. vm_compute;reflexivity. Qed.

Local Opaque EntrySource.prog caller_ge.

Lemma tail_descriptor_lookup_actual id block definition :
  Genv.find_symbol caller_ge id=Some block ->
  Genv.find_funct caller_ge(Vptr block Ptrofs.zero)=Some definition ->
  closure_lookup id=Some definition.
Proof. intros SYMBOL FOUND;unfold closure_lookup;rewrite SYMBOL;exact FOUND. Qed.

Lemma tail_descriptor_lookup_global id fn : closure_lookup id=Some(Internal fn) ->
  caller_vars_safe fn=true.
Proof.
  unfold closure_lookup;destruct(Genv.find_symbol caller_ge id)as[block|]eqn:SYMBOL;[|discriminate].
  intro FOUND;exact(proj1(caller_function_source _ _ FOUND)).
Qed.

Local Opaque closure_lookup tail_descriptor_calls.

Lemma tail_descriptor_function_checked fn : closure_function tail_descriptor_calls (Internal fn) ->
  tail_descriptor_function fn.
Proof.
  intros [id[MEMBER LOOKUP]];pose proof tail_descriptor_source_profile as PROFILE.
  unfold tail_descriptor_profile in PROFILE;apply forallb_forall with(x:=id)in PROFILE;[|exact MEMBER].
  rewrite LOOKUP in PROFILE;cbn -[tail_descriptor_required tail_descriptor_mode tail_descriptor_signature tail_descriptor_sensitive tail_descriptor_immutable checked_statement] in PROFILE;repeat rewrite andb_true_iff in PROFILE;unfold tail_descriptor_function;tauto.
Qed.

Lemma tail_descriptor_function_signature definition : closure_function tail_descriptor_calls definition ->
  tail_descriptor_required definition=true ->tail_descriptor_signature definition=true.
Proof.
  intros [id[MEMBER LOOKUP]] REQUIRED;pose proof tail_descriptor_source_profile as PROFILE.
  unfold tail_descriptor_profile in PROFILE;apply forallb_forall with(x:=id)in PROFILE;[|exact MEMBER].
  rewrite LOOKUP,REQUIRED in PROFILE;repeat rewrite andb_true_iff in PROFILE;tauto.
Qed.

Definition tail_descriptor_temp fd fn le:=match tail_descriptor_mode fn with
  |Some id=>le!id=Some(Vint fd)|None=>True end.
Definition tail_descriptor_arguments fd definition arguments:=
  (tail_descriptor_required definition=true->exists rest,arguments=Vint fd::rest) /\
  (tail_descriptor_report definition=true->exists first rest,arguments=first::Vint fd::rest).
Fixpoint tail_descriptor_cont fd mode continuation : Prop := match continuation with
  |Kstop=>True
  |Kseq body rest=>tail_descriptor_immutable body=true /\
    checked_statement(tail_descriptor_call mode)body=true /\tail_descriptor_cont fd mode rest
  |Kloop1 first second rest|Kloop2 first second rest=>
    tail_descriptor_immutable first=true /\tail_descriptor_immutable second=true /\
    checked_statement(tail_descriptor_call mode)first=true /\
    checked_statement(tail_descriptor_call mode)second=true /\tail_descriptor_cont fd mode rest
  |Kswitch _=>False
  |Kcall opt caller _ le rest=>tail_descriptor_function caller /\tail_descriptor_temp fd caller le /\
    tail_descriptor_opt opt=true /\tail_descriptor_cont fd (tail_descriptor_mode caller) rest
  end.
Definition tail_descriptor_control fd state : Prop := match state with
  |State fn body k _ le _=>tail_descriptor_function fn /\tail_descriptor_immutable body=true /\
    checked_statement(tail_descriptor_call(tail_descriptor_mode fn))body=true /\
    tail_descriptor_temp fd fn le /\tail_descriptor_cont fd (tail_descriptor_mode fn)k
  |Callstate definition arguments k _=>tail_descriptor_arguments fd definition arguments /\
    is_call_cont k /\tail_descriptor_cont fd None k
  |Returnstate _ k _=>is_call_cont k /\tail_descriptor_cont fd None k
  end.
Definition tail_descriptor_state fd state:=closure_state tail_descriptor_calls state /\tail_descriptor_control fd state.
Definition tail_descriptor_machine fd state:=match state with live source=>tail_descriptor_state fd source|dead _=>True end.

Lemma tail_descriptor_call_cont fd mode target k : tail_descriptor_cont fd mode k ->
  tail_descriptor_cont fd target (call_cont k).
Proof. induction k;cbn;intuition. Qed.

Lemma tail_descriptor_cont_call_mode fd mode target k : is_call_cont k ->
  tail_descriptor_cont fd mode k ->tail_descriptor_cont fd target k.
Proof. destruct k;cbn;intuition. Qed.

Lemma tail_descriptor_call_cont_is_call k : is_call_cont(call_cont k).
Proof. induction k;cbn;auto. Qed.

Lemma tail_descriptor_mode_range fn id:tail_descriptor_mode fn=Some id->id=_fd\/id=_report.
Proof.
  unfold tail_descriptor_mode;destruct(fn_params fn)as[|[first ty]rest];[discriminate|].
  destruct(Pos.eqb first _fd);[intros SAME;inversion SAME;auto|].
  destruct rest as[|[second ty']rest];[discriminate|].
  destruct(Pos.eqb second _report);intros SAME;inversion SAME;auto.
Qed.
Lemma tail_descriptor_temp_set fd fn le id value:
  tail_descriptor_temp fd fn le->id<>_fd->id<>_report->
  tail_descriptor_temp fd fn(PTree.set id value le).
Proof.
  unfold tail_descriptor_temp;intros TEMP FD CG.
  destruct(tail_descriptor_mode fn)as[wanted|]eqn:MODE;[|exact I].
  rewrite PTree.gso;[exact TEMP|]. destruct(tail_descriptor_mode_range _ _ MODE);congruence.
Qed.
Lemma tail_descriptor_temp_optional fd fn le opt value:
  tail_descriptor_temp fd fn le->tail_descriptor_opt opt=true->
  tail_descriptor_temp fd fn(set_opttemp opt value le).
Proof.
  intros TEMP OPTIONAL;destruct opt as[id|];[|exact TEMP].
  unfold tail_descriptor_opt in OPTIONAL;apply negb_true_iff,orb_false_iff in OPTIONAL as[FD CG].
  apply Pos.eqb_neq in FD,CG;apply tail_descriptor_temp_set;assumption.
Qed.
Lemma tail_descriptor_bind_other protected formals arguments before after:
  ~In protected(map fst formals)->bind_parameter_temps formals arguments before=Some after->after!protected=before!protected.
Proof.
  revert arguments before after;induction formals as[|[id ty]rest IH];
    intros arguments before after ABSENT BIND;destruct arguments;cbn in BIND;try discriminate.
  - inversion BIND;reflexivity.
  - rewrite(IH _ _ _ ltac:(cbn in ABSENT;intuition)BIND).
    rewrite PTree.gso;[reflexivity|];cbn in ABSENT;intuition.
Qed.
Lemma tail_descriptor_function_entry fd fn args before e le after:
  tail_descriptor_arguments fd(Internal fn)args->
  function_entry2 caller_ge fn args before e le after->tail_descriptor_temp fd fn le.
Proof.
  intros[FIRST SECOND]ENTRY;inversion ENTRY as[VARS NAMES DISJOINT ALLOC BIND];subst.
  unfold tail_descriptor_temp,tail_descriptor_mode.
  destruct(fn_params fn)as[|[id ty]rest]eqn:PARAMS;[exact I|].
  destruct(Pos.eqb id _fd)eqn:FD.
  - apply Pos.eqb_eq in FD;subst id.
    assert(REQUIRED:tail_descriptor_required(Internal fn)=true).
    { unfold tail_descriptor_required,tail_descriptor_mode;rewrite PARAMS;reflexivity. }
    destruct(FIRST REQUIRED)as[remaining VALUES];subst args.
    assert(ABSENT:~In _fd(map fst rest)).
    { unfold var_names in NAMES;try rewrite PARAMS in NAMES;inversion NAMES;assumption. }
    try rewrite PARAMS in BIND;cbn in BIND.
    rewrite(tail_descriptor_bind_other _fd rest remaining _ _ ABSENT BIND);apply PTree.gss.
  - destruct rest as[|[second ty']remaining]eqn:REST;[exact I|].
    destruct(Pos.eqb second _report)eqn:CG;[|exact I].
    apply Pos.eqb_eq in CG;subst second.
    assert(REQUIRED:tail_descriptor_report(Internal fn)=true).
    { unfold tail_descriptor_report,tail_descriptor_mode;rewrite PARAMS,FD;reflexivity. }
    destruct(SECOND REQUIRED)as[first[values VALUES]];subst args.
    assert(ABSENT:~In _report(map fst remaining)).
    { unfold var_names in NAMES;try rewrite PARAMS in NAMES;inversion NAMES;subst;
        match goal with N:list_norepet(_::_)|-_=>inversion N;assumption end. }
    try rewrite PARAMS in BIND;cbn in BIND.
    rewrite(tail_descriptor_bind_other _report remaining values _ _ ABSENT BIND);apply PTree.gss.
Qed.

Lemma tail_descriptor_first_shape protected arguments : tail_descriptor_first(Some protected)arguments=true ->
  exists attr rest,arguments=Etempvar protected(Tint I32 Signed attr)::rest.
Proof.
  destruct arguments as[|argument rest];[discriminate|].
  destruct argument;cbn[tail_descriptor_first];try discriminate.
  destruct t;try discriminate.
  match goal with size:intsize|-_=>destruct size end;try discriminate.
  match goal with sign:signedness|-_=>destruct sign end;try discriminate.
  intro IDENTIFIER;apply Pos.eqb_eq in IDENTIFIER;subst;eauto.
Qed.

Lemma tail_descriptor_signature_shape definition : tail_descriptor_signature definition=true ->
  exists attr rest result cc,type_of_fundef definition=Tfunction(Tint I32 Signed attr::rest)result cc.
Proof.
  unfold tail_descriptor_signature;destruct(type_of_fundef definition);try discriminate.
  destruct l as[|first rest];[discriminate|].
  destruct first;try discriminate.
  match goal with size:intsize|-_=>destruct size end;try discriminate.
  match goal with sign:signedness|-_=>destruct sign end;try discriminate.
  intros;do 4 eexists;reflexivity.
Qed.

Lemma tail_descriptor_argument_values ge e le memory fd protected expressions attr types values :
  le!protected=Some(Vint fd) ->tail_descriptor_first(Some protected)expressions=true ->
  eval_exprlist ge e le memory expressions(Tint I32 Signed attr::types)values ->
  exists rest,values=Vint fd::rest.
Proof.
  intros REGISTER FIRST ARGUMENTS.
  destruct(tail_descriptor_first_shape protected _ FIRST)as[actual[rest SHAPE]];subst expressions.
  inversion ARGUMENTS;subst.
  match goal with VALUE:eval_expr _ _ _ _ (Etempvar protected _) _|-_=>inversion VALUE;subst end.
  match goal with LOOKUP:le!protected=Some ?value|-_=>
    assert(value=Vint fd)by congruence;subst value end.
  match goal with CAST:sem_cast _ _ _ _=Some _|-_=>cbn[sem_cast classify_cast]in CAST;inversion CAST;subst end.
  eexists;reflexivity.
  all:match goal with LOCATION:eval_lvalue _ _ _ _ (Etempvar _ _) _ _ _|-_=>inversion LOCATION end.
Qed.

Lemma tail_descriptor_allowed mode id formal result convention expressions:
  tail_descriptor_call mode(Evar id(Tfunction formal result convention))expressions=true ->
  Pos.eqb id _namespace_init=false /\
    (tail_descriptor_sensitive id=true->tail_descriptor_first mode expressions=true).
Proof.
  unfold tail_descriptor_call;destruct(Pos.eqb id _namespace_init);[discriminate|].
  destruct(tail_descriptor_sensitive id);intuition discriminate.
Qed.
Lemma tail_descriptor_first_mode mode expressions:
  tail_descriptor_first mode expressions=true->exists protected,mode=Some protected.
Proof. destruct mode;[eauto|destruct expressions;discriminate]. Qed.

Lemma tail_descriptor_actual_call fd fn e le memory expression expressions types result cc pointer values definition:
  caller_env_global e->closure_call tail_descriptor_calls expression=true->
  tail_descriptor_call(tail_descriptor_mode fn)expression expressions=true->tail_descriptor_temp fd fn le->
  eval_expr caller_ge e le memory expression pointer->eval_exprlist caller_ge e le memory expressions types values->
  Genv.find_funct caller_ge pointer=Some definition->type_of_fundef definition=Tfunction types result cc->
  tail_descriptor_arguments fd definition values.
Proof.
  intros GLOBAL CLOSED ALLOWED REGISTER FUNCTION ARGUMENTS FOUND TYPE.
  destruct(closure_call_shape _ _ CLOSED)as[id[formal[result_type[convention[EXPRESSION[MEMBER IDENTIFIER]]]]]];subst expression.
  destruct(caller_global_function_value _ _ _ _ _ _ _ _ GLOBAL IDENTIFIER FUNCTION)
    as[block[SYMBOL POINTER]];subst pointer.
  assert(LOOKUP:closure_lookup id=Some definition)by(eapply tail_descriptor_lookup_actual;eassumption).
  assert(CALLEE:closure_function tail_descriptor_calls definition)by(exists id;auto).
  pose proof tail_descriptor_source_profile as PROFILE.
  unfold tail_descriptor_profile in PROFILE;apply forallb_forall with(x:=id)in PROFILE;[|exact MEMBER].
  rewrite LOOKUP in PROFILE;repeat rewrite andb_true_iff in PROFILE.
  destruct(tail_descriptor_allowed _ _ _ _ _ _ ALLOWED)as[NONRECURSIVE FIRST].
  unfold tail_descriptor_arguments;split.
  - intro REQUIRED.
    pose proof(tail_descriptor_function_signature _ CALLEE REQUIRED)as SIGNATURE.
    destruct(tail_descriptor_signature_shape _ SIGNATURE)as[attr[rest[returned[cconv SIGNED]]]].
    rewrite TYPE in SIGNED;inversion SIGNED;subst types returned cconv.
    assert(SENSITIVE:tail_descriptor_sensitive id=true).
    { rewrite REQUIRED in PROFILE;destruct(tail_descriptor_sensitive id);cbn in PROFILE;tauto. }
    pose proof(FIRST SENSITIVE)as FIRST_ARGUMENT.
    destruct(tail_descriptor_first_mode _ _ FIRST_ARGUMENT)as[protected MODE].
    rewrite MODE in FIRST_ARGUMENT.
    unfold tail_descriptor_temp in REGISTER;rewrite MODE in REGISTER.
    eapply tail_descriptor_argument_values;eassumption.
  - intro CGROUP.
    assert(CHECK:Bool.eqb(tail_descriptor_report definition)(Pos.eqb id _namespace_init)=true)by tauto.
    rewrite CGROUP,NONRECURSIVE in CHECK;discriminate.
Qed.

Theorem tail_descriptor_source_step fd before trace after :
  tail_descriptor_state fd before ->step2 caller_ge before trace after ->tail_descriptor_state fd after.
Proof.
  intros [CLOSED CONTROL] STEP;split.
  - eapply closure_source_step;[exact tail_descriptor_source_closure|exact CLOSED|exact STEP].
  - inversion STEP;subst;
      cbn[tail_descriptor_control tail_descriptor_immutable tail_descriptor_cont checked_statement]in *;
      repeat rewrite andb_true_iff in *;try solve[intuition discriminate].
    all:try solve[exfalso;destruct CLOSED as[GLOBAL[BODY CONT]];change(false=true)in BODY;discriminate].
    + destruct CONTROL as[FUNCTION[IMMUTABLE[CALLS[REGISTER CONT]]]].
      refine(conj FUNCTION(conj eq_refl(conj eq_refl(conj _ CONT)))).
      apply tail_descriptor_temp_set;[exact REGISTER| |].
      all:apply negb_true_iff,orb_false_iff in IMMUTABLE as[FD CG];
        apply Pos.eqb_neq in FD,CG;assumption.
    + destruct CONTROL as[FUNCTION[IMMUTABLE[CALLS[REGISTER CONT]]]].
      destruct CLOSED as[[ENV GLOBAL_CONT][CALL CLOSED_CONT]].
      split.
      * eapply tail_descriptor_actual_call;eassumption.
      * split;[exact I|]. cbn;exact(conj FUNCTION(conj REGISTER(conj IMMUTABLE CONT))).
    + destruct b;cbn;tauto.
    + destruct CONTROL as[FUNCTION[IMMUTABLE[CALLS[REGISTER CONT]]]].
      split;[apply tail_descriptor_call_cont_is_call|].
      exact(tail_descriptor_call_cont fd(tail_descriptor_mode f)None k CONT).
    + destruct CONTROL as[FUNCTION[IMMUTABLE[CALLS[REGISTER CONT]]]].
      split;[apply tail_descriptor_call_cont_is_call|].
      exact(tail_descriptor_call_cont fd(tail_descriptor_mode f)None k CONT).
    + destruct CONTROL as[FUNCTION[IMMUTABLE[CALLS[REGISTER CONT]]]].
      split;[assumption|]. eapply tail_descriptor_cont_call_mode;[assumption|exact CONT].
    + destruct CONTROL as[ARGUMENTS[CALL CONT]].
      destruct CLOSED as[GLOBAL[FUNCTION CLOSED_CONT]].
      pose proof(tail_descriptor_function_checked _ FUNCTION)as CHECKED.
      assert(CONT':tail_descriptor_cont fd(tail_descriptor_mode f)k).
      { eapply tail_descriptor_cont_call_mode;[exact CALL|exact CONT]. }
      refine(conj CHECKED(conj(proj1 CHECKED)(conj(proj2 CHECKED)(conj _ CONT')))).
      eapply tail_descriptor_function_entry;eassumption.
    + destruct CONTROL as[CALL CONT].
      destruct CONT as[FUNCTION[REGISTER[OPTIONAL CONT]]].
      refine(conj FUNCTION(conj eq_refl(conj eq_refl(conj _ CONT)))).
      eapply tail_descriptor_temp_optional;eassumption.
Qed.

Lemma tail_descriptor_external_return fd definition args k before value after :
  tail_descriptor_control fd(Callstate definition args k before) ->
  tail_descriptor_control fd(Returnstate value k after).
Proof.
  intros[ARGS[CALL CONT]];split;[exact CALL|].
  eapply tail_descriptor_cont_call_mode;eassumption.
Qed.

Lemma tail_descriptor_original_step fd cell before event after :
  tail_descriptor_machine fd before ->Machine.step caller_ge cell before event after ->
  tail_descriptor_machine fd after.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn[tail_descriptor_machine]in *;try exact I;try exact GOOD.
  all:try solve[eapply tail_descriptor_source_step;eassumption].
  all:destruct GOOD as[CLOSED CONTROL];split;
    [match type of STEP with Machine.step _ _ ?first ?current ?last=>
      exact(closure_original_step tail_descriptor_calls cell first current last tail_descriptor_source_closure CLOSED STEP)end|
      exact(tail_descriptor_external_return fd _ _ _ _ _ _ CONTROL)].
Qed.

Lemma tail_descriptor_library_step fd cell before event after :
  tail_descriptor_machine fd before ->library_step caller_ge cell before event after ->
  tail_descriptor_machine fd after.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn[tail_descriptor_machine]in *;try exact I;try exact GOOD.
  all:try solve[eapply tail_descriptor_original_step;eassumption].
  all:destruct GOOD as[CLOSED CONTROL];split;
    [match type of STEP with library_step _ _ ?first ?current ?last=>
      exact(closure_library_step tail_descriptor_calls cell first current last tail_descriptor_source_closure CLOSED STEP)end|
      exact(tail_descriptor_external_return fd _ _ _ _ _ _ CONTROL)].
Qed.

Lemma tail_descriptor_entry_step fd cell before event after :
  tail_descriptor_machine fd before ->entry_handoff_step caller_ge cell before event after ->
  tail_descriptor_machine fd after.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn[tail_descriptor_machine]in *;try exact I;try exact GOOD.
  all:try solve[eapply tail_descriptor_library_step;eassumption].
  all:destruct GOOD as[CLOSED CONTROL];split;
    [match type of STEP with entry_handoff_step _ _ ?first ?current ?last=>
      exact(closure_entry_step tail_descriptor_calls cell first current last tail_descriptor_source_closure CLOSED STEP)end|
      exact(tail_descriptor_external_return fd _ _ _ _ _ _ CONTROL)].
Qed.

Lemma tail_descriptor_process_step fd cell before event after :
  tail_descriptor_machine fd before ->process_step caller_ge cell before event after ->
  tail_descriptor_machine fd after.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn[tail_descriptor_machine]in *;try exact I;try exact GOOD.
  all:try solve[eapply tail_descriptor_entry_step;eassumption].
  all:destruct GOOD as[CLOSED CONTROL];split;
    [match type of STEP with process_step _ _ ?first ?current ?last=>
      exact(closure_process_step tail_descriptor_calls cell first current last tail_descriptor_source_closure CLOSED STEP)end|
      exact(tail_descriptor_external_return fd _ _ _ _ _ _ CONTROL)].
Qed.

Theorem tail_descriptor_namespace_step fd cell before event after :
  tail_descriptor_machine fd before ->namespace_step caller_ge cell before event after ->
  tail_descriptor_machine fd after.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn[tail_descriptor_machine]in *;try exact I;try exact GOOD.
  all:try solve[eapply tail_descriptor_process_step;eassumption].
  all:destruct GOOD as[CLOSED CONTROL];split;
    [match type of STEP with namespace_step _ _ ?first ?current ?last=>
      exact(closure_namespace_step tail_descriptor_calls cell first current last tail_descriptor_source_closure CLOSED STEP)end|
      exact(tail_descriptor_external_return fd _ _ _ _ _ _ CONTROL)].
Qed.

Theorem tail_descriptor_namespace_prefix fd cell before events after :
  tail_descriptor_machine fd before ->namespace_steps caller_ge cell before events after ->
  tail_descriptor_machine fd after.
Proof.
  intros GOOD RUN;revert GOOD;induction RUN;intro GOOD;[exact GOOD|].
  apply IHRUN;eapply tail_descriptor_namespace_step;eassumption.
Qed.

Definition tail_descriptor_io_event fd event : Prop := match event with
  |io_step q _|partial_loss q _ _=>operation q=writing ->descriptor q=fd
  |_=>True end.
Definition tail_descriptor_library_event fd event := match event with
  |original_event event=>tail_descriptor_io_event fd event|_=>True end.
Definition tail_descriptor_entry_event fd event := match event with
  |entry_library event=>tail_descriptor_library_event fd event|_=>True end.
Definition tail_descriptor_process_event fd event := match event with
  |process_entry event=>tail_descriptor_entry_event fd event|_=>True end.
Definition tail_descriptor_namespace_event fd event := match event with
  |namespace_process event=>tail_descriptor_process_event fd event|_=>True end.

Lemma tail_descriptor_io_boundary fd cell state q : tail_descriptor_control fd state ->boundary cell state q ->
  operation q=writing ->descriptor q=fd.
Proof.
  intros CONTROL BOUNDARY WRITING;inversion BOUNDARY;subst.
  destruct CONTROL as[ARGS[CALL CONT]].
  destruct ARGS as[ARGS CGROUP];unfold tail_descriptor_required in ARGS;rewrite WRITING in ARGS.
  destruct(ARGS eq_refl)as[rest VALUES];inversion VALUES;reflexivity.
Qed.

Lemma tail_descriptor_original_event fd cell before event after :
  tail_descriptor_machine fd before ->Machine.step caller_ge cell before event after ->tail_descriptor_io_event fd event.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn[tail_descriptor_io_event];try exact I.
  all:intro WRITING;eapply tail_descriptor_io_boundary;[exact(proj2 GOOD)|eassumption|exact WRITING].
Qed.
Lemma tail_descriptor_library_event_checked fd cell before event after :
  tail_descriptor_machine fd before ->library_step caller_ge cell before event after ->tail_descriptor_library_event fd event.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn[tail_descriptor_library_event];try exact I.
  eapply tail_descriptor_original_event;eassumption.
Qed.
Lemma tail_descriptor_entry_event_checked fd cell before event after :
  tail_descriptor_machine fd before ->entry_handoff_step caller_ge cell before event after ->tail_descriptor_entry_event fd event.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn[tail_descriptor_entry_event];try exact I.
  eapply tail_descriptor_library_event_checked;eassumption.
Qed.
Lemma tail_descriptor_process_event_checked fd cell before event after :
  tail_descriptor_machine fd before ->process_step caller_ge cell before event after ->tail_descriptor_process_event fd event.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn[tail_descriptor_process_event];try exact I.
  eapply tail_descriptor_entry_event_checked;eassumption.
Qed.
Lemma tail_descriptor_namespace_event_checked fd cell before event after :
  tail_descriptor_machine fd before ->namespace_step caller_ge cell before event after ->tail_descriptor_namespace_event fd event.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn[tail_descriptor_namespace_event];try exact I.
  eapply tail_descriptor_process_event_checked;eassumption.
Qed.

Theorem tail_descriptor_actual_namespace_writes fd cell before events after :
  tail_descriptor_machine fd before ->namespace_steps caller_ge cell before events after ->
  Forall(tail_descriptor_namespace_event fd)events.
Proof.
  intros GOOD RUN;revert GOOD;induction RUN;intro GOOD;constructor.
  - eapply tail_descriptor_namespace_event_checked;eassumption.
  - apply IHRUN;eapply tail_descriptor_namespace_step;eassumption.
Qed.

Theorem tail_descriptor_initial fd fn arguments memory :
  closure_function tail_descriptor_calls(Internal fn) ->tail_descriptor_arguments fd(Internal fn)arguments ->
  tail_descriptor_machine fd(live(Callstate(Internal fn)arguments Kstop memory)).
Proof.
  intros FUNCTION ARGUMENTS;split.
  - split.
    + split;[destruct FUNCTION as[id[MEMBER LOOKUP]];eapply tail_descriptor_lookup_global;exact LOOKUP|exact I].
    + split;[exact FUNCTION|exact I].
  - split;[exact ARGUMENTS|split;exact I].
Qed.

Theorem namespace_report_variable_checked:tail_descriptor_function f_namespace_init.
Proof. split;vm_compute;reflexivity. Qed.

Theorem namespace_tail_report_checked:
  tail_descriptor_immutable(namespace_tail 31)=true /\
  checked_statement(tail_descriptor_call(tail_descriptor_mode f_namespace_init))(namespace_tail 31)=true /\
  closure_statement tail_descriptor_calls(namespace_tail 31)=true.
Proof. repeat split;vm_compute;reflexivity. Qed.

Theorem actual_namespace_tail_report_descriptors cell e le memory report events target:
  caller_env_global e ->le!_report=Some(Vint report) ->
  namespace_steps caller_ge cell(live(State f_namespace_init(namespace_tail 31)Kstop e le memory))events target ->
  Forall(descriptor_namespace_event report)events.
Proof.
  intros GLOBAL REPORT RUN;change(Forall(tail_descriptor_namespace_event report)events).
  eapply tail_descriptor_actual_namespace_writes;[|exact RUN].
  destruct namespace_tail_report_checked as[IMMUTABLE[CALLS CLOSED]].
  split.
  - split;[split;[exact GLOBAL|exact I]|split;[exact CLOSED|exact I]].
  - refine(conj namespace_report_variable_checked(conj IMMUTABLE(conj CALLS(conj _ I)))).
    change(le!_report=Some(Vint report));exact REPORT.
Qed.
