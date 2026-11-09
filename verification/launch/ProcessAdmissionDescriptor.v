(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.origin: Admission writes retain the actual scalar cgroup descriptor. *)
From Stdlib Require Import ZArith List Bool String.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs
  Ctypes Ctypesdefs Cop Clight.
Require Import IO Machine LibraryMachine.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessControl ProcessGlobalCalls ProcessCaller.
From EntryNamespace Require Import NamespaceMachine NamespaceClosure.
From EntryProcess Require Import ProcessDescriptor.
Import ListNotations.

Definition admission_descriptor_calls := [_admit_child;_number;_write_all;_error_number;_waitpid;_entry_ptrace4;_entry_decimal;_write;___errno_location].
Definition admission_descriptor_mode fn := match fn_params fn with
  |(id,_)::rest=>if Pos.eqb id _fd then Some _fd else
    match rest with (id,_)::_=>if Pos.eqb id _cgfd then Some _cgfd else None|[]=>None end
  |[]=>None end.
Definition admission_descriptor_required definition :=match definition with
  |Internal fn=>match admission_descriptor_mode fn with Some id=>Pos.eqb id _fd|None=>false end
  |External(EF_external name _)_ _ _=>String.eqb name "write"|_=>false end.
Definition admission_descriptor_cgroup definition :=match definition with
  |Internal fn=>match admission_descriptor_mode fn with Some id=>Pos.eqb id _cgfd|None=>false end
  |_=>false end.
Definition admission_descriptor_signature definition := match type_of_fundef definition with
  | Tfunction (Tint I32 Signed _::_) _ _=>true|_=>false end.
Definition admission_descriptor_first mode arguments:=match mode,arguments with
  |Some wanted,Etempvar id(Tint I32 Signed _)::_=>Pos.eqb id wanted|_,_=>false end.
Definition admission_descriptor_sensitive id:=Pos.eqb id _write_all||Pos.eqb id _write.
Definition admission_descriptor_call mode expression arguments:=match expression with
  |Evar id(Tfunction _ _ _)=>if Pos.eqb id _admit_child then false else
    if admission_descriptor_sensitive id then admission_descriptor_first mode arguments else true
  |_=>false end.
Definition admission_descriptor_opt option:=match option with
  |Some id=>negb(Pos.eqb id _fd||Pos.eqb id _cgfd)|None=>true end.
Fixpoint admission_descriptor_immutable body := match body with
  | Sset id _=>negb(Pos.eqb id _fd||Pos.eqb id _cgfd)
  | Scall opt _ _=>admission_descriptor_opt opt
  | Ssequence first rest|Sifthenelse _ first rest|Sloop first rest=>
      admission_descriptor_immutable first&&admission_descriptor_immutable rest
  | Sbuiltin _ _ _ _|Sgoto _|Sswitch _ _|Slabel _ _=>false
  |_=>true end.
Definition admission_descriptor_function fn :=
  admission_descriptor_immutable (fn_body fn)=true /\
  checked_statement (admission_descriptor_call (admission_descriptor_mode fn)) (fn_body fn)=true.
Definition admission_descriptor_profile := forallb (fun id=>match closure_lookup id with
  |Some definition=>
    Bool.eqb(admission_descriptor_required definition)(admission_descriptor_sensitive id)&&
    Bool.eqb(admission_descriptor_cgroup definition)(Pos.eqb id _admit_child)&&
    (if admission_descriptor_required definition then admission_descriptor_signature definition else true)&&
    match definition with
    |Internal fn=>admission_descriptor_immutable(fn_body fn)&&
      checked_statement(admission_descriptor_call(admission_descriptor_mode fn))(fn_body fn)
    |_=>true end
  |None=>false end)admission_descriptor_calls.

Theorem admission_descriptor_source_profile : admission_descriptor_profile=true.
Proof. vm_compute;reflexivity. Qed.
Theorem admission_descriptor_source_closure : closure_profile admission_descriptor_calls=true.
Proof. vm_compute;reflexivity. Qed.

Theorem admission_descriptor_admit_binding:closure_function admission_descriptor_calls(Internal f_admit_child).
Proof. exists _admit_child;split;[left;reflexivity|vm_compute;reflexivity]. Qed.

Local Opaque EntrySource.prog caller_ge.

Lemma admission_descriptor_lookup_actual id block definition :
  Genv.find_symbol caller_ge id=Some block ->
  Genv.find_funct caller_ge(Vptr block Ptrofs.zero)=Some definition ->
  closure_lookup id=Some definition.
Proof. intros SYMBOL FOUND;unfold closure_lookup;rewrite SYMBOL;exact FOUND. Qed.

Lemma admission_descriptor_lookup_global id fn : closure_lookup id=Some(Internal fn) ->
  caller_vars_safe fn=true.
Proof.
  unfold closure_lookup;destruct(Genv.find_symbol caller_ge id)as[block|]eqn:SYMBOL;[|discriminate].
  intro FOUND;exact(proj1(caller_function_source _ _ FOUND)).
Qed.

Local Opaque closure_lookup admission_descriptor_calls.

Lemma admission_descriptor_function_checked fn : closure_function admission_descriptor_calls (Internal fn) ->
  admission_descriptor_function fn.
Proof.
  intros [id[MEMBER LOOKUP]];pose proof admission_descriptor_source_profile as PROFILE.
  unfold admission_descriptor_profile in PROFILE;apply forallb_forall with(x:=id)in PROFILE;[|exact MEMBER].
  rewrite LOOKUP in PROFILE;cbn -[admission_descriptor_required admission_descriptor_mode admission_descriptor_signature admission_descriptor_sensitive admission_descriptor_immutable checked_statement] in PROFILE;repeat rewrite andb_true_iff in PROFILE;unfold admission_descriptor_function;tauto.
Qed.

Lemma admission_descriptor_function_signature definition : closure_function admission_descriptor_calls definition ->
  admission_descriptor_required definition=true ->admission_descriptor_signature definition=true.
Proof.
  intros [id[MEMBER LOOKUP]] REQUIRED;pose proof admission_descriptor_source_profile as PROFILE.
  unfold admission_descriptor_profile in PROFILE;apply forallb_forall with(x:=id)in PROFILE;[|exact MEMBER].
  rewrite LOOKUP,REQUIRED in PROFILE;repeat rewrite andb_true_iff in PROFILE;tauto.
Qed.

Definition admission_descriptor_temp fd fn le:=match admission_descriptor_mode fn with
  |Some id=>le!id=Some(Vint fd)|None=>True end.
Definition admission_descriptor_arguments fd definition arguments:=
  (admission_descriptor_required definition=true->exists rest,arguments=Vint fd::rest) /\
  (admission_descriptor_cgroup definition=true->exists first rest,arguments=first::Vint fd::rest).
Fixpoint admission_descriptor_cont fd mode continuation : Prop := match continuation with
  |Kstop=>True
  |Kseq body rest=>admission_descriptor_immutable body=true /\
    checked_statement(admission_descriptor_call mode)body=true /\admission_descriptor_cont fd mode rest
  |Kloop1 first second rest|Kloop2 first second rest=>
    admission_descriptor_immutable first=true /\admission_descriptor_immutable second=true /\
    checked_statement(admission_descriptor_call mode)first=true /\
    checked_statement(admission_descriptor_call mode)second=true /\admission_descriptor_cont fd mode rest
  |Kswitch _=>False
  |Kcall opt caller _ le rest=>admission_descriptor_function caller /\admission_descriptor_temp fd caller le /\
    admission_descriptor_opt opt=true /\admission_descriptor_cont fd (admission_descriptor_mode caller) rest
  end.
Definition admission_descriptor_control fd state : Prop := match state with
  |State fn body k _ le _=>admission_descriptor_function fn /\admission_descriptor_immutable body=true /\
    checked_statement(admission_descriptor_call(admission_descriptor_mode fn))body=true /\
    admission_descriptor_temp fd fn le /\admission_descriptor_cont fd (admission_descriptor_mode fn)k
  |Callstate definition arguments k _=>admission_descriptor_arguments fd definition arguments /\
    is_call_cont k /\admission_descriptor_cont fd None k
  |Returnstate _ k _=>is_call_cont k /\admission_descriptor_cont fd None k
  end.
Definition admission_descriptor_state fd state:=closure_state admission_descriptor_calls state /\admission_descriptor_control fd state.
Definition admission_descriptor_machine fd state:=match state with live source=>admission_descriptor_state fd source|dead _=>True end.

Lemma admission_descriptor_call_cont fd mode target k : admission_descriptor_cont fd mode k ->
  admission_descriptor_cont fd target (call_cont k).
Proof. induction k;cbn;intuition. Qed.

Lemma admission_descriptor_cont_call_mode fd mode target k : is_call_cont k ->
  admission_descriptor_cont fd mode k ->admission_descriptor_cont fd target k.
Proof. destruct k;cbn;intuition. Qed.

Lemma admission_descriptor_call_cont_is_call k : is_call_cont(call_cont k).
Proof. induction k;cbn;auto. Qed.

Lemma admission_descriptor_mode_range fn id:admission_descriptor_mode fn=Some id->id=_fd\/id=_cgfd.
Proof.
  unfold admission_descriptor_mode;destruct(fn_params fn)as[|[first ty]rest];[discriminate|].
  destruct(Pos.eqb first _fd);[intros SAME;inversion SAME;auto|].
  destruct rest as[|[second ty']rest];[discriminate|].
  destruct(Pos.eqb second _cgfd);intros SAME;inversion SAME;auto.
Qed.
Lemma admission_descriptor_temp_set fd fn le id value:
  admission_descriptor_temp fd fn le->id<>_fd->id<>_cgfd->
  admission_descriptor_temp fd fn(PTree.set id value le).
Proof.
  unfold admission_descriptor_temp;intros TEMP FD CG.
  destruct(admission_descriptor_mode fn)as[wanted|]eqn:MODE;[|exact I].
  rewrite PTree.gso;[exact TEMP|]. destruct(admission_descriptor_mode_range _ _ MODE);congruence.
Qed.
Lemma admission_descriptor_temp_optional fd fn le opt value:
  admission_descriptor_temp fd fn le->admission_descriptor_opt opt=true->
  admission_descriptor_temp fd fn(set_opttemp opt value le).
Proof.
  intros TEMP OPTIONAL;destruct opt as[id|];[|exact TEMP].
  unfold admission_descriptor_opt in OPTIONAL;apply negb_true_iff,orb_false_iff in OPTIONAL as[FD CG].
  apply Pos.eqb_neq in FD,CG;apply admission_descriptor_temp_set;assumption.
Qed.
Lemma admission_descriptor_bind_other protected formals arguments before after:
  ~In protected(map fst formals)->bind_parameter_temps formals arguments before=Some after->after!protected=before!protected.
Proof.
  revert arguments before after;induction formals as[|[id ty]rest IH];
    intros arguments before after ABSENT BIND;destruct arguments;cbn in BIND;try discriminate.
  - inversion BIND;reflexivity.
  - rewrite(IH _ _ _ ltac:(cbn in ABSENT;intuition)BIND).
    rewrite PTree.gso;[reflexivity|];cbn in ABSENT;intuition.
Qed.
Lemma admission_descriptor_function_entry fd fn args before e le after:
  admission_descriptor_arguments fd(Internal fn)args->
  function_entry2 caller_ge fn args before e le after->admission_descriptor_temp fd fn le.
Proof.
  intros[FIRST SECOND]ENTRY;inversion ENTRY as[VARS NAMES DISJOINT ALLOC BIND];subst.
  unfold admission_descriptor_temp,admission_descriptor_mode.
  destruct(fn_params fn)as[|[id ty]rest]eqn:PARAMS;[exact I|].
  destruct(Pos.eqb id _fd)eqn:FD.
  - apply Pos.eqb_eq in FD;subst id.
    assert(REQUIRED:admission_descriptor_required(Internal fn)=true).
    { unfold admission_descriptor_required,admission_descriptor_mode;rewrite PARAMS;reflexivity. }
    destruct(FIRST REQUIRED)as[remaining VALUES];subst args.
    assert(ABSENT:~In _fd(map fst rest)).
    { unfold var_names in NAMES;try rewrite PARAMS in NAMES;inversion NAMES;assumption. }
    try rewrite PARAMS in BIND;cbn in BIND.
    rewrite(admission_descriptor_bind_other _fd rest remaining _ _ ABSENT BIND);apply PTree.gss.
  - destruct rest as[|[second ty']remaining]eqn:REST;[exact I|].
    destruct(Pos.eqb second _cgfd)eqn:CG;[|exact I].
    apply Pos.eqb_eq in CG;subst second.
    assert(REQUIRED:admission_descriptor_cgroup(Internal fn)=true).
    { unfold admission_descriptor_cgroup,admission_descriptor_mode;rewrite PARAMS,FD;reflexivity. }
    destruct(SECOND REQUIRED)as[first[values VALUES]];subst args.
    assert(ABSENT:~In _cgfd(map fst remaining)).
    { unfold var_names in NAMES;try rewrite PARAMS in NAMES;inversion NAMES;subst;
        match goal with N:list_norepet(_::_)|-_=>inversion N;assumption end. }
    try rewrite PARAMS in BIND;cbn in BIND.
    rewrite(admission_descriptor_bind_other _cgfd remaining values _ _ ABSENT BIND);apply PTree.gss.
Qed.

Lemma admission_descriptor_first_shape protected arguments : admission_descriptor_first(Some protected)arguments=true ->
  exists attr rest,arguments=Etempvar protected(Tint I32 Signed attr)::rest.
Proof.
  destruct arguments as[|argument rest];[discriminate|].
  destruct argument;cbn[admission_descriptor_first];try discriminate.
  destruct t;try discriminate.
  match goal with size:intsize|-_=>destruct size end;try discriminate.
  match goal with sign:signedness|-_=>destruct sign end;try discriminate.
  intro IDENTIFIER;apply Pos.eqb_eq in IDENTIFIER;subst;eauto.
Qed.

Lemma admission_descriptor_signature_shape definition : admission_descriptor_signature definition=true ->
  exists attr rest result cc,type_of_fundef definition=Tfunction(Tint I32 Signed attr::rest)result cc.
Proof.
  unfold admission_descriptor_signature;destruct(type_of_fundef definition);try discriminate.
  destruct l as[|first rest];[discriminate|].
  destruct first;try discriminate.
  match goal with size:intsize|-_=>destruct size end;try discriminate.
  match goal with sign:signedness|-_=>destruct sign end;try discriminate.
  intros;do 4 eexists;reflexivity.
Qed.

Lemma admission_descriptor_argument_values ge e le memory fd protected expressions attr types values :
  le!protected=Some(Vint fd) ->admission_descriptor_first(Some protected)expressions=true ->
  eval_exprlist ge e le memory expressions(Tint I32 Signed attr::types)values ->
  exists rest,values=Vint fd::rest.
Proof.
  intros REGISTER FIRST ARGUMENTS.
  destruct(admission_descriptor_first_shape protected _ FIRST)as[actual[rest SHAPE]];subst expressions.
  inversion ARGUMENTS;subst.
  match goal with VALUE:eval_expr _ _ _ _ (Etempvar protected _) _|-_=>inversion VALUE;subst end.
  match goal with LOOKUP:le!protected=Some ?value|-_=>
    assert(value=Vint fd)by congruence;subst value end.
  match goal with CAST:sem_cast _ _ _ _=Some _|-_=>cbn[sem_cast classify_cast]in CAST;inversion CAST;subst end.
  eexists;reflexivity.
  all:match goal with LOCATION:eval_lvalue _ _ _ _ (Etempvar _ _) _ _ _|-_=>inversion LOCATION end.
Qed.

Lemma admission_descriptor_allowed mode id formal result convention expressions:
  admission_descriptor_call mode(Evar id(Tfunction formal result convention))expressions=true ->
  Pos.eqb id _admit_child=false /\
    (admission_descriptor_sensitive id=true->admission_descriptor_first mode expressions=true).
Proof.
  unfold admission_descriptor_call;destruct(Pos.eqb id _admit_child);[discriminate|].
  destruct(admission_descriptor_sensitive id);intuition discriminate.
Qed.
Lemma admission_descriptor_first_mode mode expressions:
  admission_descriptor_first mode expressions=true->exists protected,mode=Some protected.
Proof. destruct mode;[eauto|destruct expressions;discriminate]. Qed.

Lemma admission_descriptor_actual_call fd fn e le memory expression expressions types result cc pointer values definition:
  caller_env_global e->closure_call admission_descriptor_calls expression=true->
  admission_descriptor_call(admission_descriptor_mode fn)expression expressions=true->admission_descriptor_temp fd fn le->
  eval_expr caller_ge e le memory expression pointer->eval_exprlist caller_ge e le memory expressions types values->
  Genv.find_funct caller_ge pointer=Some definition->type_of_fundef definition=Tfunction types result cc->
  admission_descriptor_arguments fd definition values.
Proof.
  intros GLOBAL CLOSED ALLOWED REGISTER FUNCTION ARGUMENTS FOUND TYPE.
  destruct(closure_call_shape _ _ CLOSED)as[id[formal[result_type[convention[EXPRESSION[MEMBER IDENTIFIER]]]]]];subst expression.
  destruct(caller_global_function_value _ _ _ _ _ _ _ _ GLOBAL IDENTIFIER FUNCTION)
    as[block[SYMBOL POINTER]];subst pointer.
  assert(LOOKUP:closure_lookup id=Some definition)by(eapply admission_descriptor_lookup_actual;eassumption).
  assert(CALLEE:closure_function admission_descriptor_calls definition)by(exists id;auto).
  pose proof admission_descriptor_source_profile as PROFILE.
  unfold admission_descriptor_profile in PROFILE;apply forallb_forall with(x:=id)in PROFILE;[|exact MEMBER].
  rewrite LOOKUP in PROFILE;repeat rewrite andb_true_iff in PROFILE.
  destruct(admission_descriptor_allowed _ _ _ _ _ _ ALLOWED)as[NONRECURSIVE FIRST].
  unfold admission_descriptor_arguments;split.
  - intro REQUIRED.
    pose proof(admission_descriptor_function_signature _ CALLEE REQUIRED)as SIGNATURE.
    destruct(admission_descriptor_signature_shape _ SIGNATURE)as[attr[rest[returned[cconv SIGNED]]]].
    rewrite TYPE in SIGNED;inversion SIGNED;subst types returned cconv.
    assert(SENSITIVE:admission_descriptor_sensitive id=true).
    { rewrite REQUIRED in PROFILE;destruct(admission_descriptor_sensitive id);cbn in PROFILE;tauto. }
    pose proof(FIRST SENSITIVE)as FIRST_ARGUMENT.
    destruct(admission_descriptor_first_mode _ _ FIRST_ARGUMENT)as[protected MODE].
    rewrite MODE in FIRST_ARGUMENT.
    unfold admission_descriptor_temp in REGISTER;rewrite MODE in REGISTER.
    eapply admission_descriptor_argument_values;eassumption.
  - intro CGROUP.
    assert(CHECK:Bool.eqb(admission_descriptor_cgroup definition)(Pos.eqb id _admit_child)=true)by tauto.
    rewrite CGROUP,NONRECURSIVE in CHECK;discriminate.
Qed.

Theorem admission_descriptor_source_step fd before trace after :
  admission_descriptor_state fd before ->step2 caller_ge before trace after ->admission_descriptor_state fd after.
Proof.
  intros [CLOSED CONTROL] STEP;split.
  - eapply closure_source_step;[exact admission_descriptor_source_closure|exact CLOSED|exact STEP].
  - inversion STEP;subst;
      cbn[admission_descriptor_control admission_descriptor_immutable admission_descriptor_cont checked_statement]in *;
      repeat rewrite andb_true_iff in *;try solve[intuition discriminate].
    + destruct CONTROL as[FUNCTION[IMMUTABLE[CALLS[REGISTER CONT]]]].
      refine(conj FUNCTION(conj eq_refl(conj eq_refl(conj _ CONT)))).
      apply admission_descriptor_temp_set;[exact REGISTER| |].
      all:apply negb_true_iff,orb_false_iff in IMMUTABLE as[FD CG];
        apply Pos.eqb_neq in FD,CG;assumption.
    + destruct CONTROL as[FUNCTION[IMMUTABLE[CALLS[REGISTER CONT]]]].
      destruct CLOSED as[[ENV GLOBAL_CONT][CALL CLOSED_CONT]].
      split.
      * eapply admission_descriptor_actual_call;eassumption.
      * split;[exact I|]. cbn;exact(conj FUNCTION(conj REGISTER(conj IMMUTABLE CONT))).
    + destruct b;cbn;tauto.
    + destruct CONTROL as[FUNCTION[IMMUTABLE[CALLS[REGISTER CONT]]]].
      split;[apply admission_descriptor_call_cont_is_call|].
      exact(admission_descriptor_call_cont fd(admission_descriptor_mode f)None k CONT).
    + destruct CONTROL as[FUNCTION[IMMUTABLE[CALLS[REGISTER CONT]]]].
      split;[apply admission_descriptor_call_cont_is_call|].
      exact(admission_descriptor_call_cont fd(admission_descriptor_mode f)None k CONT).
    + destruct CONTROL as[FUNCTION[IMMUTABLE[CALLS[REGISTER CONT]]]].
      split;[assumption|]. eapply admission_descriptor_cont_call_mode;[assumption|exact CONT].
    + destruct CONTROL as[ARGUMENTS[CALL CONT]].
      destruct CLOSED as[GLOBAL[FUNCTION CLOSED_CONT]].
      pose proof(admission_descriptor_function_checked _ FUNCTION)as CHECKED.
      assert(CONT':admission_descriptor_cont fd(admission_descriptor_mode f)k).
      { eapply admission_descriptor_cont_call_mode;[exact CALL|exact CONT]. }
      refine(conj CHECKED(conj(proj1 CHECKED)(conj(proj2 CHECKED)(conj _ CONT')))).
      eapply admission_descriptor_function_entry;eassumption.
    + destruct CONTROL as[CALL CONT].
      destruct CONT as[FUNCTION[REGISTER[OPTIONAL CONT]]].
      refine(conj FUNCTION(conj eq_refl(conj eq_refl(conj _ CONT)))).
      eapply admission_descriptor_temp_optional;eassumption.
Qed.

Lemma admission_descriptor_external_return fd definition args k before value after :
  admission_descriptor_control fd(Callstate definition args k before) ->
  admission_descriptor_control fd(Returnstate value k after).
Proof.
  intros[ARGS[CALL CONT]];split;[exact CALL|].
  eapply admission_descriptor_cont_call_mode;eassumption.
Qed.

Lemma admission_descriptor_original_step fd cell before event after :
  admission_descriptor_machine fd before ->Machine.step caller_ge cell before event after ->
  admission_descriptor_machine fd after.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn[admission_descriptor_machine]in *;try exact I;try exact GOOD.
  all:try solve[eapply admission_descriptor_source_step;eassumption].
  all:destruct GOOD as[CLOSED CONTROL];split;
    [match type of STEP with Machine.step _ _ ?first ?current ?last=>
      exact(closure_original_step admission_descriptor_calls cell first current last admission_descriptor_source_closure CLOSED STEP)end|
      exact(admission_descriptor_external_return fd _ _ _ _ _ _ CONTROL)].
Qed.

Lemma admission_descriptor_library_step fd cell before event after :
  admission_descriptor_machine fd before ->library_step caller_ge cell before event after ->
  admission_descriptor_machine fd after.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn[admission_descriptor_machine]in *;try exact I;try exact GOOD.
  all:try solve[eapply admission_descriptor_original_step;eassumption].
  all:destruct GOOD as[CLOSED CONTROL];split;
    [match type of STEP with library_step _ _ ?first ?current ?last=>
      exact(closure_library_step admission_descriptor_calls cell first current last admission_descriptor_source_closure CLOSED STEP)end|
      exact(admission_descriptor_external_return fd _ _ _ _ _ _ CONTROL)].
Qed.

Lemma admission_descriptor_entry_step fd cell before event after :
  admission_descriptor_machine fd before ->entry_handoff_step caller_ge cell before event after ->
  admission_descriptor_machine fd after.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn[admission_descriptor_machine]in *;try exact I;try exact GOOD.
  all:try solve[eapply admission_descriptor_library_step;eassumption].
  all:destruct GOOD as[CLOSED CONTROL];split;
    [match type of STEP with entry_handoff_step _ _ ?first ?current ?last=>
      exact(closure_entry_step admission_descriptor_calls cell first current last admission_descriptor_source_closure CLOSED STEP)end|
      exact(admission_descriptor_external_return fd _ _ _ _ _ _ CONTROL)].
Qed.

Lemma admission_descriptor_process_step fd cell before event after :
  admission_descriptor_machine fd before ->process_step caller_ge cell before event after ->
  admission_descriptor_machine fd after.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn[admission_descriptor_machine]in *;try exact I;try exact GOOD.
  all:try solve[eapply admission_descriptor_entry_step;eassumption].
  all:destruct GOOD as[CLOSED CONTROL];split;
    [match type of STEP with process_step _ _ ?first ?current ?last=>
      exact(closure_process_step admission_descriptor_calls cell first current last admission_descriptor_source_closure CLOSED STEP)end|
      exact(admission_descriptor_external_return fd _ _ _ _ _ _ CONTROL)].
Qed.

Theorem admission_descriptor_namespace_step fd cell before event after :
  admission_descriptor_machine fd before ->namespace_step caller_ge cell before event after ->
  admission_descriptor_machine fd after.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn[admission_descriptor_machine]in *;try exact I;try exact GOOD.
  all:try solve[eapply admission_descriptor_process_step;eassumption].
  all:destruct GOOD as[CLOSED CONTROL];split;
    [match type of STEP with namespace_step _ _ ?first ?current ?last=>
      exact(closure_namespace_step admission_descriptor_calls cell first current last admission_descriptor_source_closure CLOSED STEP)end|
      exact(admission_descriptor_external_return fd _ _ _ _ _ _ CONTROL)].
Qed.

Theorem admission_descriptor_namespace_prefix fd cell before events after :
  admission_descriptor_machine fd before ->namespace_steps caller_ge cell before events after ->
  admission_descriptor_machine fd after.
Proof.
  intros GOOD RUN;revert GOOD;induction RUN;intro GOOD;[exact GOOD|].
  apply IHRUN;eapply admission_descriptor_namespace_step;eassumption.
Qed.

Definition admission_descriptor_io_event fd event : Prop := match event with
  |io_step q _|partial_loss q _ _=>operation q=writing ->descriptor q=fd
  |_=>True end.
Definition admission_descriptor_library_event fd event := match event with
  |original_event event=>admission_descriptor_io_event fd event|_=>True end.
Definition admission_descriptor_entry_event fd event := match event with
  |entry_library event=>admission_descriptor_library_event fd event|_=>True end.
Definition admission_descriptor_process_event fd event := match event with
  |process_entry event=>admission_descriptor_entry_event fd event|_=>True end.
Definition admission_descriptor_namespace_event fd event := match event with
  |namespace_process event=>admission_descriptor_process_event fd event|_=>True end.

Lemma admission_descriptor_io_boundary fd cell state q : admission_descriptor_control fd state ->boundary cell state q ->
  operation q=writing ->descriptor q=fd.
Proof.
  intros CONTROL BOUNDARY WRITING;inversion BOUNDARY;subst.
  destruct CONTROL as[ARGS[CALL CONT]].
  destruct ARGS as[ARGS CGROUP];unfold admission_descriptor_required in ARGS;rewrite WRITING in ARGS.
  destruct(ARGS eq_refl)as[rest VALUES];inversion VALUES;reflexivity.
Qed.

Lemma admission_descriptor_original_event fd cell before event after :
  admission_descriptor_machine fd before ->Machine.step caller_ge cell before event after ->admission_descriptor_io_event fd event.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn[admission_descriptor_io_event];try exact I.
  all:intro WRITING;eapply admission_descriptor_io_boundary;[exact(proj2 GOOD)|eassumption|exact WRITING].
Qed.
Lemma admission_descriptor_library_event_checked fd cell before event after :
  admission_descriptor_machine fd before ->library_step caller_ge cell before event after ->admission_descriptor_library_event fd event.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn[admission_descriptor_library_event];try exact I.
  eapply admission_descriptor_original_event;eassumption.
Qed.
Lemma admission_descriptor_entry_event_checked fd cell before event after :
  admission_descriptor_machine fd before ->entry_handoff_step caller_ge cell before event after ->admission_descriptor_entry_event fd event.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn[admission_descriptor_entry_event];try exact I.
  eapply admission_descriptor_library_event_checked;eassumption.
Qed.
Lemma admission_descriptor_process_event_checked fd cell before event after :
  admission_descriptor_machine fd before ->process_step caller_ge cell before event after ->admission_descriptor_process_event fd event.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn[admission_descriptor_process_event];try exact I.
  eapply admission_descriptor_entry_event_checked;eassumption.
Qed.
Lemma admission_descriptor_namespace_event_checked fd cell before event after :
  admission_descriptor_machine fd before ->namespace_step caller_ge cell before event after ->admission_descriptor_namespace_event fd event.
Proof.
  intros GOOD STEP;inversion STEP;subst;cbn[admission_descriptor_namespace_event];try exact I.
  eapply admission_descriptor_process_event_checked;eassumption.
Qed.

Theorem admission_descriptor_actual_namespace_writes fd cell before events after :
  admission_descriptor_machine fd before ->namespace_steps caller_ge cell before events after ->
  Forall(admission_descriptor_namespace_event fd)events.
Proof.
  intros GOOD RUN;revert GOOD;induction RUN;intro GOOD;constructor.
  - eapply admission_descriptor_namespace_event_checked;eassumption.
  - apply IHRUN;eapply admission_descriptor_namespace_step;eassumption.
Qed.

Theorem admission_descriptor_initial fd fn arguments memory :
  closure_function admission_descriptor_calls(Internal fn) ->admission_descriptor_arguments fd(Internal fn)arguments ->
  admission_descriptor_machine fd(live(Callstate(Internal fn)arguments Kstop memory)).
Proof.
  intros FUNCTION ARGUMENTS;split.
  - split.
    + split;[destruct FUNCTION as[id[MEMBER LOOKUP]];eapply admission_descriptor_lookup_global;exact LOOKUP|exact I].
    + split;[exact FUNCTION|exact I].
  - split;[exact ARGUMENTS|split;exact I].
Qed.

Theorem actual_admit_namespace_write_descriptors cell child cgroup status memory events after:
  namespace_steps caller_ge cell
    (live(Callstate(Internal f_admit_child)[Vint child;Vint cgroup;status]Kstop memory))events after->
  Forall(descriptor_namespace_event cgroup)events.
Proof.
  intro RUN;change(Forall(admission_descriptor_namespace_event cgroup)events).
  eapply admission_descriptor_actual_namespace_writes;[|exact RUN].
  apply admission_descriptor_initial;[exact admission_descriptor_admit_binding|].
  split.
  - intro REQUIRED;change(false=true)in REQUIRED;discriminate.
  - intro REQUIRED;exists(Vint child),[status];reflexivity.
Qed.
