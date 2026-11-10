(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual SDK identity helper compares genuine type pointers. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayBindings GatewayKeywordRuntime
  GatewayKeywordTypes GatewayPointerEquality GatewayPython GatewayRuntime GatewayEffectRuntime
  GatewayEffectComposition GatewayFramedRuntime GatewayReadonly GatewayCallPath GatewayContexts.
Import ListNotations.
Open Scope Z_scope.

Definition keyword_identity_parameters object wanted:=PTree.set _type wanted
  (PTree.set _ob object(create_undef_temps(fn_temps f_Py_IS_TYPE))).
Definition keyword_identity_call:=match fn_body f_Py_IS_TYPE with Ssequence call _=>call|_=>Sskip end.
Definition keyword_identity_after:=match fn_body f_Py_IS_TYPE with Ssequence _ after=>after|_=>Sskip end.
Definition keyword_identity_cont object wanted:=Kcall(Some _t'1)f_Py_IS_TYPE empty_env
  (keyword_identity_parameters object wanted)(Kseq keyword_identity_after Kstop).
Definition keyword_identity_result class wanted:=Vint(if Val.eq class wanted then Int.one else Int.zero).

Lemma actual_keyword_header_binding:
  gateway_function_binding(Clight.globalenv prog)_Py_TYPE(Internal f_Py_TYPE).
Proof. apply gateway_actual_function_binding;vm_compute;reflexivity. Qed.

Lemma keyword_identity_entry(ge:Clight.genv)object wanted memory:
  function_entry2 ge f_Py_IS_TYPE[object;wanted]memory empty_env(keyword_identity_parameters object wanted)memory.
Proof.
  constructor;[constructor|repeat constructor;cbn;intuition discriminate| |constructor|reflexivity].
  unfold list_disjoint,var_names;cbn;intros first second LEFT RIGHT;
    repeat destruct LEFT as[LEFT|LEFT];try contradiction;subst first;
    repeat destruct RIGHT as[RIGHT|RIGHT];try contradiction;subst second;discriminate.
Qed.

Lemma keyword_identity_first_call(ge:Clight.genv)object object_offset wanted memory symbol:
  Genv.find_symbol ge _Py_TYPE=Some symbol->Genv.find_funct_ptr ge symbol=Some(Internal f_Py_TYPE)->
  store_edge ge
    (State f_Py_IS_TYPE keyword_identity_call(Kseq keyword_identity_after Kstop)empty_env
      (keyword_identity_parameters(Vptr object object_offset)wanted)memory)
    (Callstate(Internal f_Py_TYPE)[Vptr object object_offset]
      (keyword_identity_cont(Vptr object object_offset)wanted)memory).
Proof.
  intros SYMBOL FUNCTION;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
  - eapply cons_argument_values with(v:=Vptr object object_offset).
    + apply old_expression_value,value_temp;unfold keyword_identity_parameters;rewrite PTree.gso by discriminate;apply PTree.gss.
    + reflexivity.
    + apply no_argument_values.
  - cbn;exact FUNCTION.
  - reflexivity.
Qed.

Lemma keyword_identity_first_path(ge:Clight.genv)object object_offset wanted memory symbol:
  Genv.find_symbol ge _Py_TYPE=Some symbol->Genv.find_funct_ptr ge symbol=Some(Internal f_Py_TYPE)->
  gateway_retained_call_path ge(Internal f_Py_TYPE)[Vptr object object_offset]
    (keyword_identity_cont(Vptr object object_offset)wanted)
    (Callstate(Internal f_Py_IS_TYPE)[Vptr object object_offset;wanted]Kstop memory).
Proof.
  intros SYMBOL FUNCTION.
  eapply gateway_retained_next with(next:=State f_Py_IS_TYPE(fn_body f_Py_IS_TYPE)Kstop empty_env
    (keyword_identity_parameters(Vptr object object_offset)wanted)memory);
    [cbn;tauto|intro available;apply function_entry_source_edge,keyword_identity_entry|].
  eapply gateway_retained_next with(next:=State f_Py_IS_TYPE keyword_identity_call(Kseq keyword_identity_after Kstop)
    empty_env(keyword_identity_parameters(Vptr object object_offset)wanted)memory);
    [cbn;tauto|intro available;apply unchanged_store_edge,edge_seq|].
  eapply gateway_retained_next with(next:=Callstate(Internal f_Py_TYPE)[Vptr object object_offset]
    (keyword_identity_cont(Vptr object object_offset)wanted)memory).
  - cbn;tauto.
  - intro available;eapply keyword_identity_first_call;eassumption.
  - constructor.
Qed.

Local Opaque prog.
Section Identity.
Context {World Event}(backend:gateway_backend World Event)(python:World->python_world)
  (views:gateway_keyword_views World)(io:Event->option GatewayStreamInterface.gateway_native_io)
  (normal:mem->World->Prop)(runtime:gateway_keyword_runtime backend python views io normal).

Definition keyword_identity_context object class wanted memory world:Prop:=
  keyword_header_context python views normal object class memory world /\
    gateway_real_type _ views world wanted.

Lemma keyword_identity_ambient object class wanted:
  gateway_ambient_closed backend(keyword_identity_context object class wanted).
Proof.
  intros before world after next[HEADER WANTED]INTERFERENCE;split.
  - eapply keyword_header_context_ambient;[exact runtime|exact HEADER|exact INTERFERENCE].
  - destruct(gateway_keyword_ambient _ _ _ _ _ runtime _ _ _ _ (proj1 HEADER)INTERFERENCE)
      as[NORMAL[RETAINED REST]].
    destruct RETAINED as[_[_[_[_[_[TYPES MORE]]]]]];apply TYPES;exact WANTED.
Qed.

Definition keyword_identity_returned object class wanted returned memory world:Prop:=
  returned=class /\keyword_identity_context object class wanted memory world.

Lemma keyword_identity_returned_ambient object class wanted returned:
  gateway_ambient_closed backend(keyword_identity_returned object class wanted returned).
Proof. intros before world after next[VALUE CONTEXT]STEP;split;[exact VALUE|eapply keyword_identity_ambient;eassumption]. Qed.

Ltac identity_same target:=
  eapply gateway_effect_same with(next:=target);
    [apply keyword_identity_returned_ambient|cbn;tauto|intros available current GOOD;cbn[gateway_replace_memory]|].

Lemma keyword_identity_caller_path object class wanted returned memory:
  gateway_effect_path backend(Clight.globalenv prog)(keyword_identity_returned object class wanted returned)
    (Returnstate returned(keyword_identity_cont object wanted)memory)(keyword_identity_result class wanted)
    (keyword_identity_context object class wanted).
Proof.
  identity_same(State f_Py_IS_TYPE Sskip(Kseq keyword_identity_after Kstop)empty_env
    (PTree.set _t'1 returned(keyword_identity_parameters object wanted))memory).
  { apply unchanged_store_edge,edge_returnstate. }
  identity_same(State f_Py_IS_TYPE keyword_identity_after Kstop empty_env
    (PTree.set _t'1 returned(keyword_identity_parameters object wanted))memory).
  { apply unchanged_store_edge,edge_skip_seq. }
  identity_same(Returnstate(keyword_identity_result class wanted)Kstop memory).
  { destruct GOOD as[VALUE[HEADER WANTED]];subst returned.
    destruct HEADER as[NORMAL[LIVE[ADDRESS CLASS]]].
    destruct ADDRESS as[object_block[object_offset[OBJECT OBJECT_VALID]]].
    destruct(gateway_keyword_type_headers _ _ _ _ _ runtime _ _ _ _ _ NORMAL LIVE OBJECT
      ltac:(exists object_block,object_offset;auto))as[actual[BOUND[LOAD[ACTUAL CLASS_TYPE]]]].
    assert(SAME:actual=class)by(eapply(gateway_keyword_class_unique _ _ _ _ _ runtime);eassumption);subst actual.
    eapply certified_local_return_edge with(v:=keyword_identity_result class wanted).
    - apply old_expression_value;eapply value_binary.
      + apply value_temp;apply PTree.gss.
      + apply value_temp;rewrite PTree.gso by discriminate;unfold keyword_identity_parameters;apply PTree.gss.
      + apply gateway_live_pointer_equality.
        * exact(gateway_keyword_type_addresses _ _ _ _ _ runtime _ _ _ NORMAL CLASS_TYPE).
        * exact(gateway_keyword_type_addresses _ _ _ _ _ runtime _ _ _ NORMAL WANTED).
    - unfold keyword_identity_result;destruct(Val.eq class wanted);reflexivity.
    - reflexivity. }
  constructor;[apply keyword_identity_returned_ambient|intros available current[_ CONTEXT];exact CONTEXT].
Qed.

Lemma keyword_identity_header_returns object class wanted before world events returned after next:
  keyword_identity_context object class wanted before world->
  gateway_steps backend(Clight.globalenv prog)(gateway_live(Callstate(Internal f_Py_TYPE)[object]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next)->
  keyword_identity_returned object class wanted returned after next.
Proof.
  intros[HEADER WANTED]RUN.
  assert(CLOSED:gateway_ambient_closed backend(fun memory world=>normal memory world /\gateway_real_type _ views world wanted)).
  { intros previous current following target[NORMAL TYPE]STEP.
    destruct(gateway_keyword_ambient _ _ _ _ _ runtime _ _ _ _ NORMAL STEP)as[NEXT[RETAINED REST]].
    split;[exact NEXT|]. destruct RETAINED as[_[_[_[_[_[TYPES MORE]]]]]];apply TYPES;exact TYPE. }
  destruct(actual_keyword_header_passthrough backend python views io normal runtime
    (fun memory world=>normal memory world /\gateway_real_type _ views world wanted)
    object class before world events returned after next CLOSED HEADER ltac:(split;[exact(proj1 HEADER)|exact WANTED])RUN)
    as[VALUE[AFTER[[NORMAL TYPE]QUIET]]].
  split;[exact VALUE|]. split;assumption.
Qed.

Theorem actual_keyword_identity object class wanted before world events returned after next:
  keyword_identity_context object class wanted before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_Py_IS_TYPE)[object;wanted]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next)->
  returned=keyword_identity_result class wanted /\keyword_identity_context object class wanted after next.
Proof.
  intros INITIAL RUN.
  destruct(proj1 INITIAL)as[NORMAL[LIVE[[object_block[object_offset[OBJECT ADDRESS]]]CLASS]]];subst object.
  destruct actual_keyword_header_binding as[symbol[SYMBOL FUNCTION]].
  destruct(gateway_retained_call_ready_cut backend(Clight.globalenv prog)
    (keyword_identity_context(Vptr object_block object_offset)class wanted)
    (keyword_identity_ambient(Vptr object_block object_offset)class wanted)(Internal f_Py_TYPE)
    [Vptr object_block object_offset](keyword_identity_cont(Vptr object_block object_offset)wanted)
    (Callstate(Internal f_Py_IS_TYPE)[Vptr object_block object_offset;wanted]Kstop before)world events returned after next
    (keyword_identity_first_path _ object_block object_offset wanted before symbol SYMBOL FUNCTION)INITIAL RUN)
    as[prefix[suffix[called[call_world[EVENTS[QUIET[PREFIX[CONTEXT REST]]]]]]]].
  destruct(gateway_callee_return_composition backend(Clight.globalenv prog)(Internal f_Py_TYPE)
    [Vptr object_block object_offset](keyword_identity_cont(Vptr object_block object_offset)wanted)
    (keyword_identity_context(Vptr object_block object_offset)class wanted)
    (keyword_identity_returned(Vptr object_block object_offset)class wanted)(keyword_identity_result class wanted)
    (keyword_identity_context(Vptr object_block object_offset)class wanted)called call_world suffix returned after next
    ltac:(exact I)ltac:(cbn;lia)
    (keyword_identity_header_returns(Vptr object_block object_offset)class wanted)
    (keyword_identity_caller_path(Vptr object_block object_offset)class wanted)CONTEXT REST)
    as[inside[outside[callee_value[callee_memory[callee_world[ORDER[CALLEE[POST[CALLER FINAL]]]]]]]]].
  exact FINAL.
Qed.

End Identity.
