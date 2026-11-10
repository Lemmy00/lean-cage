(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Genuine keyword types come from the actual SDK header accessor. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Errors
  Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayRuntime GatewayKeywordRuntime
  GatewayEffectRuntime GatewayFramedRuntime GatewayReadonly GatewayPathEvents.
Import ListNotations.
Open Scope Z_scope.

Definition keyword_header_parameters object:=PTree.set _ob object(create_undef_temps(fn_temps f_Py_TYPE)).
Definition keyword_header_expression:=match fn_body f_Py_TYPE with
  |Ssequence(Sset _ expression)_=>expression|_=>Econst_int Int.zero tint end.
Definition keyword_header_after:=match fn_body f_Py_TYPE with Ssequence _ after=>after|_=>Sskip end.

Lemma actual_keyword_header_entry ge object memory:
  function_entry2 ge f_Py_TYPE[object]memory empty_env(keyword_header_parameters object)memory.
Proof.
  constructor;[constructor|repeat constructor;cbn;intuition discriminate| |constructor|reflexivity].
  unfold list_disjoint,var_names;cbn;intros first second LEFT RIGHT;
    repeat destruct LEFT as[LEFT|LEFT];try contradiction;subst first;
    repeat destruct RIGHT as[RIGHT|RIGHT];try contradiction;subst second;discriminate.
Qed.

Lemma actual_keyword_header_members:
  option_map co_members((prog_comp_env prog)!__object)=Some
    [Member_plain 18727075383868559167%positive(Tunion __5138 noattr);
      Member_plain _ob_type(tptr(Tstruct __typeobject noattr))].
Proof. vm_compute;reflexivity. Qed.

Lemma actual_keyword_refcount_layout:
  sizeof(prog_comp_env prog)(Tunion __5138 noattr)=8 /\alignof(prog_comp_env prog)(Tunion __5138 noattr)=8.
Proof. vm_compute;split;reflexivity. Qed.

Lemma actual_keyword_header_layout:
  exists composite,(genv_cenv(Clight.globalenv prog))!__object=Some composite /\
    field_offset(genv_cenv(Clight.globalenv prog))_ob_type(co_members composite)=OK(8,Full).
Proof.
  pose proof actual_keyword_header_members as MEMBERS.
  destruct((prog_comp_env prog)!__object)as[composite|]eqn:LOOK;[|discriminate].
  cbn in MEMBERS;injection MEMBERS as MEMBERS.
  exists composite;split;[exact LOOK|]. rewrite MEMBERS.
  destruct actual_keyword_refcount_layout as[SIZE ALIGNMENT].
  change(field_offset(prog_comp_env prog)_ob_type
    [Member_plain 18727075383868559167%positive(Tunion __5138 noattr);
      Member_plain _ob_type(tptr(Tstruct __typeobject noattr))]=OK(8,Full)).
  cbn[field_offset field_offset_rec];reflexivity.
Qed.

Local Opaque prog.

Section KeywordTypes.
Context {World Event}(backend:gateway_backend World Event)(python:World->python_world)
  (views:gateway_keyword_views World)(io:Event->option GatewayStreamInterface.gateway_native_io)
  (normal:mem->World->Prop)(runtime:gateway_keyword_runtime backend python views io normal).

Definition keyword_header_context object class memory world:Prop:=
  normal memory world /\python_live(python world)object /\gateway_keyword_address memory object /\
    gateway_object_class _ views world object class.

Lemma keyword_header_context_ambient object class:
  gateway_ambient_closed backend(keyword_header_context object class).
Proof.
  intros before world after next[NORMAL[LIVE[ADDRESS CLASS]]]INTERFERENCE.
  destruct(gateway_keyword_ambient _ _ _ _ _ runtime _ _ _ _ NORMAL INTERFERENCE)
    as[NEXT_NORMAL[RETAINED[EXTENSION_FRAME[PRIVATE_FRAME BORROWED]]]].
  destruct(BORROWED object LIVE ADDRESS)as[NEXT_LIVE NEXT_ADDRESS].
  split;[exact NEXT_NORMAL|]. split;[exact NEXT_LIVE|]. split;[exact NEXT_ADDRESS|].
  destruct RETAINED as[_[_[_[_[CLASSES REST]]]]];apply CLASSES;assumption.
Qed.

Lemma actual_keyword_header_value memory world temporaries object class:
  keyword_header_context object class memory world->temporaries!_ob=Some object->
  expression_value(Clight.globalenv prog)empty_env temporaries memory keyword_header_expression class.
Proof.
  intros[NORMAL[LIVE[[object_block[object_offset[POINTER ADDRESS]]]CLASS]]]OBJECT.
  destruct(gateway_keyword_type_headers _ _ _ _ _ runtime _ _ _ _ _ NORMAL LIVE POINTER
    ltac:(exists object_block,object_offset;auto))as[actual[BOUND[LOAD[ACTUAL REAL]]]].
  assert(SAME:actual=class)by(eapply(gateway_keyword_class_unique _ _ _ _ _ runtime);eassumption);subst actual.
  destruct actual_keyword_header_layout as[composite[COMPOSITE MEMBER]].
  eapply location_read_value with(b:=object_block)(ofs:=Ptrofs.add object_offset(Ptrofs.repr 8)).
  - eapply struct_location_value with(id:=__object)(co:=composite)(att:=noattr)(delta:=8).
    + eapply location_read_value.
      * apply pointer_location_value,old_expression_value,value_temp;rewrite<-POINTER;exact OBJECT.
      * apply deref_loc_copy;reflexivity.
    + reflexivity.
    + exact COMPOSITE.
    + exact MEMBER.
  - eapply deref_loc_value;[reflexivity|]. unfold Mem.loadv.
    rewrite Ptrofs.add_unsigned.
    rewrite(Ptrofs.unsigned_repr 8)by(change Ptrofs.max_unsigned with 18446744073709551615;lia).
    rewrite Ptrofs.unsigned_repr by(pose proof(Ptrofs.unsigned_range object_offset)as RANGE;
      change(0<=Ptrofs.unsigned object_offset<18446744073709551616)in RANGE;
      change Ptrofs.max_unsigned with 18446744073709551615;
      change Ptrofs.modulus with 18446744073709551616 in BOUND;lia).
    rewrite zle_true by(change(Ptrofs.unsigned object_offset+8+8<=Ptrofs.modulus);lia);exact LOAD.
Qed.

Ltac header_same target:=
  eapply gateway_effect_same with(next:=target);
    [apply keyword_header_context_ambient|cbn;tauto|intros available current GOOD;cbn[gateway_replace_memory]|].

Theorem actual_keyword_header_path object class before:
  gateway_effect_path backend(Clight.globalenv prog)(keyword_header_context object class)
    (Callstate(Internal f_Py_TYPE)[object]Kstop before)class(keyword_header_context object class).
Proof.
  header_same(State f_Py_TYPE(fn_body f_Py_TYPE)Kstop empty_env(keyword_header_parameters object)before).
  { apply function_entry_source_edge,actual_keyword_header_entry. }
  header_same(State f_Py_TYPE(Sset _t'1 keyword_header_expression)(Kseq keyword_header_after Kstop)
    empty_env(keyword_header_parameters object)before).
  { apply unchanged_store_edge,edge_seq. }
  header_same(State f_Py_TYPE Sskip(Kseq keyword_header_after Kstop)empty_env
    (PTree.set _t'1 class(keyword_header_parameters object))before).
  { apply certified_set_edge;eapply actual_keyword_header_value;
      [exact GOOD|unfold keyword_header_parameters;apply PTree.gss]. }
  header_same(State f_Py_TYPE keyword_header_after Kstop empty_env
    (PTree.set _t'1 class(keyword_header_parameters object))before).
  { apply unchanged_store_edge,edge_skip_seq. }
  header_same(Returnstate class Kstop before).
  { eapply certified_local_return_edge with(v:=class).
    - apply old_expression_value,value_temp;apply PTree.gss.
    - destruct GOOD as[NORMAL[LIVE[[object_block[object_offset[POINTER ADDRESS]]]CLASS]]].
      destruct(gateway_keyword_type_headers _ _ _ _ _ runtime _ _ _ _ _ NORMAL LIVE POINTER
        ltac:(exists object_block,object_offset;auto))as[actual[BOUND[LOAD[ACTUAL REAL]]]].
      assert(SAME:actual=class)by(eapply(gateway_keyword_class_unique _ _ _ _ _ runtime);eassumption);subst actual.
      destruct(gateway_keyword_type_addresses _ _ _ _ _ runtime _ _ _ NORMAL REAL)
        as[type_block[type_offset[TYPE TYPE_ADDRESS]]];rewrite TYPE;reflexivity.
    - reflexivity. }
  constructor;[apply keyword_header_context_ambient|auto].
Qed.

Theorem actual_keyword_header object class before world events returned after next:
  keyword_header_context object class before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_Py_TYPE)[object]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next)->
  returned=class /\keyword_header_context object class after next.
Proof.
  intros CONTEXT RUN.
  exact(gateway_effect_return_exact backend(Clight.globalenv prog)(keyword_header_context object class)
    (Callstate(Internal f_Py_TYPE)[object]Kstop before)class(keyword_header_context object class)
    before world events returned after next CONTEXT(actual_keyword_header_path object class before)RUN).
Qed.

Theorem actual_keyword_header_passthrough(extra:mem->World->Prop)object class before world events returned after next:
  gateway_ambient_closed backend extra->keyword_header_context object class before world->extra before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_Py_TYPE)[object]Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next)->
  returned=class /\keyword_header_context object class after next /\extra after next /\Forall gateway_quiet_event events.
Proof.
  intros CLOSED CONTEXT EXTRA RUN.
  destruct(actual_keyword_header object class before world events returned after next CONTEXT RUN)as[VALUE FINAL].
  split;[exact VALUE|]. split;[exact FINAL|]. split.
  - exact(gateway_readonly_run_side backend(Clight.globalenv prog)extra CLOSED
      (Callstate(Internal f_Py_TYPE)[object]Kstop before)world events returned after next
      ltac:(split;reflexivity)EXTRA RUN).
  - exact(gateway_readonly_run_events backend(Clight.globalenv prog)
      (Callstate(Internal f_Py_TYPE)[object]Kstop before)world events returned after next ltac:(split;reflexivity)RUN).
Qed.

End KeywordTypes.
