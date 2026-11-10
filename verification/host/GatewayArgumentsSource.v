(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Retained arguments are the objects loaded by the actual root loop. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs
  Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From HostGateway Require Import GatewaySource GatewayPython GatewayWordsMemory GatewayMachine GatewayArgumentContext.
Import ListNotations.
Open Scope Z_scope.

Definition arguments_pointer_type:=tptr(tptr(Tstruct __object noattr)).
Definition arguments_object_type:=tptr(Tstruct __object noattr).
Definition arguments_element:=Ederef
  (Ebinop Oadd(Etempvar _arguments arguments_pointer_type)(Etempvar _index tuint)arguments_pointer_type)
  arguments_object_type.
Definition arguments_guard:=Ebinop Olt(Etempvar _index tuint)(Etempvar _count tuint)tint.
Definition arguments_retain_loop:=match fn_body f_host_arguments_retain with Ssequence _ loop=>loop|_=>Sskip end.
Definition arguments_retain_first:=match arguments_retain_loop with Sloop first _=>first|_=>Sskip end.
Definition arguments_retain_increment:=match arguments_retain_loop with Sloop _ increment=>increment|_=>Sskip end.
Definition arguments_retain_body:=match arguments_retain_first with Ssequence _ body=>body|_=>Sskip end.
Definition arguments_retain_test:=match arguments_retain_body with Ssequence _ test=>test|_=>Sskip end.
Definition arguments_retain_call:=Scall None
  (Evar _Py_IncRef(Tfunction[arguments_object_type]tvoid cc_default))[Etempvar _t'2 arguments_object_type].
Definition arguments_retain_cont:=Kloop1 arguments_retain_first arguments_retain_increment Kstop.
Definition arguments_retain_parameters pointer count:=PTree.set _count(Vint(Int.repr count))
  (PTree.set _arguments pointer(create_undef_temps(fn_temps f_host_arguments_retain))).

Theorem actual_arguments_retain_shape:
  fn_body f_host_arguments_retain=Ssequence(Sset _index(Econst_int Int.zero tint))arguments_retain_loop /\
  arguments_retain_loop=Sloop arguments_retain_first arguments_retain_increment /\
  arguments_retain_first=Ssequence(Sifthenelse arguments_guard Sskip Sbreak)arguments_retain_body /\
  arguments_retain_body=Ssequence(Sset _t'1 arguments_element)arguments_retain_test /\
  arguments_retain_test=Sifthenelse(Etempvar _t'1 arguments_object_type)
    (Ssequence(Sset _t'2 arguments_element)arguments_retain_call)Sskip /\
  arguments_retain_increment=Sset _index(Ebinop Oadd(Etempvar _index tuint)(Econst_int Int.one tint)tuint).
Proof. repeat split;reflexivity. Qed.

Lemma actual_arguments_retain_entry ge pointer count memory:
  function_entry2 ge f_host_arguments_retain[pointer;Vint(Int.repr count)]memory empty_env
    (arguments_retain_parameters pointer count)memory.
Proof.
  constructor;[constructor|repeat constructor;cbn;intuition discriminate| |constructor|reflexivity].
  unfold list_disjoint,var_names;cbn;intros first second LEFT RIGHT;
    repeat destruct LEFT as[LEFT|LEFT];try contradiction;subst first;
    repeat destruct RIGHT as[RIGHT|RIGHT];try contradiction;subst second;discriminate.
Qed.

Lemma arguments_pointer_step index:
  0<=index<=14->
  Ptrofs.mul(Ptrofs.repr 8)(Ptrofs.of_intu(Int.repr index))=Ptrofs.repr(8*index).
Proof.
  intro BOUND;unfold Ptrofs.of_intu,Ptrofs.of_int.
  rewrite Int.unsigned_repr by(change Int.max_unsigned with 4294967295;lia).
  unfold Ptrofs.mul;rewrite!Ptrofs.unsigned_repr by(change Ptrofs.max_unsigned with 18446744073709551615;lia).
  reflexivity.
Qed.

Lemma actual_argument_element (ge:Clight.genv)temporaries memory array offset index object:
  temporaries!_arguments=Some(Vptr array offset)->temporaries!_index=Some(Vint(Int.repr index))->
  0<=index<=14->Ptrofs.unsigned offset+8*index+8<=Ptrofs.modulus->
  Mem.load Mptr memory array(Ptrofs.unsigned offset+8*index)=Some object->
  expression_value ge empty_env temporaries memory arguments_element object.
Proof.
  intros POINTER INDEX BOUND NOWRAP LOAD.
  eapply location_read_value with(b:=array)(ofs:=Ptrofs.add offset(Ptrofs.repr(8*index))).
  - apply pointer_location_value,old_expression_value;eapply value_binary.
    + apply value_temp;exact POINTER.
    + apply value_temp;exact INDEX.
    + change(Some(Vptr array(Ptrofs.add offset(Ptrofs.mul(Ptrofs.repr 8)(Ptrofs.of_intu(Int.repr index)))))=
        Some(Vptr array(Ptrofs.add offset(Ptrofs.repr(8*index))))).
      rewrite arguments_pointer_step by exact BOUND;reflexivity.
  - eapply deref_loc_value;[reflexivity|]. unfold Mem.loadv.
    rewrite Ptrofs.add_unsigned.
    rewrite(Ptrofs.unsigned_repr(8*index))by(change Ptrofs.max_unsigned with 18446744073709551615;lia).
    rewrite Ptrofs.unsigned_repr by(unfold Ptrofs.max_unsigned;pose proof(Ptrofs.unsigned_range offset);lia).
    rewrite zle_true by exact NOWRAP;exact LOAD.
Qed.

Lemma actual_arguments_guard ge temporaries memory index count:
  temporaries!_index=Some(Vint(Int.repr index))->temporaries!_count=Some(Vint(Int.repr count))->
  0<=index<=14->0<=count<=14->
  expression_value ge empty_env temporaries memory arguments_guard(Vint(if zlt index count then Int.one else Int.zero)).
Proof.
  intros INDEX COUNT INDEX_BOUND COUNT_BOUND.
  apply old_expression_value;eapply value_binary;[apply value_temp;exact INDEX|apply value_temp;exact COUNT|].
  change(Some(Val.of_bool(Int.ltu(Int.repr index)(Int.repr count)))=
    Some(Vint(if zlt index count then Int.one else Int.zero))).
  unfold Int.ltu;rewrite!Int.unsigned_repr by(change Int.max_unsigned with 4294967295;lia).
  destruct(zlt index count);reflexivity.
Qed.

Lemma actual_arguments_retain_call (ge:Clight.genv)temporaries memory continuation object symbol:
  temporaries!_t'2=Some object->(exists block offset,object=Vptr block offset)->
  Genv.find_symbol ge _Py_IncRef=Some symbol->Genv.find_funct_ptr ge symbol=Some python_incref_definition->
  store_edge ge(State f_host_arguments_retain arguments_retain_call continuation empty_env temporaries memory)
    (Callstate python_incref_definition[object](Kcall None f_host_arguments_retain empty_env temporaries continuation)memory).
Proof.
  intros OBJECT[block[offset POINTER]]SYMBOL FUNCTION.
  eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
  - eapply cons_argument_values with(v:=object).
    + apply old_expression_value,value_temp;exact OBJECT.
    + rewrite POINTER;reflexivity.
    + apply no_argument_values.
  - cbn;exact FUNCTION.
  - reflexivity.
Qed.
