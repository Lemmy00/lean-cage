(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: Descriptor movement is selected from the actual two-iteration source loop. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayPairSource GatewayIntegerFailures GatewaySpawnABI.
Import ListNotations.
Open Scope Z_scope.

Definition pair_sequence_first(statement:statement):=match statement with Ssequence first _=>first|_=>Sskip end.
Definition pair_sequence_rest(statement:statement):=match statement with Ssequence _ rest=>rest|_=>Sskip end.
Definition pair_for:=pair_sequence_first pair_after_first.
Definition pair_return:=pair_sequence_rest pair_after_first.
Definition pair_initialize:=pair_sequence_first pair_for.
Definition pair_loop:=pair_sequence_rest pair_for.
Definition pair_iteration:=match pair_loop with Sloop first _=>first|_=>Sskip end.
Definition pair_increment:=match pair_loop with Sloop _ second=>second|_=>Sskip end.
Definition pair_limit:=pair_sequence_first pair_iteration.
Definition pair_work:=pair_sequence_rest pair_iteration.
Definition pair_load:=pair_sequence_first pair_work.
Definition pair_low_guard:=pair_sequence_rest pair_work.
Definition pair_low_body:=match pair_low_guard with Sifthenelse _ first _=>first|_=>Sskip end.
Definition pair_duplicate_sequence:=pair_sequence_first pair_low_body.
Definition pair_after_duplicate:=pair_sequence_rest pair_low_body.
Definition pair_duplicate_prefix:=pair_sequence_first pair_duplicate_sequence.
Definition pair_moved_set:=pair_sequence_rest pair_duplicate_sequence.
Definition pair_duplicate_load:=pair_sequence_first pair_duplicate_prefix.
Definition pair_duplicate_call:=pair_sequence_rest pair_duplicate_prefix.
Definition pair_moved_guard:=pair_sequence_first pair_after_duplicate.
Definition pair_replacement:=pair_sequence_rest pair_after_duplicate.
Definition pair_failure:=match pair_moved_guard with Sifthenelse _ first _=>first|_=>Sskip end.
Definition pair_close_prefix:=pair_sequence_first pair_replacement.
Definition pair_store:=pair_sequence_rest pair_replacement.
Definition pair_close_load:=pair_sequence_first pair_close_prefix.
Definition pair_close_call:=pair_sequence_rest pair_close_prefix.
Definition pair_loop_cont:=Kloop1 pair_iteration pair_increment(Kseq pair_return Kstop).
Definition pair_element:=Ebinop Oadd(Etempvar _pair(tptr tint))(Etempvar _index tuint)(tptr tint).
Definition pair_element_read:=Ederef pair_element tint.
Definition pair_limit_expression:=Ebinop Olt(Etempvar _index tuint)(Econst_int(Int.repr 2)tint)tint.
Definition pair_low_expression:=Ebinop Olt(Etempvar _t'5 tint)(Econst_int(Int.repr 4)tint)tint.

Theorem actual_pair_loop_shape:
  pair_for=Ssequence pair_initialize pair_loop /\pair_loop=Sloop pair_iteration pair_increment /\
  pair_iteration=Ssequence pair_limit pair_work /\
  pair_limit=Sifthenelse pair_limit_expression Sskip Sbreak /\
  pair_work=Ssequence(Sset _t'5 pair_element_read)pair_low_guard /\
  pair_low_guard=Sifthenelse pair_low_expression pair_low_body Sskip /\
  pair_duplicate_load=Sset _t'9 pair_element_read /\
  pair_moved_guard=Sifthenelse(Ebinop Olt(Etempvar _moved tint)(Econst_int Int.zero tint)tint)pair_failure Sskip /\
  pair_close_load=Sset _t'6 pair_element_read /\pair_store=Sassign(Ederef pair_element tint)(Etempvar _moved tint) /\
  gateway_must_integer_failure pair_failure /\
  pair_increment=Sset _index(Ebinop Oadd(Etempvar _index tuint)(Econst_int Int.one tint)tuint).
Proof. cbn;repeat split;try reflexivity;tauto. Qed.

Lemma pair_pointer_step index:
  0<=index<=2->Ptrofs.mul(Ptrofs.repr 4)(Ptrofs.of_intu(Int.repr index))=Ptrofs.repr(4*index).
Proof.
  intro BOUND;unfold Ptrofs.of_intu,Ptrofs.of_int.
  rewrite Int.unsigned_repr by(change Int.max_unsigned with 4294967295;lia).
  unfold Ptrofs.mul;rewrite!Ptrofs.unsigned_repr by(change Ptrofs.max_unsigned with 18446744073709551615;lia).
  reflexivity.
Qed.

Lemma actual_pair_duplicate_call(ge:Clight.genv)temporaries memory continuation descriptor symbol:
  temporaries!_t'9=Some(Vint(Int.repr descriptor))->
  Genv.find_symbol ge _leancage_host_fcntl=Some symbol->
  Genv.find_funct_ptr ge symbol=Some(gateway_spawn_signature gateway_fcntl_api)->
  store_edge ge(State f_host_private_pair pair_duplicate_call continuation empty_env temporaries memory)
    (Callstate(gateway_spawn_signature gateway_fcntl_api)
      [Vint(Int.repr descriptor);Vint(Int.repr 1030);Vint(Int.repr 4)]
      (Kcall(Some _t'2)f_host_private_pair empty_env temporaries continuation)memory).
Proof.
  intros DESCRIPTOR SYMBOL FUNCTION;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
  - eapply cons_argument_values with(v:=Vint(Int.repr descriptor));
      [apply old_expression_value,value_temp;exact DESCRIPTOR|reflexivity|].
    eapply cons_argument_values with(v:=Vint(Int.repr 1030));
      [apply old_expression_value;constructor|reflexivity|].
    eapply cons_argument_values with(v:=Vint(Int.repr 4));
      [apply old_expression_value;constructor|reflexivity|apply no_argument_values].
  - cbn;exact FUNCTION.
  - reflexivity.
Qed.

Lemma actual_pair_close_call(ge:Clight.genv)temporaries memory continuation descriptor symbol:
  temporaries!_t'6=Some(Vint(Int.repr descriptor))->
  Genv.find_symbol ge _close=Some symbol->
  Genv.find_funct_ptr ge symbol=Some(gateway_spawn_signature gateway_close_api)->
  store_edge ge(State f_host_private_pair pair_close_call continuation empty_env temporaries memory)
    (Callstate(gateway_spawn_signature gateway_close_api)[Vint(Int.repr descriptor)]
      (Kcall None f_host_private_pair empty_env temporaries continuation)memory).
Proof.
  intros DESCRIPTOR SYMBOL FUNCTION;eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
  - eapply cons_argument_values with(v:=Vint(Int.repr descriptor));
      [apply old_expression_value,value_temp;exact DESCRIPTOR|reflexivity|apply no_argument_values].
  - cbn;exact FUNCTION.
  - reflexivity.
Qed.

Lemma actual_pair_element(ge:Clight.genv)temporaries memory object offset index:
  temporaries!_pair=Some(Vptr object offset)->temporaries!_index=Some(Vint(Int.repr index))->0<=index<=2->
  expression_value ge empty_env temporaries memory pair_element(Vptr object(Ptrofs.add offset(Ptrofs.repr(4*index)))).
Proof.
  intros POINTER INDEX BOUND;apply old_expression_value;eapply value_binary.
  - apply value_temp;exact POINTER.
  - apply value_temp;exact INDEX.
  - change(Some(Vptr object(Ptrofs.add offset(Ptrofs.mul(Ptrofs.repr 4)(Ptrofs.of_intu(Int.repr index)))))=
      Some(Vptr object(Ptrofs.add offset(Ptrofs.repr(4*index))))).
    rewrite pair_pointer_step by exact BOUND;reflexivity.
Qed.

Lemma actual_pair_element_read(ge:Clight.genv)temporaries memory object offset index value:
  temporaries!_pair=Some(Vptr object offset)->temporaries!_index=Some(Vint(Int.repr index))->0<=index<2->
  Ptrofs.unsigned offset+8<=Ptrofs.modulus->
  Mem.load Mint32 memory object(Ptrofs.unsigned offset+4*index)=Some value->
  expression_value ge empty_env temporaries memory pair_element_read value.
Proof.
  intros POINTER INDEX BOUND NOWRAP LOAD.
  eapply location_read_value with(b:=object)(ofs:=Ptrofs.add offset(Ptrofs.repr(4*index))).
  - apply pointer_location_value;eapply actual_pair_element;[exact POINTER|exact INDEX|lia].
  - eapply deref_loc_value;[reflexivity|]. unfold Mem.loadv.
    rewrite Ptrofs.add_unsigned.
    rewrite(Ptrofs.unsigned_repr(4*index))by(change Ptrofs.max_unsigned with 18446744073709551615;lia).
    rewrite Ptrofs.unsigned_repr by(unfold Ptrofs.max_unsigned;pose proof(Ptrofs.unsigned_range offset);lia).
    rewrite zle_true by(change(Ptrofs.unsigned offset+4*index+4<=Ptrofs.modulus);lia);exact LOAD.
Qed.

Lemma actual_pair_limit(ge:Clight.genv)temporaries memory index:
  temporaries!_index=Some(Vint(Int.repr index))->0<=index<=2->
  expression_value ge empty_env temporaries memory pair_limit_expression
    (Vint(if zlt index 2 then Int.one else Int.zero)).
Proof.
  intros INDEX BOUND;apply old_expression_value;eapply value_binary.
  - apply value_temp;exact INDEX.
  - constructor.
  - change(Some(Val.of_bool(Int.ltu(Int.repr index)(Int.repr 2)))=
      Some(Vint(if zlt index 2 then Int.one else Int.zero))).
    unfold Int.ltu;rewrite Int.unsigned_repr by(change Int.max_unsigned with 4294967295;lia).
    change(Int.unsigned(Int.repr 2))with 2;destruct(zlt index 2);reflexivity.
Qed.

Lemma actual_pair_low(ge:Clight.genv)temporaries memory descriptor:
  temporaries!_t'5=Some(Vint(Int.repr descriptor))->0<=descriptor<=Int.max_signed->
  expression_value ge empty_env temporaries memory pair_low_expression
    (Vint(if zlt descriptor 4 then Int.one else Int.zero)).
Proof.
  intros DESCRIPTOR BOUND;apply old_expression_value;eapply value_binary.
  - apply value_temp;exact DESCRIPTOR.
  - constructor.
  - change(Some(Val.of_bool(Int.lt(Int.repr descriptor)(Int.repr 4)))=
      Some(Vint(if zlt descriptor 4 then Int.one else Int.zero))).
    unfold Int.lt;rewrite Int.signed_repr by(change Int.max_signed with 2147483647 in BOUND;
      change(-2147483648<=descriptor<=2147483647);lia).
    change(Int.signed(Int.repr 4))with 4;destruct(zlt descriptor 4);reflexivity.
Qed.
