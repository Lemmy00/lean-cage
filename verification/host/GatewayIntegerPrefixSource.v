(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual leading-zero and sign checks establish the same bounded
   digit-loop frontier, retaining the exact received bytes and source temporaries. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayValueEntry GatewayValueExpressions GatewayScalarContext
  GatewayScalarLength GatewayScalarTerminate GatewayScalarBytesPath GatewayIntegerCanonical GatewayIntegerLoop GatewayIntegerMemory
  GatewayIntegerPrefix GatewaySourceSegments GatewaySourceDynamic GatewayUnaryExpressions GatewayFramedRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_integer_loop_cont:=Kseq gateway_integer_after_loop
  (Kseq gateway_scalar_cleanup(Kseq gateway_value_after_scalar Kstop)).

Ltac gateway_integer_prefix_reduce :=
  cbn -[Int64.eq Int64.ltu Int64.unsigned Int64.repr Int64.sub Int.eq Int.signed Int.repr Int.lt
    Byte.eq Byte.signed Z.of_nat];
  repeat rewrite Nat2Z.inj_succ;
  repeat rewrite Int.signed_repr by(change Int.min_signed with (-2147483648);change Int.max_signed with 2147483647;lia);
  try unfold Int64.sub;
  repeat rewrite Int64.unsigned_repr by(change Int64.max_unsigned with 18446744073709551615;lia);
  change Int64.zero with(Int64.repr 0);
  change Int64.one with(Int64.repr 1);
  repeat first[
    rewrite gateway_integer_small_equal by lia|
    rewrite gateway_integer_word_equal by lia|
    rewrite gateway_integer_word_less by lia];
  repeat match goal with |-context[Z.eqb(Byte.signed ?character)?constant]=>
    rewrite<-(gateway_integer_signed_equal character constant)by lia end;
  repeat match goal with H:Byte.eq _ _=_|-_=>progress(rewrite H)end;
  repeat match goal with
  | |-context[Z.eqb ?first ?second]=>first[
      rewrite(proj2(Z.eqb_eq first second)ltac:(lia))|
      rewrite(proj2(Z.eqb_neq first second)ltac:(lia))]
  | |-context[Z.ltb ?first ?second]=>first[
      rewrite(proj2(Z.ltb_lt first second)ltac:(lia))|
      rewrite(proj2(Z.ltb_ge first second)ltac:(lia))]
  end;
  repeat rewrite Int.eq_true;
  try rewrite(Int.eq_false Int.one Int.zero Int.one_not_zero);
  reflexivity.

Ltac gateway_integer_prefix_byte_load byte_list buffer_block position character memory world good loads :=
  eapply(loads(Z.to_nat position)character);
    [vm_compute;reflexivity|exact good].

Ltac gateway_integer_prefix_loads byte_list buffer_block loads bytes_parameter :=
  lazymatch goal with
  | |-expression_value _ _ _ _ (Evar _tag _) _=>apply gateway_value_tag_expression;eauto
  | |-expression_value _ _ _ _ (Evar _size _) _=>apply gateway_value_size_expression;eauto
  | |-expression_value ?ge ?environment ?parameters ?memory
      (Ederef(Ebinop Oadd _(Econst_int ?literal_index _)_)_) _=>
    let selected_index:=eval vm_compute in(Int.signed literal_index)in
    let selected:=eval vm_compute in(nth_error byte_list(Z.to_nat selected_index))in
    lazymatch selected with Some ?character=>
      eapply gateway_integer_fixed_character with(index:=selected_index)(byte:=character)(object:=buffer_block);
        [lia|unfold gateway_scalar_terminated_parameters,set_opttemp;repeat rewrite PTree.gso by discriminate;exact bytes_parameter|
          match goal with GOOD:?property memory ?world|-_=>
            gateway_integer_prefix_byte_load byte_list buffer_block selected_index character memory world GOOD loads end]
    end
  | |-expression_value ?ge ?environment ?parameters ?memory
      (Ederef(Ebinop Oadd _(Etempvar _start _)_)_) _=>
    first[
      let selected:=eval cbn[nth_error]in(nth_error byte_list 0%nat)in
      lazymatch selected with Some ?character=>
        eapply gateway_integer_temporary_character with(identifier:=_start)(index:=0)(byte:=character)(object:=buffer_block);
          [lia|unfold gateway_scalar_terminated_parameters,set_opttemp;repeat rewrite PTree.gso by discriminate;exact bytes_parameter|
            repeat rewrite PTree.gso by discriminate;rewrite PTree.gss;reflexivity|
            match goal with GOOD:?property memory ?world|-_=>
              gateway_integer_prefix_byte_load byte_list buffer_block 0 character memory world GOOD loads end]
      end|
      let selected:=eval cbn[nth_error]in(nth_error byte_list 1%nat)in
      lazymatch selected with Some ?character=>
        eapply gateway_integer_temporary_character with(identifier:=_start)(index:=1)(byte:=character)(object:=buffer_block);
          [lia|unfold gateway_scalar_terminated_parameters,set_opttemp;repeat rewrite PTree.gso by discriminate;exact bytes_parameter|
            repeat rewrite PTree.gso by discriminate;rewrite PTree.gss;reflexivity|
            match goal with GOOD:?property memory ?world|-_=>
              gateway_integer_prefix_byte_load byte_list buffer_block 1 character memory world GOOD loads end]
      end]
  | |-expression_value _ _ _ _ (Eunop _ _ _) _=>
    eapply gateway_unary_expression_value;
      [gateway_integer_dynamic_expression
        ltac:(fun _=>gateway_integer_prefix_loads byte_list buffer_block loads bytes_parameter)
        ltac:(fun _=>gateway_integer_prefix_reduce)|gateway_integer_prefix_reduce]
  | _=>match goal with |-?GOAL=>idtac "UNHANDLED PREFIX LOAD" GOAL;fail 1 end
  end.

Ltac gateway_integer_prefix_to_loop closed loads reduce :=
  lazymatch goal with
  | |-gateway_source_segment _ _ _ (State ?function ?body ?continuation ?environment ?parameters ?memory)_ _=>
    let statement:=eval hnf in body in
    lazymatch statement with
    |(if ?flag then ?yes else ?no)=>
      let decision:=fresh "PREFIX_DECISION" in
      tryif(assert(decision:flag=true)by gateway_integer_prefix_reduce)
      then(rewrite decision;gateway_integer_prefix_to_loop closed loads reduce)
      else(assert(decision:flag=false)by gateway_integer_prefix_reduce;
        rewrite decision;gateway_integer_prefix_to_loop closed loads reduce)
    |Sloop _ _=>apply gateway_segment_here
    |Ssequence ?first ?rest=>
      eapply gateway_segment_same with(next:=State function first(Kseq rest continuation)environment parameters memory);
        [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|
          gateway_integer_prefix_to_loop closed loads reduce]
    |Sskip=>lazymatch continuation with
      |Kseq ?following ?rest=>
        eapply gateway_segment_same with(next:=State function following rest environment parameters memory);
          [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|
            gateway_integer_prefix_to_loop closed loads reduce]
      |Kloop1 ?first ?second ?rest=>
        eapply gateway_segment_same with(next:=State function second(Kloop2 first second rest)environment parameters memory);
          [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_loop1|
            gateway_integer_prefix_to_loop closed loads reduce]
      |Kloop2 ?first ?second ?rest=>
        eapply gateway_segment_same with(next:=State function(Sloop first second)rest environment parameters memory);
          [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_loop2|
            gateway_integer_prefix_to_loop closed loads reduce]
      end
    |Sset ?identifier ?expression=>
      let result:=open_constr:(_ : Values.val)in
      eapply gateway_segment_same with(next:=State function Sskip continuation environment(PTree.set identifier result parameters)memory);
        [exact closed|cbn;tauto|intros;apply certified_set_edge;gateway_integer_dynamic_expression loads reduce|
          gateway_integer_prefix_to_loop closed loads reduce]
    |Sifthenelse ?expression ?yes ?no=>
      let flag:=open_constr:(_ : bool)in
      eapply gateway_segment_same with(next:=State function(if flag then yes else no)continuation environment parameters memory);
        [exact closed|cbn;tauto|intros;eapply certified_if_edge;
          [gateway_integer_dynamic_expression loads reduce|reduce ()]|
          gateway_integer_prefix_to_loop closed loads reduce]
    | _=>idtac "UNHANDLED STATEMENT" statement;fail 1
    end
  | _=>match goal with |-?GOAL=>idtac "UNHANDLED SEGMENT GOAL" GOAL;fail 1 end
  end.

Theorem gateway_integer_actual_prefix {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)slots parameters object bytes memory:
  gateway_ambient_closed backend property->Z.of_nat(length bytes)<=32->parameters!_bytes=Some(Vptr object Ptrofs.zero)->
  (forall memory world,property memory world->Mem.loadv Mint64 memory(Vptr(gateway_value_tag_slot slots)Ptrofs.zero)=Some(Vlong(Int64.repr 3)))->
  (forall memory world,property memory world->Mem.loadv Mint64 memory(Vptr(gateway_value_size_slot slots)Ptrofs.zero)=Some(Vlong(Int64.repr(Z.of_nat(length bytes)))))->
  (forall index byte,nth_error bytes index=Some byte->forall memory world,property memory world->
    Mem.loadv Mint8signed memory(Vptr object(Ptrofs.repr(Z.of_nat index)))=Some(Vint(Int.repr(Byte.signed byte))))->
  exists loop_parameters,
    gateway_source_segment backend ge property
      (gateway_scalar_terminated_state slots(Int64.repr(Z.of_nat(length bytes)))parameters memory)
      (State f_host_value gateway_integer_loop gateway_integer_loop_cont(gateway_value_environment slots)loop_parameters memory)property /\
    loop_parameters!_bytes=Some(Vptr object Ptrofs.zero) /\loop_parameters!_value=Some Vnullptr /\
    loop_parameters!_start=Some(Vlong(Int64.repr(gateway_integer_start bytes))) /\
    loop_parameters!_index=Some(Vlong(Int64.repr(gateway_integer_start bytes))) /\
    loop_parameters!_valid=Some(Vint(if gateway_integer_initial_flag bytes then Int.one else Int.zero)).
Proof.
  intros CLOSED BOUND BYTES TAG SIZE LOADS.
  destruct bytes as[|first[|second[|third rest]]].
  all:try(destruct(Byte.eq first(Byte.repr 45))eqn:SIGN;destruct(Byte.eq first(Byte.repr 48))eqn:ZERO).
  all:try(destruct(Byte.eq second(Byte.repr 48))eqn:SECOND_ZERO).
  all:try solve[pose proof(Byte.same_if_eq _ _ SIGN)as FIRST45;pose proof(Byte.same_if_eq _ _ ZERO)as FIRST48;
    rewrite FIRST45 in FIRST48;apply(f_equal Byte.unsigned)in FIRST48;vm_compute in FIRST48;discriminate].
  all:try(pose proof(gateway_integer_signed_range first)as FIRST_RANGE).
  all:try(pose proof(gateway_integer_signed_range second)as SECOND_RANGE).
  all:cbn[length]in BOUND;repeat rewrite Nat2Z.inj_succ in BOUND.
  all:eexists;split.
  all:lazymatch goal with |-gateway_source_segment _ _ _ _ _ _=>
    let selected:=lazymatch type of LOADS with
      |forall index byte,nth_error ?source index=Some byte->_=>constr:(source)end in
    unfold gateway_scalar_terminated_state;
    gateway_integer_prefix_to_loop CLOSED
      ltac:(fun _=>gateway_integer_prefix_loads selected object LOADS BYTES)
      ltac:(fun _=>gateway_integer_prefix_reduce)
  |_=>idtac end.
  all:repeat split;unfold gateway_scalar_terminated_parameters,set_opttemp;
    repeat rewrite PTree.gso by discriminate;try rewrite PTree.gss;try exact BYTES.
  all:unfold gateway_integer_start,gateway_integer_initial_flag,gateway_integer_digits,gateway_integer_negative,gateway_integer_head_check;
    cbn[tl length Nat.eqb];
    repeat match goal with H:Byte.eq _ _=_|-_=>progress(rewrite H)end;
    cbn[tl length Nat.eqb];
    repeat match goal with H:Byte.eq _ _=_|-_=>progress(rewrite H)end;
    repeat rewrite Int.eq_true;try rewrite(Int.eq_false Int.one Int.zero Int.one_not_zero);reflexivity.
Qed.
