(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual bounded integer loop checks every received byte;
   its source controls retain the same native memory under arbitrary permitted interleaving. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayValueEntry GatewayValueExpressions GatewayScalarContext GatewayScalarTerminate
  GatewayScalarBytesPath GatewaySourceSegments GatewaySourceDynamic GatewayFramedRuntime GatewayIntegerCanonical.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_integer_dispatch:=match gateway_scalar_after_terminator with
  Ssequence _(Ssequence dispatch _)=>dispatch|_=>Sskip end.
Definition gateway_integer_branch:=match gateway_integer_dispatch with
  Ssequence _(Sifthenelse _ body _)=>body|_=>Sskip end.
Definition gateway_integer_after_start:=match gateway_integer_branch with Ssequence _ rest=>rest|_=>Sskip end.
Definition gateway_integer_after_valid:=match gateway_integer_after_start with Ssequence _ rest=>rest|_=>Sskip end.
Definition gateway_integer_loop_setup:=match gateway_integer_after_valid with Ssequence first _=>first|_=>Sskip end.
Definition gateway_integer_after_loop:=match gateway_integer_after_valid with Ssequence _ rest=>rest|_=>Sskip end.
Definition gateway_integer_loop:=match gateway_integer_loop_setup with Ssequence _ loop=>loop|_=>Sskip end.
Definition gateway_integer_loop_body:=match gateway_integer_loop with Sloop body _=>body|_=>Sskip end.
Definition gateway_integer_loop_increment:=match gateway_integer_loop with Sloop _ increment=>increment|_=>Sskip end.

Lemma gateway_integer_loop_actual:
  gateway_integer_loop=Sloop
    (Ssequence
      (Ssequence(Sset _t'67(Evar _size tulong))
        (Sifthenelse(Ebinop Olt(Etempvar _index tulong)(Etempvar _t'67 tulong)tint)Sskip Sbreak))
      (Ssequence
        (Ssequence(Sset _t'65(Ederef(Ebinop Oadd(Etempvar _bytes(tptr tschar))(Etempvar _index tulong)(tptr tschar))tschar))
          (Sifthenelse(Ebinop Olt(Etempvar _t'65 tschar)(Econst_int(Int.repr 48)tint)tint)
            (Sset _t'18(Econst_int Int.one tint))
            (Ssequence(Sset _t'66(Ederef(Ebinop Oadd(Etempvar _bytes(tptr tschar))(Etempvar _index tulong)(tptr tschar))tschar))
              (Sset _t'18(Ecast(Ebinop Ogt(Etempvar _t'66 tschar)(Econst_int(Int.repr 57)tint)tint)tbool)))))
        (Sifthenelse(Etempvar _t'18 tint)(Sset _valid(Econst_int Int.zero tint))Sskip)))
    (Sset _index(Ebinop Oadd(Etempvar _index tulong)(Econst_int Int.one tint)tulong)).
Proof. vm_compute;reflexivity. Qed.

Lemma gateway_integer_signed_range byte:-128<=Byte.signed byte<=127.
Proof. pose proof(Byte.signed_range byte);change Byte.min_signed with (-128)in H;change Byte.max_signed with 127 in H;lia. Qed.
Lemma gateway_integer_signed_digit byte:
  (48<=Byte.signed byte<=57)<->(48<=Byte.unsigned byte<=57).
Proof.
  unfold Byte.signed;pose proof(Byte.unsigned_range byte)as BOUND.
  change Byte.half_modulus with 128;change Byte.modulus with 256 in *.
  destruct(zlt(Byte.unsigned byte)128);split;intros;lia.
Qed.

Lemma gateway_integer_digit_signed byte:
  gateway_integer_digit byte=((48<=?Byte.signed byte)&&(Byte.signed byte<=?57)).
Proof.
  assert(BOOL:forall first second:bool,(first=true<->second=true)->first=second).
  { intros[][];intuition discriminate. }
  apply BOOL;unfold gateway_integer_digit.
  rewrite !andb_true_iff,!Z.leb_le;apply iff_sym;apply gateway_integer_signed_digit.
Qed.

Lemma gateway_integer_character ge environment parameters memory object index byte:
  0<=index<=32->parameters!_bytes=Some(Vptr object Ptrofs.zero)->
  parameters!_index=Some(Vlong(Int64.repr index))->
  Mem.loadv Mint8signed memory(Vptr object(Ptrofs.repr index))=Some(Vint(Int.repr(Byte.signed byte)))->
  expression_value ge environment parameters memory
    (Ederef(Ebinop Oadd(Etempvar _bytes(tptr tschar))(Etempvar _index tulong)(tptr tschar))tschar)
    (Vint(Int.repr(Byte.signed byte))).
Proof.
  intros INDEX BYTES POSITION LOAD.
  eapply location_read_value with(b:=object)(ofs:=Ptrofs.repr index).
  - apply pointer_location_value;eapply binary_expression_value with(v:=Vptr object Ptrofs.zero)(w:=Vlong(Int64.repr index)).
    + apply old_expression_value,value_temp;exact BYTES.
    + apply old_expression_value,value_temp;exact POSITION.
    + change(Some(Vptr object(Ptrofs.add Ptrofs.zero(Ptrofs.mul Ptrofs.one(Ptrofs.of_int64(Int64.repr index)))))=
        Some(Vptr object(Ptrofs.repr index))).
      rewrite Ptrofs.add_zero_l,Ptrofs.mul_commut,Ptrofs.mul_one.
      unfold Ptrofs.of_int64;rewrite Int64.unsigned_repr by(change Int64.max_unsigned with 18446744073709551615;lia);reflexivity.
  - apply deref_loc_value with(chunk:=Mint8signed);[reflexivity|exact LOAD].
Qed.

Ltac gateway_integer_dynamic_expression loads reduce :=
    lazymatch goal with
    | |- expression_value _ _ _ _ (Ebinop _ _ _ _) _=>
        eapply binary_expression_value;
          [gateway_integer_dynamic_expression loads reduce|gateway_integer_dynamic_expression loads reduce|reduce ()]
    | |- expression_value _ _ _ _ (Ecast _ _) _=>
        eapply cast_expression_value;[gateway_integer_dynamic_expression loads reduce|reduce ()]
    | |- expression_value _ _ _ _ (Econst_int _ _) _=>apply old_expression_value;apply value_int
    | |- expression_value _ _ _ _ (Etempvar _ _) _=>
        apply old_expression_value;apply value_temp;unfold set_opttemp;
          repeat rewrite PTree.gso by discriminate;first[apply PTree.gss|reflexivity|eassumption|match goal with |-?GOAL=>idtac "FAILED TEMP" GOAL;fail 1 end]
    | |- _=>loads ()
    end.

Ltac gateway_integer_segment_to_loop closed loads reduce :=
  lazymatch goal with
  | |-gateway_source_segment _ _ _ (State ?function ?body ?continuation ?environment ?parameters ?memory)_ _=>
    let statement:=eval hnf in body in
    lazymatch statement with
    |(if ?flag then ?yes else ?no)=>
      let selected:=eval vm_compute in flag in
      lazymatch selected with
      |true=>change body with yes;gateway_integer_segment_to_loop closed loads reduce
      |false=>change body with no;gateway_integer_segment_to_loop closed loads reduce
      end
    |Sloop _ _=>apply gateway_segment_here
    |Ssequence ?first ?rest=>
      eapply gateway_segment_same with(next:=State function first(Kseq rest continuation)environment parameters memory);
        [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_seq|
          gateway_integer_segment_to_loop closed loads reduce]
    |Sskip=>lazymatch continuation with
      |Kseq ?following ?rest=>
        eapply gateway_segment_same with(next:=State function following rest environment parameters memory);
          [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_seq|
            gateway_integer_segment_to_loop closed loads reduce]
      |Kloop1 ?first ?second ?rest=>
        eapply gateway_segment_same with(next:=State function second(Kloop2 first second rest)environment parameters memory);
          [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_loop1|
            gateway_integer_segment_to_loop closed loads reduce]
      |Kloop2 ?first ?second ?rest=>
        eapply gateway_segment_same with(next:=State function(Sloop first second)rest environment parameters memory);
          [exact closed|cbn;tauto|intros;apply unchanged_store_edge,edge_skip_loop2|
            gateway_integer_segment_to_loop closed loads reduce]
      end
    |Sset ?identifier ?expression=>
      let result:=open_constr:(_ : Values.val)in
      eapply gateway_segment_same with(next:=State function Sskip continuation environment(PTree.set identifier result parameters)memory);
        [exact closed|cbn;tauto|intros;apply certified_set_edge;gateway_integer_dynamic_expression loads reduce|
          gateway_integer_segment_to_loop closed loads reduce]
    |Sifthenelse ?expression ?yes ?no=>
      let flag:=open_constr:(_ : bool)in
      eapply gateway_segment_same with(next:=State function(if flag then yes else no)continuation environment parameters memory);
        [exact closed|cbn;tauto|intros;eapply certified_if_edge;
          [gateway_integer_dynamic_expression loads reduce|reduce ()]|
          gateway_integer_segment_to_loop closed loads reduce]
    | _=>idtac "UNHANDLED STATEMENT" statement;fail 1
    end
  | _=>match goal with |-?GOAL=>idtac "UNHANDLED SEGMENT GOAL" GOAL;fail 1 end
  end.

Theorem gateway_integer_loop_step {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)slots parameters continuation object index count(valid:bool)byte memory:
  gateway_ambient_closed backend property->0<=index /\index<count /\count<=32->
  parameters!_bytes=Some(Vptr object Ptrofs.zero)->parameters!_index=Some(Vlong(Int64.repr index))->
  parameters!_valid=Some(Vint(if valid then Int.one else Int.zero))->
  (forall memory world,property memory world->Mem.loadv Mint64 memory(Vptr(gateway_value_size_slot slots)Ptrofs.zero)=Some(Vlong(Int64.repr count)))->
  (forall memory world,property memory world->Mem.loadv Mint8signed memory(Vptr object(Ptrofs.repr index))=
    Some(Vint(Int.repr(Byte.signed byte))))->
  exists next_parameters,
    gateway_source_segment backend ge property
      (State f_host_value gateway_integer_loop continuation(gateway_value_environment slots)parameters memory)
      (State f_host_value gateway_integer_loop continuation(gateway_value_environment slots)next_parameters memory)property /\
    next_parameters!_bytes=Some(Vptr object Ptrofs.zero) /\
    next_parameters!_index=Some(Vlong(Int64.repr(index+1))) /\
    next_parameters!_valid=Some(Vint(if valid&&gateway_integer_digit byte then Int.one else Int.zero)).
Proof.
  intros CLOSED INDEX BYTES POSITION VALID SIZE CHARACTER.
  assert(LESS:Int64.ltu(Int64.repr index)(Int64.repr count)=true).
  { unfold Int64.ltu;rewrite !Int64.unsigned_repr by(change Int64.max_unsigned with 18446744073709551615;lia);apply zlt_true;lia. }
  destruct(zlt(Byte.signed byte)48)as[LOW|NOT_LOW];
    [|destruct(zlt 57(Byte.signed byte))as[HIGH|NOT_HIGH]];eexists;split.
  all:lazymatch goal with
  | |-gateway_source_segment _ _ _ _ _ _=>
    rewrite gateway_integer_loop_actual;
    eapply gateway_segment_same with(next:=State f_host_value gateway_integer_loop_body
      (Kloop1 gateway_integer_loop_body gateway_integer_loop_increment continuation)(gateway_value_environment slots)parameters memory);
      [exact CLOSED|cbn;tauto|intros;apply unchanged_store_edge,edge_loop|];
    unfold gateway_integer_loop_body,gateway_integer_loop_increment;
    gateway_integer_segment_to_loop CLOSED
      ltac:(fun _=>first[apply gateway_value_size_expression;eapply SIZE;eassumption|
        eapply gateway_integer_character with(index:=index)(byte:=byte)(object:=object);[lia|repeat rewrite PTree.gso by discriminate;exact BYTES|
          repeat rewrite PTree.gso by discriminate;exact POSITION|eapply CHARACTER;eassumption]|
        match goal with |-?GOAL=>idtac "UNHANDLED LOAD" GOAL;fail 1 end])
      ltac:(fun _=>cbn -[Int64.ltu Int64.unsigned Int64.repr Int64.add Int.signed Int.repr Int.lt];unfold Int.lt;
        repeat rewrite Int.signed_repr by(pose proof(gateway_integer_signed_range byte);
          change Int.min_signed with (-2147483648);change Int.max_signed with 2147483647;lia);
        try rewrite LESS;
        repeat first[rewrite zlt_true by lia|rewrite zlt_false by lia];
        first[reflexivity|match goal with |-?GOAL=>idtac "UNHANDLED REDUCE" GOAL;fail 1 end])
  | _=>idtac end.
  all:repeat split;try solve[repeat rewrite PTree.gso by discriminate;exact BYTES].
  all:repeat rewrite PTree.gso by discriminate;try rewrite PTree.gss.
  all:try solve[rewrite Int64.add_unsigned;rewrite !Int64.unsigned_repr by
    (change Int64.max_unsigned with 18446744073709551615;lia);reflexivity].
  all:rewrite gateway_integer_digit_signed.
  all:destruct(48<=?Byte.signed byte)eqn:FROM;destruct(Byte.signed byte<=?57)eqn:TO;
    first[apply Z.leb_le in FROM|apply Z.leb_gt in FROM];
    first[apply Z.leb_le in TO|apply Z.leb_gt in TO];try lia;cbn;
    destruct valid;first[reflexivity|exact VALID].
Qed.
