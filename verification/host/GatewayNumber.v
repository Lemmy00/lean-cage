(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: The real nine-digit native loop uses bounded
   exact arithmetic. *)
From Stdlib Require Import ZArith List Lia Ring.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Ctypesdefs Cop Clight.
Require Import LocalAccess CallAccess ClightSteps StoreSteps Readers.
From HostGateway Require Import GatewaySource GatewayObjects GatewayWordsMemory.
Import ListNotations.
Open Scope Z_scope.

Lemma gateway_decimal_append first rest :
  gateway_decimal_value(first++rest)=
    gateway_decimal_value first*10^Z.of_nat(length rest)+gateway_decimal_value rest.
Proof.
  induction first as[|byte first IH];[cbn;ring|].
  cbn[List.app gateway_decimal_value];rewrite length_app,Nat2Z.inj_add,Z.pow_add_r by lia.
  rewrite IH;ring.
Qed.

Lemma gateway_decimal_bounds bytes :
  Forall(fun byte=>48<=Byte.unsigned byte<=57)bytes ->
  0<=gateway_decimal_value bytes<10^Z.of_nat(length bytes).
Proof.
  intro DIGITS;induction DIGITS as[|byte rest DIGIT REST IH];[cbn;lia|].
  cbn[gateway_decimal_value length];rewrite Nat2Z.inj_succ,Z.pow_succ_r by lia.
  pose proof(Z.pow_pos_nonneg 10(Z.of_nat(length rest))ltac:(lia)ltac:(lia));nia.
Qed.

Theorem gateway_nine_digit_chunk_fits bytes :
  (length bytes<=9)%nat ->Forall(fun byte=>48<=Byte.unsigned byte<=57)bytes ->
  0<=gateway_decimal_value bytes<1000000000.
Proof.
  intros WIDTH DIGITS;pose proof(gateway_decimal_bounds bytes DIGITS)as RANGE.
  assert(POWER:10^Z.of_nat(length bytes)<=10^9).
  { apply Z.pow_le_mono_r;lia. }
  change(10^9)with 1000000000 in POWER;lia.
Qed.

Fixpoint gateway_number_sets (identifier:ident)(source:statement):list expr:=
  match source with
  |Sset actual expression=>if Pos.eqb identifier actual then[expression]else[]
  |Ssequence first second|Sifthenelse _ first second|Sloop first second=>
    gateway_number_sets identifier first++gateway_number_sets identifier second
  |Slabel _ body=>gateway_number_sets identifier body
  |_=>[]end.

Definition gateway_chunk_expression:=
  Ebinop Oadd(Ebinop Omul(Econst_int(Int.repr 10)tint)(Etempvar _chunk tulong)tulong)
    (Ecast(Ebinop Osub(Etempvar _t'23 tschar)(Econst_int(Int.repr 48)tint)tint)tulong)tulong.

Theorem gateway_actual_number_chunk_expressions :
  gateway_number_sets _chunk(fn_body f_host_json_number)=
    [Ecast(Econst_int Int.zero tint)tulong;gateway_chunk_expression].
Proof. vm_compute;reflexivity. Qed.

Lemma gateway_chunk_multiply ge environment temporaries memory accumulator :
  temporaries!_chunk=Some(Vlong(Int64.repr accumulator)) ->
  expression_value ge environment temporaries memory
    (Ebinop Omul(Econst_int(Int.repr 10)tint)(Etempvar _chunk tulong)tulong)
    (Vlong(Int64.repr(10*accumulator))).
Proof.
  intro ACCUMULATOR;eapply binary_expression_value.
  - apply old_expression_value;constructor.
  - apply old_expression_value,value_temp;exact ACCUMULATOR.
  - change (Some (Vlong (Int64.mul (Int64.repr 10) (Int64.repr accumulator))) =
      Some (Vlong (Int64.repr (10*accumulator)))).
    unfold Int64.mul;f_equal;f_equal;apply Int64.eqm_samerepr.
    apply Int64.eqm_mult;apply Int64.eqm_unsigned_repr_l;apply Int64.eqm_refl.
Qed.

Lemma gateway_chunk_digit ge environment temporaries memory digit :
  48<=digit<=57 ->temporaries!_t'23=Some(Vint(Int.repr digit)) ->
  expression_value ge environment temporaries memory
    (Ecast(Ebinop Osub(Etempvar _t'23 tschar)(Econst_int(Int.repr 48)tint)tint)tulong)
    (Vlong(Int64.repr(digit-48))).
Proof.
  intros DIGIT VALUE;eapply cast_expression_value with(v:=Vint(Int.repr(digit-48))).
  - eapply binary_expression_value.
    + apply old_expression_value,value_temp;exact VALUE.
    + apply old_expression_value;constructor.
    + change (Some (Vint (Int.sub (Int.repr digit) (Int.repr 48))) = Some (Vint (Int.repr (digit-48)))).
      unfold Int.sub;rewrite(Int.unsigned_repr digit)by
        (change(0<=digit<=4294967295);lia);reflexivity.
  - change (Some (Vlong (Int64.repr (Int.signed (Int.repr (digit-48))))) =
      Some (Vlong (Int64.repr (digit-48)))).
    rewrite Int.signed_repr;[reflexivity|change(-2147483648<=digit-48<=2147483647);lia].
Qed.

Theorem gateway_actual_chunk_step ge function environment temporaries memory continuation accumulator digit :
  48<=digit<=57 ->temporaries!_chunk=Some(Vlong(Int64.repr accumulator)) ->
  temporaries!_t'23=Some(Vint(Int.repr digit)) ->
  store_edge ge(State function(Sset _chunk gateway_chunk_expression)continuation environment temporaries memory)
    (State function Sskip continuation environment
      (PTree.set _chunk(Vlong(Int64.repr(10*accumulator+digit-48)))temporaries)memory).
Proof.
  intros DIGIT ACCUMULATOR BYTE;apply certified_set_edge.
  eapply binary_expression_value with(v:=Vlong(Int64.repr(10*accumulator)))(w:=Vlong(Int64.repr(digit-48))).
  - apply gateway_chunk_multiply;exact ACCUMULATOR.
  - apply gateway_chunk_digit;[exact DIGIT|exact BYTE].
  - change (Some (Vlong (Int64.add (Int64.repr (10*accumulator)) (Int64.repr (digit-48)))) =
      Some (Vlong (Int64.repr (10*accumulator+digit-48)))).
    unfold Int64.add;f_equal;f_equal;apply Int64.eqm_samerepr.
    replace(10*accumulator+digit-48)with(10*accumulator+(digit-48))by ring.
    apply Int64.eqm_add;apply Int64.eqm_unsigned_repr_l;apply Int64.eqm_refl.
Qed.

(* The generic signed-byte argument follows the accepted DigestWords byte proof;
   the resulting C expression is bound above to this maintained helper. *)
Lemma gateway_number_signed_ascii byte :
  Byte.unsigned byte<128 ->Int.sign_ext 8(Readers.byte_word byte)=Int.repr(Byte.unsigned byte).
Proof.
  intro ASCII.
  pose proof(Int.sign_ext_range 8(Readers.byte_word byte)ltac:(change(0<8<32);lia))as RANGE.
  pose proof(Int.eqmod_sign_ext 8(Readers.byte_word byte)ltac:(change(0<8<32);lia))as[quotient CONGRUENT].
  change(-128<=Int.signed(Int.sign_ext 8(Readers.byte_word byte))<128)in RANGE.
  unfold Readers.byte_word in CONGRUENT.
  rewrite Int.unsigned_repr in CONGRUENT by(pose proof(Byte.unsigned_range byte);
    change Byte.modulus with 256 in *;change Int.max_unsigned with 4294967295;lia).
  change(two_p 8)with 256 in CONGRUENT.
  pose proof(Byte.unsigned_range byte)as BYTE;change(0<=Byte.unsigned byte<256)in BYTE.
  assert(SIGNED:Int.signed(Int.sign_ext 8(Readers.byte_word byte))=Byte.unsigned byte)
    by(unfold Readers.byte_word in *;lia).
  rewrite<-(Int.repr_signed(Int.sign_ext 8(Readers.byte_word byte))),SIGNED;reflexivity.
Qed.

Lemma gateway_number_ascii_load memory block ofs bytes index byte :
  gateway_read_ready block ofs(map Readers.byte_word bytes)memory ->
  nth_error bytes index=Some byte ->Byte.unsigned byte<128 ->
  Mem.loadv Mint8signed memory(Vptr block(Ptrofs.add ofs(Ptrofs.repr(Z.of_nat index))))=
    Some(Vint(Int.repr(Byte.unsigned byte))).
Proof.
  intros READY SELECTED ASCII.
  specialize(READY index(Readers.byte_word byte)ltac:(rewrite nth_error_map,SELECTED;reflexivity)).
  unfold Mem.loadv in READY|-*;destruct(zle _ _);[|discriminate].
  rewrite Mem.load_int8_signed_unsigned,READY.
  change (Some (Vint (Int.sign_ext 8 (Readers.byte_word byte))) =
    Some (Vint (Int.repr (Byte.unsigned byte)))).
  rewrite gateway_number_signed_ascii by exact ASCII;reflexivity.
Qed.

Definition gateway_number_offset_test:=
  Ebinop Olt(Etempvar _offset tulong)(Etempvar _width tulong)tint.
Definition gateway_number_chunk_read:=
  Ederef(Ebinop Oadd(Etempvar _bytes(tptr tschar))
    (Ebinop Oadd(Etempvar _index tulong)(Etempvar _offset tulong)tulong)(tptr tschar))tschar.
Definition gateway_number_chunk_body:=Ssequence
  (Sifthenelse gateway_number_offset_test Sskip Sbreak)
  (Ssequence(Sset _t'23 gateway_number_chunk_read)(Sset _chunk gateway_chunk_expression)).
Definition gateway_number_chunk_increment:=Sset _offset
  (Ebinop Oadd(Etempvar _offset tulong)(Econst_int Int.one tint)tulong).
Definition gateway_number_chunk_loop:=Sloop gateway_number_chunk_body gateway_number_chunk_increment.

Definition gateway_is_chunk_loop source :bool:=
  match source with
  |Sloop(Ssequence(Sifthenelse(Ebinop Olt(Etempvar first _)(Etempvar second _)_)Sskip Sbreak)_)_=>
    Pos.eqb first _offset&&Pos.eqb second _width
  |_=>false end.
Fixpoint gateway_number_chunk_loops(source:statement):list statement:=
  (if gateway_is_chunk_loop source then[source]else[])++
  match source with
  |Ssequence first second|Sifthenelse _ first second|Sloop first second=>
    gateway_number_chunk_loops first++gateway_number_chunk_loops second
  |Slabel _ body=>gateway_number_chunk_loops body
  |_=>[]end.

Theorem gateway_actual_number_chunk_loop :
  gateway_number_chunk_loops(fn_body f_host_json_number)=[gateway_number_chunk_loop].
Proof. vm_compute;reflexivity. Qed.

Lemma gateway_number_long_add ge memory first second :
  sem_binary_operation ge Oadd(Vlong(Int64.repr first))tulong(Vlong(Int64.repr second))tulong memory=
    Some(Vlong(Int64.repr(first+second))).
Proof.
  change (Some (Vlong (Int64.add (Int64.repr first) (Int64.repr second))) =
    Some (Vlong (Int64.repr (first+second)))).
  unfold Int64.add;f_equal;f_equal;apply Int64.eqm_samerepr.
  apply Int64.eqm_add;apply Int64.eqm_unsigned_repr_l;apply Int64.eqm_refl.
Qed.

Lemma gateway_number_pointer_add ge memory block ofs index :
  0<=index<=65545 ->
  sem_binary_operation ge Oadd(Vptr block ofs)(tptr tschar)(Vlong(Int64.repr index))tulong memory=
    Some(Vptr block(Ptrofs.add ofs(Ptrofs.repr index))).
Proof.
  intro INDEX.
  change (Some (Vptr block (Ptrofs.add ofs
      (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_int64 (Int64.repr index))))) =
    Some (Vptr block (Ptrofs.add ofs (Ptrofs.repr index)))).
  unfold Ptrofs.of_int64,Ptrofs.mul.
  rewrite Int64.unsigned_repr by(change(0<=index<=18446744073709551615);lia).
  rewrite !Ptrofs.unsigned_repr by(change Ptrofs.max_unsigned with 18446744073709551615;lia).
  rewrite Z.mul_1_l;reflexivity.
Qed.

Theorem gateway_actual_chunk_character ge environment temporaries memory block ofs index offset digit :
  0<=index<=65536 ->0<=offset<=9 ->
  temporaries!_bytes=Some(Vptr block ofs) ->temporaries!_index=Some(Vlong(Int64.repr index)) ->
  temporaries!_offset=Some(Vlong(Int64.repr offset)) ->
  Mem.loadv Mint8signed memory(Vptr block(Ptrofs.add ofs(Ptrofs.repr(index+offset))))=Some(Vint digit) ->
  expression_value ge environment temporaries memory gateway_number_chunk_read(Vint digit).
Proof.
  intros INDEX OFFSET BYTES POSITION WITHIN LOAD.
  eapply location_read_value.
  - apply pointer_location_value;eapply binary_expression_value.
    + apply old_expression_value,value_temp;exact BYTES.
    + eapply binary_expression_value.
      * apply old_expression_value,value_temp;exact POSITION.
      * apply old_expression_value,value_temp;exact WITHIN.
      * apply gateway_number_long_add.
    + apply gateway_number_pointer_add;lia.
  - eapply deref_loc_value;[reflexivity|exact LOAD].
Qed.

Lemma gateway_number_offset_guard ge environment temporaries memory offset width :
  0<=offset<=9 ->0<=width<=9 ->
  temporaries!_offset=Some(Vlong(Int64.repr offset)) ->temporaries!_width=Some(Vlong(Int64.repr width)) ->
  expression_value ge environment temporaries memory gateway_number_offset_test
    (Vint(if zlt offset width then Int.one else Int.zero)).
Proof.
  intros OFFSET WIDTH POSITION LIMIT;eapply binary_expression_value.
  - apply old_expression_value,value_temp;exact POSITION.
  - apply old_expression_value,value_temp;exact LIMIT.
  - change (Some (Val.of_bool (Int64.ltu (Int64.repr offset) (Int64.repr width))) =
      Some (Vint (if zlt offset width then Int.one else Int.zero))).
    unfold Int64.ltu;rewrite !Int64.unsigned_repr by(change Int64.max_unsigned with 18446744073709551615;lia).
    destruct(zlt offset width);reflexivity.
Qed.

Lemma gateway_number_offset_increment ge memory offset :
  sem_binary_operation ge Oadd(Vlong(Int64.repr offset))tulong(Vint Int.one)tint memory=
    Some(Vlong(Int64.repr(offset+1))).
Proof.
  change (Some (Vlong (Int64.add (Int64.repr offset) (Int64.repr 1))) =
    Some (Vlong (Int64.repr (offset+1)))).
  unfold Int64.add;f_equal;f_equal;apply Int64.eqm_samerepr.
  apply Int64.eqm_add;apply Int64.eqm_unsigned_repr_l;apply Int64.eqm_refl.
Qed.

Definition gateway_number_chunk_next temporaries accumulator offset digit:=
  PTree.set _offset(Vlong(Int64.repr(offset+1)))
    (PTree.set _chunk(Vlong(Int64.repr(10*accumulator+digit-48)))
      (PTree.set _t'23(Vint(Int.repr digit))temporaries)).

Theorem gateway_actual_chunk_iteration ge environment temporaries memory continuation
    block ofs index width offset accumulator digit :
  0<=index<=65536 ->0<=offset<width ->width<=9 ->48<=digit<=57 ->
  temporaries!_bytes=Some(Vptr block ofs) ->temporaries!_index=Some(Vlong(Int64.repr index)) ->
  temporaries!_width=Some(Vlong(Int64.repr width)) ->temporaries!_offset=Some(Vlong(Int64.repr offset)) ->
  temporaries!_chunk=Some(Vlong(Int64.repr accumulator)) ->
  Mem.loadv Mint8signed memory(Vptr block(Ptrofs.add ofs(Ptrofs.repr(index+offset))))=
    Some(Vint(Int.repr digit)) ->
  store_path ge(fun _=>True)
    (State f_host_json_number gateway_number_chunk_loop continuation environment temporaries memory)11
    (State f_host_json_number gateway_number_chunk_loop continuation environment
      (gateway_number_chunk_next temporaries accumulator offset digit)memory).
Proof.
  intros INDEX OFFSET WIDTH DIGIT BYTES POSITION LIMIT WITHIN ACCUMULATOR LOAD.
  eapply store_next;[exact I|apply unchanged_store_edge,edge_loop|].
  eapply store_next;[exact I|apply unchanged_store_edge,edge_seq|].
  eapply store_next;[exact I|eapply certified_if_edge with(b:=true)|].
  - pose proof(gateway_number_offset_guard ge environment temporaries memory offset width
      ltac:(lia)ltac:(lia)WITHIN LIMIT)as TEST.
    rewrite zlt_true in TEST by lia;exact TEST.
  - reflexivity.
  - eapply store_next;[exact I|apply unchanged_store_edge,edge_skip_seq|].
    eapply store_next;[exact I|apply unchanged_store_edge,edge_seq|].
    eapply store_next;[exact I|apply certified_set_edge|].
    + eapply gateway_actual_chunk_character;try eassumption;lia.
    + eapply store_next;[exact I|apply unchanged_store_edge,edge_skip_seq|].
      eapply store_next;[exact I|apply gateway_actual_chunk_step with(accumulator:=accumulator)(digit:=digit)|].
      * exact DIGIT.
      * rewrite PTree.gso by discriminate;exact ACCUMULATOR.
      * apply PTree.gss.
      * eapply store_next;[exact I|apply unchanged_store_edge,edge_skip_loop1|].
        eapply store_next;[exact I|apply certified_set_edge|].
        -- eapply binary_expression_value.
           ++ apply old_expression_value,value_temp;repeat rewrite PTree.gso by discriminate;exact WITHIN.
           ++ apply old_expression_value;constructor.
           ++ apply gateway_number_offset_increment.
        -- eapply store_next;[exact I|apply unchanged_store_edge,edge_skip_loop2|].
           constructor;exact I.
Qed.

Fixpoint gateway_number_fold accumulator(bytes:list Byte.int):Z:=
  match bytes with
  |[]=>accumulator
  |byte::rest=>gateway_number_fold(10*accumulator+Byte.unsigned byte-48)rest end.

Lemma gateway_number_fold_exact bytes accumulator :
  gateway_number_fold accumulator bytes=
    accumulator*10^Z.of_nat(length bytes)+gateway_decimal_value bytes.
Proof.
  revert accumulator;induction bytes as[|byte rest IH];intro accumulator;[cbn;ring|].
  cbn[gateway_number_fold gateway_decimal_value length].
  rewrite IH,Nat2Z.inj_succ,Z.pow_succ_r by lia;ring.
Qed.

Theorem gateway_actual_chunk_argument_bounded bytes :
  (length bytes<=9)%nat ->Forall(fun byte=>48<=Byte.unsigned byte<=57)bytes ->
  Int64.unsigned(Int64.repr(gateway_number_fold 0 bytes))=gateway_decimal_value bytes /\
    0<=Int64.unsigned(Int64.repr(gateway_number_fold 0 bytes))<1000000000.
Proof.
  intros WIDTH DIGITS;pose proof(gateway_nine_digit_chunk_fits bytes WIDTH DIGITS)as BOUND.
  rewrite gateway_number_fold_exact;rewrite Z.mul_0_l,Z.add_0_l.
  rewrite Int64.unsigned_repr by(change Int64.max_unsigned with 18446744073709551615;lia).
  split;[reflexivity|exact BOUND].
Qed.

Definition gateway_number_chunk_state temporaries block ofs index width offset accumulator :Prop:=
  temporaries!_bytes=Some(Vptr block ofs) /\temporaries!_index=Some(Vlong(Int64.repr index)) /\
  temporaries!_width=Some(Vlong(Int64.repr width)) /\temporaries!_offset=Some(Vlong(Int64.repr offset)) /\
  temporaries!_chunk=Some(Vlong(Int64.repr accumulator)).

Lemma gateway_number_chunk_next_state temporaries block ofs index width offset accumulator digit :
  gateway_number_chunk_state temporaries block ofs index width offset accumulator ->
  gateway_number_chunk_state(gateway_number_chunk_next temporaries accumulator offset digit)
    block ofs index width(offset+1)(10*accumulator+digit-48).
Proof.
  intros[BYTES[INDEX[WIDTH[OFFSET ACCUMULATOR]]]].
  unfold gateway_number_chunk_state,gateway_number_chunk_next;repeat split.
  all:repeat rewrite PTree.gso by discriminate;try apply PTree.gss;assumption.
Qed.

Theorem gateway_actual_chunk_exit ge environment temporaries memory continuation width :
  0<=width<=9 ->temporaries!_width=Some(Vlong(Int64.repr width)) ->
  temporaries!_offset=Some(Vlong(Int64.repr width)) ->
  store_path ge(fun _=>True)
    (State f_host_json_number gateway_number_chunk_loop continuation environment temporaries memory)5
    (State f_host_json_number Sskip continuation environment temporaries memory).
Proof.
  intros WIDTH LIMIT POSITION.
  eapply store_next;[exact I|apply unchanged_store_edge,edge_loop|].
  eapply store_next;[exact I|apply unchanged_store_edge,edge_seq|].
  eapply store_next;[exact I|eapply certified_if_edge with(b:=false)|].
  - pose proof(gateway_number_offset_guard ge environment temporaries memory width width
      WIDTH WIDTH POSITION LIMIT)as TEST;rewrite zlt_false in TEST by lia;exact TEST.
  - reflexivity.
  - eapply store_next;[exact I|apply unchanged_store_edge,edge_break_seq|].
    eapply store_next;[exact I|apply unchanged_store_edge,edge_break_loop1|].
    constructor;exact I.
Qed.
