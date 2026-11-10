(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: Checked positive native counts advance exactly the acknowledged span. *)
From Stdlib Require Import ZArith Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Ctypesdefs Cop Clight.
Require Import ClightSteps LocalAccess.
From HostGateway Require Import GatewaySource GatewayTransferMath.
Open Scope Z_scope.

Lemma actual_positive_count_not_negative ge environment temporaries memory count :
  0<count<=65536 ->temporaries!_count=Some(Vlong(Int64.repr count)) ->
  expression_value ge environment temporaries memory
    (Ebinop Olt(Etempvar _count tlong)(Econst_int Int.zero tint)tint)(Vint Int.zero).
Proof.
  intros COUNT LOOK;apply old_expression_value;eapply value_binary.
  - apply value_temp;exact LOOK.
  - constructor.
  - change(Some(Val.of_bool(Int64.lt(Int64.repr count)Int64.zero))=Some(Vint Int.zero)).
    unfold Int64.lt;rewrite(proj1(transfer_positive_signed_count count COUNT)),Int64.signed_zero.
    destruct(zlt count 0);[lia|reflexivity].
Qed.

Lemma actual_positive_count_not_zero ge environment temporaries memory count :
  0<count<=65536 ->temporaries!_count=Some(Vlong(Int64.repr count)) ->
  expression_value ge environment temporaries memory
    (Ebinop Ole(Etempvar _count tlong)(Econst_int Int.zero tint)tint)(Vint Int.zero).
Proof.
  intros COUNT LOOK;apply old_expression_value;eapply value_binary.
  - apply value_temp;exact LOOK.
  - constructor.
  - change(Some(Val.of_bool(negb(Int64.lt Int64.zero(Int64.repr count))))=Some(Vint Int.zero)).
    unfold Int64.lt;rewrite(proj1(transfer_positive_signed_count count COUNT)),Int64.signed_zero.
    destruct(zlt 0 count);[reflexivity|lia].
Qed.

Lemma actual_count_inside_chunk ge environment temporaries memory count amount :
  0<count<=amount ->amount<=65536 ->
  temporaries!_count=Some(Vlong(Int64.repr count)) ->temporaries!_amount=Some(Vlong(Int64.repr amount)) ->
  expression_value ge environment temporaries memory
    (Ecast(Ebinop Ogt(Ecast(Etempvar _count tlong)tulong)(Etempvar _amount tulong)tint)tbool)(Vint Int.zero).
Proof.
  intros COUNT AMOUNT COUNT_LOOK AMOUNT_LOOK.
  apply cast_expression_value with(v:=Vint Int.zero);[|reflexivity].
  apply old_expression_value;eapply value_binary.
  - eapply value_cast;[apply value_temp;exact COUNT_LOOK|reflexivity].
  - apply value_temp;exact AMOUNT_LOOK.
  - change(Some(Val.of_bool(Int64.ltu(Int64.repr amount)(Int64.repr count)))=Some(Vint Int.zero)).
    unfold Int64.ltu;rewrite !Int64.unsigned_repr by(change Int64.max_unsigned with 18446744073709551615;lia).
    destruct(zlt amount count);[lia|reflexivity].
Qed.

Lemma actual_cursor_advance ge environment temporaries memory count block offset :
  0<count<=65536 ->temporaries!_count=Some(Vlong(Int64.repr count)) ->
  temporaries!_cursor=Some(Vptr block offset) ->
  expression_value ge environment temporaries memory
    (Ebinop Oadd(Etempvar _cursor(tptr tuchar))(Etempvar _count tlong)(tptr tuchar))
    (Vptr block(Ptrofs.add offset(Ptrofs.repr count))).
Proof.
  intros COUNT COUNT_LOOK CURSOR_LOOK;apply old_expression_value;eapply value_binary.
  - apply value_temp;exact CURSOR_LOOK.
  - apply value_temp;exact COUNT_LOOK.
  - change (Some (Vptr block
      (Ptrofs.add offset (Ptrofs.mul Ptrofs.one (Ptrofs.of_int64 (Int64.repr count))))) =
      Some (Vptr block (Ptrofs.add offset (Ptrofs.repr count)))).
    rewrite Ptrofs.mul_commut,Ptrofs.mul_one.
    unfold Ptrofs.of_int64;rewrite Int64.unsigned_repr by(change Int64.max_unsigned with 18446744073709551615;lia).
    reflexivity.
Qed.

Lemma actual_size_decrement ge environment temporaries memory size count :
  0<=size<=Int64.max_unsigned ->0<count<=size ->
  temporaries!_size=Some(Vlong(Int64.repr size)) ->temporaries!_count=Some(Vlong(Int64.repr count)) ->
  expression_value ge environment temporaries memory
    (Ebinop Osub(Etempvar _size tulong)(Ecast(Etempvar _count tlong)tulong)tulong)
    (Vlong(Int64.repr(size-count))).
Proof.
  intros SIZE COUNT SIZE_LOOK COUNT_LOOK;apply old_expression_value;eapply value_binary.
  - apply value_temp;exact SIZE_LOOK.
  - eapply value_cast;[apply value_temp;exact COUNT_LOOK|reflexivity].
  - change(Some(Vlong(Int64.sub(Int64.repr size)(Int64.repr count)))=Some(Vlong(Int64.repr(size-count)))).
    unfold Int64.sub;rewrite !Int64.unsigned_repr by lia;reflexivity.
Qed.
