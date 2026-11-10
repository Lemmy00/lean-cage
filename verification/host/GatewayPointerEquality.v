(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Pointer identity tests use live native object addresses. *)
From Stdlib Require Import ZArith Bool.
From compcert Require Import Coqlib Integers Values Memory Ctypes Ctypesdefs Cop.
From HostGateway Require Import GatewaySource GatewayKeywordRuntime.

Lemma gateway_live_pointer_equality memory first second:
  gateway_keyword_nonempty_address memory first->gateway_keyword_nonempty_address memory second->
  sem_cmp Ceq first(tptr(Tstruct __typeobject noattr))second(tptr(Tstruct __typeobject noattr))memory=
    Some(Vint(if Val.eq first second then Int.one else Int.zero)).
Proof.
  intros[first_block[first_offset[FIRST FIRST_VALID]]][second_block[second_offset[SECOND SECOND_VALID]]].
  subst first second.
  assert(FIRST_WEAK:Mem.weak_valid_pointer memory first_block(Ptrofs.unsigned first_offset)=true)
    by(apply Mem.valid_pointer_implies;exact FIRST_VALID).
  assert(SECOND_WEAK:Mem.weak_valid_pointer memory second_block(Ptrofs.unsigned second_offset)=true)
    by(apply Mem.valid_pointer_implies;exact SECOND_VALID).
  change(option_map Val.of_bool(Val.cmplu_bool(Mem.valid_pointer memory)Ceq
    (Vptr first_block first_offset)(Vptr second_block second_offset))=
    Some(Vint(if Val.eq(Vptr first_block first_offset)(Vptr second_block second_offset)then Int.one else Int.zero))).
  change(option_map Val.of_bool
    (if eq_block first_block second_block then
      if Mem.weak_valid_pointer memory first_block(Ptrofs.unsigned first_offset)&&
        Mem.weak_valid_pointer memory second_block(Ptrofs.unsigned second_offset)
      then Some(Ptrofs.cmpu Ceq first_offset second_offset)else None
     else if Mem.valid_pointer memory first_block(Ptrofs.unsigned first_offset)&&
       Mem.valid_pointer memory second_block(Ptrofs.unsigned second_offset)then Some false else None)=
    Some(Vint(if Val.eq(Vptr first_block first_offset)(Vptr second_block second_offset)then Int.one else Int.zero))).
  destruct(eq_block first_block second_block)as[SAME|DIFFERENT].
  - subst second_block;rewrite FIRST_WEAK,SECOND_WEAK.
    change(Some(Val.of_bool(Ptrofs.eq first_offset second_offset))=
      Some(Vint(if Val.eq(Vptr first_block first_offset)(Vptr first_block second_offset)then Int.one else Int.zero))).
    destruct(Ptrofs.eq_dec first_offset second_offset)as[SAME|DIFFERENT].
    + subst second_offset;rewrite Ptrofs.eq_true.
      destruct(Val.eq(Vptr first_block first_offset)(Vptr first_block first_offset));[reflexivity|contradiction].
    + rewrite Ptrofs.eq_false by exact DIFFERENT.
      destruct(Val.eq(Vptr first_block first_offset)(Vptr first_block second_offset));[congruence|reflexivity].
  - rewrite FIRST_VALID,SECOND_VALID;cbn.
    destruct(Val.eq(Vptr first_block first_offset)(Vptr second_block second_offset));[congruence|reflexivity].
Qed.
