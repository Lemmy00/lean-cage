(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: Successful actual iterations either advance bytes or retry a recognized error. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayTransferSource GatewayTransferErrno
  GatewayTransferFailure GatewayTransferErrors GatewayTransferUndefined.
Import ListNotations.
Open Scope Z_scope.

Lemma gateway_mint32_load_shape memory object offset value :
  Mem.loadv Mint32 memory(Vptr object offset)=Some value ->
  value=Vundef \/exists integer,value=Vint integer.
Proof.
  intro LOAD;cbn[Mem.loadv]in LOAD.
  destruct(zle(Ptrofs.unsigned offset+size_chunk Mint32)Ptrofs.modulus);[|discriminate].
  pose proof(Mem.load_type _ _ _ _ _ LOAD)as TYPE.
  destruct value;cbn[Val.has_type type_of_chunk]in TYPE;try contradiction;
    [left;reflexivity|right;eexists;reflexivity|discriminate TYPE].
Qed.

Lemma actual_captured_errno_shape ge environment temporaries memory pointer value :
  eval_expr ge environment temporaries memory(Ederef pointer tint)value ->
  value=Vundef \/exists integer,value=Vint integer.
Proof.
  intro VALUE;inversion VALUE;subst.
  match goal with LOCATION:eval_lvalue _ _ _ _(Ederef _ _) _ _ _|-_=>inversion LOCATION;subst end.
  match goal with LOAD:deref_loc _ _ _ _ _ _|-_=>inversion LOAD;subst;try discriminate end.
  match goal with CHUNK:access_mode _=By_value _|-_=>
    cbn[typeof access_mode]in CHUNK;inversion CHUNK;subst end.
  eapply gateway_mint32_load_shape;eassumption.
Qed.

Theorem actual_successful_receive_iteration_classified {World Event}(backend:gateway_backend World Event)ge
    temporaries count chunk number before world events after next :
  -1<=count<=chunk ->temporaries!_count=Some(Vlong(Int64.repr count)) ->temporaries!_number=Some number ->
  (number=Vundef \/exists integer,number=Vint integer) ->
  gateway_steps backend ge
    (gateway_live(State f_host_transfer transfer_after_restore transfer_iteration_cont empty_env temporaries before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next) ->
  0<count<=chunk \/count= -1 /\exists integer,number=Vint integer /\
    (integer=Int.repr 4 \/integer=Int.repr 11).
Proof.
  intros BOUND COUNT NUMBER TYPE RUN.
  destruct(Z_lt_ge_dec 0 count)as[POSITIVE|NONPOSITIVE];[left;lia|].
  destruct(Z.eq_dec count 0)as[ZERO|NEGATIVE].
  - subst count.
    pose proof(actual_zero_count_returns_failure backend ge temporaries before world events(Vint Int.zero)after next COUNT RUN)
      as BAD;discriminate BAD.
  - assert(MINUS:count= -1)by lia;subst count.
    destruct TYPE as[UNDEFINED|[integer INTEGER]].
    + subst number;exfalso;eapply actual_negative_undefined_errno_cannot_return;
        [exact COUNT|exact NUMBER|exact RUN].
    + subst number.
      destruct(Int.eq_dec integer(Int.repr 4))as[FOUR|NOT_FOUR];
        [right;split;[reflexivity|exists integer;auto]|].
      destruct(Int.eq_dec integer(Int.repr 11))as[ELEVEN|NOT_ELEVEN];
        [right;split;[reflexivity|exists integer;auto]|].
      pose proof(actual_negative_nonretry_returns_failure backend ge temporaries integer before world events
        (Vint Int.zero)after next COUNT NUMBER NOT_FOUR NOT_ELEVEN RUN)as BAD;discriminate BAD.
Qed.
