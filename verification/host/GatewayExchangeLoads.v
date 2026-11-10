(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Spawn arguments use the actual initialized local endpoint cells. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps LocalAccess.
From HostGateway Require Import GatewaySource GatewayExchangeSetup GatewayPairContext GatewayPairMemory.
Import ListNotations.
Open Scope Z_scope.

Definition exchange_endpoint_element identifier index:=
  Ebinop Oadd(Evar identifier(tarray tint 2))(Econst_int(Int.repr index)tint)(tptr tint).

Theorem actual_exchange_endpoint_element(ge:Clight.genv)environment temporaries memory identifier object index:
  environment!identifier=Some(object,tarray tint 2)->0<=index<2->
  expression_value ge environment temporaries memory(exchange_endpoint_element identifier index)
    (Vptr object(Ptrofs.repr(4*index))).
Proof.
  intros ARRAY RANGE;eapply binary_expression_value with(v:=Vptr object Ptrofs.zero)(w:=Vint(Int.repr index)).
  - apply exchange_endpoint_reference;exact ARRAY.
  - apply old_expression_value;constructor.
  - assert(index=0\/index=1)by lia;destruct H;subst index;reflexivity.
Qed.

Theorem actual_exchange_endpoint_load(ge:Clight.genv)environment temporaries memory identifier object left right index:
  environment!identifier=Some(object,tarray tint 2)->gateway_pair_cells memory object Ptrofs.zero left right->0<=index<2->
  expression_value ge environment temporaries memory(Ederef(exchange_endpoint_element identifier index)tint)
    (Vint(Int.repr(pair_slot_value index left right))).
Proof.
  intros ARRAY CELLS RANGE;eapply location_read_value with(b:=object)(ofs:=Ptrofs.repr(4*index)).
  - apply pointer_location_value;apply actual_exchange_endpoint_element;assumption.
  - eapply deref_loc_value;[reflexivity|].
    pose proof(gateway_pair_selected_load memory object Ptrofs.zero left right index CELLS RANGE)as LOAD.
    assert(index=0\/index=1)by lia;destruct H;subst index;exact LOAD.
Qed.
