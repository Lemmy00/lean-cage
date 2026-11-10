(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Source builtin addresses use the same actual program symbol binding. *)
From compcert Require Import Coqlib Maps Integers Values Memory Globalenvs Ctypes Ctypesdefs Clight.
Require Import LocalAccess.

Lemma gateway_global_address_expression(ge:Clight.genv)environment temporaries memory identifier ty object :
  environment!identifier=None ->Genv.find_symbol ge identifier=Some object ->
  expression_value ge environment temporaries memory(Eaddrof(Evar identifier ty)(tptr ty))(Vptr object Ptrofs.zero).
Proof.
  intros LOCAL SYMBOL.
  destruct(global_location_value ge environment temporaries memory identifier ty object LOCAL SYMBOL)as[REAL UNIQUE].
  split;[econstructor;exact REAL|].
  intros other EVALUATION;inversion EVALUATION;subst.
  - match goal with LOCATION:eval_lvalue _ _ _ _ _ _ _ _|-_=>
      destruct(UNIQUE _ _ _ LOCATION)as[BLOCK[OFFSET BITFIELD]];subst;reflexivity end.
  - match goal with LOCATION:eval_lvalue _ _ _ _(Eaddrof _ _)_ _ _|-_=>inversion LOCATION end.
Qed.
