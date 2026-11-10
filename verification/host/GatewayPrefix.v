(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.acceptance: Start at the real C call and derive the first exact API request. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs
  Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayPython GatewayAllocation.
Import ListNotations.
Open Scope Z_scope.

Definition field_api_test :=
  match fn_body f_host_field_bytes with
  | Ssequence(Ssequence _ test)_ => test
  | _ => Sskip
  end.

Definition field_after_api :=
  match fn_body f_host_field_bytes with Ssequence _ rest=>rest|_=>Sskip end.

Definition field_api_call :=
  match fn_body f_host_field_bytes with
  | Ssequence(Ssequence call _)_=>call
  | _=>Sskip
  end.

Definition field_api_cont locals arguments k :=
  Kcall (Some _t'1) f_host_field_bytes (field_environment locals) (field_parameters arguments)
    (Kseq field_api_test(Kseq field_after_api k)).

Theorem field_first_api_structure :
  fn_body f_host_field_bytes = Ssequence(Ssequence field_api_call field_api_test)field_after_api.
Proof. reflexivity. Qed.

Lemma local_address_expression ge e le m identifier ty block :
  e!identifier=Some(block,ty) ->
  expression_value ge e le m(Eaddrof(Evar identifier ty)(tptr ty))(Vptr block Ptrofs.zero).
Proof.
  intro LOOK.
  destruct(local_location_value ge e le m identifier ty block LOOK)as[REAL UNIQUE].
  split;[econstructor;exact REAL|].
  intros other EVALUATION;inversion EVALUATION;subst.
  match goal with L:eval_lvalue _ _ _ _ _ _ _ _|-_=>
    destruct(UNIQUE _ _ _ L)as[B[O BF]];subst;reflexivity end.
  match goal with L:eval_lvalue _ _ _ _(Eaddrof _ _)_ _ _|-_=>inversion L end.
Qed.

Lemma actual_field_first_api_call (ge:Clight.genv) locals arguments m k symbol object objectOffset :
  field_object arguments=Vptr object objectOffset ->
  Genv.find_symbol ge _PyBytes_AsStringAndSize=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some python_bytes_definition ->
  store_edge ge
    (State f_host_field_bytes field_api_call (Kseq field_api_test(Kseq field_after_api k))
      (field_environment locals)(field_parameters arguments)m)
    (Callstate python_bytes_definition
      [field_object arguments;Vptr(field_local_data locals)Ptrofs.zero;
       Vptr(field_local_size locals)Ptrofs.zero]
      (field_api_cont locals arguments k)m).
Proof.
  intros OBJECT SYMBOL FUNCTION.
  eapply certified_call_edge with(vf:=Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value;eapply value_function;[reflexivity|exact SYMBOL|reflexivity].
  - eapply cons_argument_values with(v:=field_object arguments).
    + apply old_expression_value;apply value_temp;reflexivity.
    + rewrite OBJECT;reflexivity.
    + eapply cons_argument_values with(v:=Vptr(field_local_data locals)Ptrofs.zero).
      * apply local_address_expression;reflexivity.
      * reflexivity.
      * eapply cons_argument_values with(v:=Vptr(field_local_size locals)Ptrofs.zero).
        -- apply local_address_expression;reflexivity.
        -- reflexivity.
        -- apply no_argument_values.
  - cbn;exact FUNCTION.
  - reflexivity.
Qed.

Theorem actual_field_entry_reaches_python_api (ge:Clight.genv) before arguments k symbol object objectOffset :
  field_object arguments=Vptr object objectOffset ->
  Genv.find_symbol ge _PyBytes_AsStringAndSize=Some symbol ->
  Genv.find_funct_ptr ge symbol=Some python_bytes_definition ->
  exists locals after,
    field_allocations before locals after /\
    store_path ge (fun _=>True)
      (Callstate(Internal f_host_field_bytes)(field_values arguments)k before)4
      (Callstate python_bytes_definition
        [field_object arguments;Vptr(field_local_data locals)Ptrofs.zero;
         Vptr(field_local_size locals)Ptrofs.zero]
        (field_api_cont locals arguments k)after).
Proof.
  intros OBJECT SYMBOL FUNCTION.
  destruct(actual_field_entry_allocates ge before arguments k)
    as[locals[after[ENTRY[ALLOC REST]]]].
  exists locals,after;split;[exact ALLOC|].
  eapply store_next;[exact I|exact ENTRY|].
  rewrite field_first_api_structure.
  eapply store_next;[exact I|apply unchanged_store_edge,edge_seq|].
  eapply store_next;[exact I|apply unchanged_store_edge,edge_seq|].
  eapply store_next;[exact I|eapply actual_field_first_api_call;eassumption|].
  constructor;exact I.
Qed.
