(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual module initializer creates and retains its result class. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayRegistry GatewayTypeRuntime GatewayObjectAddresses.
Import ListNotations.
Open Scope Z_scope.

Fixpoint gateway_find_global_creation (identifier : ident) (body : statement) : option statement :=
  match body with
  | Ssequence first rest =>
      match first with
      | Ssequence (Scall _ _ _) (Sassign (Evar actual _) _) =>
          if Pos.eqb identifier actual then Some body else
            match gateway_find_global_creation identifier first with
            | Some found => Some found | None => gateway_find_global_creation identifier rest end
      | _ => match gateway_find_global_creation identifier first with
          | Some found => Some found | None => gateway_find_global_creation identifier rest end
      end
  | _ => None
  end.

Definition module_outcome_creation := Eval vm_compute in
  match gateway_find_global_creation _host_outcome_class (fn_body f_host_initialize) with
  | Some found => found | None => Sskip end.
Definition module_outcome_first := match module_outcome_creation with Ssequence first _ => first | _ => Sskip end.
Definition module_outcome_rest := match module_outcome_creation with Ssequence _ rest => rest | _ => Sskip end.
Definition module_outcome_call := match module_outcome_first with Ssequence first _ => first | _ => Sskip end.
Definition module_outcome_store := match module_outcome_first with Ssequence _ rest => rest | _ => Sskip end.
Definition module_outcome_cont temporaries continuation :=
  Kcall (Some _t'11) f_host_initialize empty_env temporaries
    (Kseq module_outcome_store (Kseq module_outcome_rest continuation)).

Theorem actual_module_outcome_creation :
  gateway_find_global_creation _host_outcome_class (fn_body f_host_initialize) = Some module_outcome_creation /\
  module_outcome_first = Ssequence module_outcome_call module_outcome_store /\
  module_outcome_creation = Ssequence module_outcome_first module_outcome_rest /\
  module_outcome_store = Sassign (Evar _host_outcome_class (tptr (Tstruct __object noattr)))
    (Etempvar _t'11 (tptr (Tstruct __object noattr))).
Proof. repeat split; reflexivity. Qed.

Theorem actual_module_outcome_call_edge (ge : Clight.genv) temporaries continuation before symbol specification :
  Genv.find_symbol ge _PyType_FromSpec = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some (External
    (EF_external "PyType_FromSpec" (mksignature [Xptr] Xptr cc_default))
    [tptr (Tstruct __5268 noattr)] (tptr (Tstruct __object noattr)) cc_default) ->
  Genv.find_symbol ge _host_outcome_spec = Some specification ->
  store_edge ge (State f_host_initialize module_outcome_call
      (Kseq module_outcome_store (Kseq module_outcome_rest continuation)) empty_env temporaries before)
    (Callstate (External (EF_external "PyType_FromSpec" (mksignature [Xptr] Xptr cc_default))
      [tptr (Tstruct __5268 noattr)] (tptr (Tstruct __object noattr)) cc_default)
      [Vptr specification Ptrofs.zero] (module_outcome_cont temporaries continuation) before).
Proof.
  intros SYMBOL FUNCTION SPECIFICATION.
  eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value; eapply value_function; [reflexivity |exact SYMBOL |reflexivity].
  - eapply cons_argument_values with (v := Vptr specification Ptrofs.zero).
    + apply gateway_global_address_expression; [reflexivity |exact SPECIFICATION].
    + reflexivity.
    + apply no_argument_values.
  - cbn; exact FUNCTION.
  - reflexivity.
Qed.

Theorem actual_module_outcome_store_edge (ge : Clight.genv) temporaries continuation before after class symbol :
  Genv.find_symbol ge _host_outcome_class = Some symbol ->
  temporaries ! _t'11 = Some class ->
  (exists object offset, class = Vptr object offset) ->
  Mem.store Mptr before symbol 0 class = Some after ->
  store_edge ge (State f_host_initialize module_outcome_store continuation empty_env temporaries before)
    (State f_host_initialize Sskip continuation empty_env temporaries after).
Proof.
  intros SYMBOL VALUE [object [offset CLASS]] STORE; subst class.
  eapply assignment_source_edge with (b := symbol) (ofs := Ptrofs.zero)
    (v := Vptr object offset) (w := Vptr object offset).
  - apply global_location_value; [reflexivity |exact SYMBOL].
  - apply old_expression_value, value_temp; exact VALUE.
  - reflexivity.
  - eapply assign_loc_value; [reflexivity |exact STORE].
Qed.
