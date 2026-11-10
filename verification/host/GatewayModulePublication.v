(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Module publication retains the source-owned class on success and failure. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayModuleSource GatewayRuntime
  GatewayTypeRuntime GatewayRootLeases GatewayPython GatewayObjects GatewayThreadRuntime GatewayErrorRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition module_outcome_guard_sequence := match module_outcome_rest with Ssequence first _ => first | _ => Sskip end.
Definition module_outcome_after_guard := match module_outcome_rest with Ssequence _ rest => rest | _ => Sskip end.
Definition module_outcome_add_sequence := match module_outcome_after_guard with Ssequence first _ => first | _ => Sskip end.
Definition module_outcome_return := match module_outcome_after_guard with Ssequence _ rest => rest | _ => Sskip end.
Definition module_outcome_add_first := match module_outcome_add_sequence with Ssequence first _ => first | _ => Sskip end.
Definition module_outcome_add_test := match module_outcome_add_sequence with Ssequence _ rest => rest | _ => Sskip end.
Definition module_outcome_add_load := match module_outcome_add_first with Ssequence first _ => first | _ => Sskip end.
Definition module_outcome_add_call := match module_outcome_add_first with Ssequence _ rest => rest | _ => Sskip end.
Definition module_outcome_add_cont temporaries continuation :=
  Kcall (Some _t'12) f_host_initialize empty_env temporaries
    (Kseq module_outcome_add_test (Kseq module_outcome_return continuation)).

Theorem actual_module_outcome_addref_structure :
  module_outcome_after_guard = Ssequence module_outcome_add_sequence module_outcome_return /\
  module_outcome_add_sequence = Ssequence module_outcome_add_first module_outcome_add_test /\
  module_outcome_add_first = Ssequence module_outcome_add_load module_outcome_add_call /\
  module_outcome_add_load = Sset _t'13 (Evar _host_outcome_class (tptr (Tstruct __object noattr))) /\
  module_outcome_return = Sreturn (Some (Etempvar _module (tptr (Tstruct __object noattr)))).
Proof. repeat split; reflexivity. Qed.

Theorem actual_module_outcome_addref_edge (ge : Clight.genv) temporaries continuation before
    module class symbol name :
  temporaries ! _module = Some module -> temporaries ! _t'13 = Some class ->
  (exists object offset, module = Vptr object offset) -> (exists object offset, class = Vptr object offset) ->
  Genv.find_symbol ge _PyModule_AddObjectRef = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some (External
    (EF_external "PyModule_AddObjectRef" (mksignature [Xptr; Xptr; Xptr] Xint cc_default))
    [tptr (Tstruct __object noattr); tptr tschar; tptr (Tstruct __object noattr)] tint cc_default) ->
  Genv.find_symbol ge ___stringlit_131 = Some name ->
  store_edge ge (State f_host_initialize module_outcome_add_call
      (Kseq module_outcome_add_test (Kseq module_outcome_return continuation)) empty_env temporaries before)
    (Callstate (External
      (EF_external "PyModule_AddObjectRef" (mksignature [Xptr; Xptr; Xptr] Xint cc_default))
      [tptr (Tstruct __object noattr); tptr tschar; tptr (Tstruct __object noattr)] tint cc_default)
      [module; Vptr name Ptrofs.zero; class] (module_outcome_add_cont temporaries continuation) before).
Proof.
  intros MODULE CLASS [module_object [module_offset MODULE_PTR]] [class_object [class_offset CLASS_PTR]]
    SYMBOL FUNCTION NAME; subst module class.
  eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value; eapply value_function; [reflexivity |exact SYMBOL |reflexivity].
  - eapply cons_argument_values with (v := Vptr module_object module_offset).
    + apply old_expression_value, value_temp; exact MODULE.
    + reflexivity.
    + eapply cons_argument_values with (v := Vptr name Ptrofs.zero).
      * apply old_expression_value; eapply value_function; [reflexivity |exact NAME |reflexivity].
      * reflexivity.
      * eapply cons_argument_values with (v := Vptr class_object class_offset).
        -- apply old_expression_value, value_temp; exact CLASS.
        -- reflexivity.
        -- apply no_argument_values.
  - cbn; exact FUNCTION.
  - reflexivity.
Qed.

Theorem gateway_module_publication_retains_class {World Event} (backend : gateway_backend World Event)
    python objects types allocator instances leases normal attached io native stable
    (runtime : gateway_type_runtime backend python objects types allocator instances leases normal attached io native stable)
    before world module name name_bytes class ticket symbol returned after next observed :
  normal before world -> gateway_rooted (python world) (objects world) module ->
  gateway_rooted (python world) (objects world) class -> gateway_error_cstring before name name_bytes ->
  leases world ticket class -> native world symbol -> Mem.load Mptr before symbol 0 = Some class ->
  gateway_type_operation backend gateway_module_add_object_ref [module; name; class]
    before world returned after next observed ->
  leases next ticket class /\ Mem.load Mptr after symbol 0 = Some class /\ attached after next /\
    exists status, returned = Vint status /\ (status = Int.zero -> normal after next).
Proof.
  intros NORMAL MODULE CLASS NAME LEASE PRIVATE GLOBAL OPERATION.
  destruct (@gateway_module_add_ref_effect World Event backend python objects types allocator instances leases
    normal attached io native stable runtime before world module name name_bytes class returned after next observed
    NORMAL MODULE CLASS NAME OPERATION) as [STATUS [ATTACHED [LEASES [ACCESS [FRAME QUIET]]]]].
  split; [apply LEASES; exact LEASE |]. split.
  - eapply Mem.load_unchanged_on; [exact FRAME | |exact GLOBAL].
    intros; split; [left; exact PRIVATE |cbn; tauto].
  - split; [exact ATTACHED |exact STATUS].
Qed.
