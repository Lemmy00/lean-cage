(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Initializer calls bind to the frozen actual SDK
   declarations. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib AST Values Globalenvs Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayInitializerObjectsSource GatewayReferenceSourceExecution GatewayBindings.
Import ListNotations.
Local Open Scope string_scope.

Definition initializer_add_ref_definition : Ctypes.fundef Clight.function := External
  (EF_external "PyModule_AddObjectRef" (mksignature [Xptr; Xptr; Xptr] Xint cc_default))
  [tptr (Tstruct __object noattr); tptr tschar; tptr (Tstruct __object noattr)] tint cc_default.

Theorem gateway_actual_initializer_object_bindings :
  Forall (fun pair => gateway_function_binding (Clight.globalenv prog) (fst pair) (snd pair))
    [(_PyImport_ImportModule, initializer_import_definition);
     (_PyObject_GetAttrString, initializer_attribute_definition);
     (_PyModule_Create2, initializer_module_definition);
     (_PyType_FromSpec, initializer_type_definition);
     (_PyModule_AddObject, initializer_add_definition);
     (_PyModule_AddObjectRef, initializer_add_ref_definition);
     (_Py_DecRef, gateway_reference_decref_definition)].
Proof.
  repeat (apply Forall_cons; [apply gateway_actual_function_binding; vm_compute; reflexivity |]); constructor.
Qed.

Theorem gateway_actual_initializer_object_symbols identifier :
  In identifier [___stringlit_127; ___stringlit_128; ___stringlit_129; ___stringlit_130; ___stringlit_131;
    _host_module; _host_workspace_spec; _host_cancellation_spec; _host_outcome_spec;
    _host_path_class; _host_cancellation_class; _host_outcome_class] ->
  exists object, Genv.find_symbol (Clight.globalenv prog) identifier = Some object.
Proof.
  cbn; intro MEMBER; repeat destruct MEMBER as [MEMBER |MEMBER]; try contradiction;
    subst identifier; eexists; vm_compute; reflexivity.
Qed.
