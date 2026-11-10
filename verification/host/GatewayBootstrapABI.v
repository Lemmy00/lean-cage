(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Bootstrap uses the actual loader/string-library declarations. *)
From Stdlib Require Import ZArith List String.
From compcert Require Import Coqlib Maps Integers AST Values Globalenvs Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayRegistry GatewayRuntime GatewayBindings GatewayMachine.
Import ListNotations.
Local Open Scope string_scope.
Open Scope Z_scope.

Inductive gateway_bootstrap_api :=
  | gateway_loader_address_api | gateway_canonical_path_api | gateway_bounded_length_api
  | gateway_memory_compare_api | gateway_memory_copy_api.

Definition gateway_bootstrap_identifier api : ident := match api with
  | gateway_loader_address_api => _dladdr | gateway_canonical_path_api => _realpath
  | gateway_bounded_length_api => _strnlen | gateway_memory_compare_api => _memcmp
  | gateway_memory_copy_api => _memcpy end.

Definition gateway_loader_information_type := Tstruct __7533 noattr.
Definition gateway_bootstrap_signature api : Ctypes.fundef Clight.function := match api with
  | gateway_loader_address_api => External
      (EF_external "dladdr" (mksignature [Xptr; Xptr] Xint cc_default))
      [tptr tvoid; tptr gateway_loader_information_type] tint cc_default
  | gateway_canonical_path_api => External
      (EF_external "realpath" (mksignature [Xptr; Xptr] Xptr cc_default))
      [tptr tschar; tptr tschar] (tptr tschar) cc_default
  | gateway_bounded_length_api => External
      (EF_external "strnlen" (mksignature [Xptr; Xlong] Xlong cc_default))
      [tptr tschar; tulong] tulong cc_default
  | gateway_memory_compare_api => External
      (EF_external "memcmp" (mksignature [Xptr; Xptr; Xlong] Xint cc_default))
      [tptr tvoid; tptr tvoid; tulong] tint cc_default
  | gateway_memory_copy_api => External
      (EF_external "memcpy" (mksignature [Xptr; Xptr; Xlong] Xptr cc_default))
      [tptr tvoid; tptr tvoid; tulong] (tptr tvoid) cc_default
  end.

Definition gateway_bootstrap_operation {World Event} (backend : gateway_backend World Event) api arguments
    before world result after next observed : Prop :=
  gateway_runtime_operation backend (gateway_bootstrap_signature api) arguments before world result after next observed.

Theorem actual_bootstrap_declarations api :
  gateway_program_definition (gateway_bootstrap_identifier api) global_definitions =
    Some (Gfun (gateway_bootstrap_signature api)).
Proof. destruct api; reflexivity. Qed.

Theorem actual_bootstrap_bindings api :
  gateway_function_binding (Clight.globalenv prog) (gateway_bootstrap_identifier api) (gateway_bootstrap_signature api).
Proof. apply gateway_actual_function_binding; destruct api; vm_compute; reflexivity. Qed.

Theorem actual_bootstrap_information_size :
  sizeof (genv_cenv (Clight.globalenv prog)) gateway_loader_information_type = 32.
Proof. vm_compute; reflexivity. Qed.
