(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Native resource operations use the actual fixed SDK signatures. *)
From Stdlib Require Import ZArith List String.
From compcert Require Import Coqlib Maps AST Values Globalenvs Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayRegistry GatewayMachine GatewayRuntime GatewayBindings.
Import ListNotations.
Local Open Scope string_scope.
Open Scope Z_scope.

Inductive gateway_spawn_api :=
  | gateway_socketpair_api | gateway_fcntl_api | gateway_close_api
  | gateway_actions_init_api | gateway_actions_destroy_api | gateway_actions_dup_api | gateway_actions_closefrom_api
  | gateway_attributes_init_api | gateway_attributes_destroy_api | gateway_attributes_group_api | gateway_attributes_flags_api
  | gateway_posix_spawn_api.

Definition gateway_spawn_identifier api : ident :=
  match api with
  | gateway_socketpair_api => _socketpair | gateway_fcntl_api => _leancage_host_fcntl | gateway_close_api => _close
  | gateway_actions_init_api => _posix_spawn_file_actions_init
  | gateway_actions_destroy_api => _posix_spawn_file_actions_destroy
  | gateway_actions_dup_api => _posix_spawn_file_actions_adddup2
  | gateway_actions_closefrom_api => _posix_spawn_file_actions_addclosefrom_np
  | gateway_attributes_init_api => _posix_spawnattr_init
  | gateway_attributes_destroy_api => _posix_spawnattr_destroy
  | gateway_attributes_group_api => _posix_spawnattr_setpgroup
  | gateway_attributes_flags_api => _posix_spawnattr_setflags
  | gateway_posix_spawn_api => _posix_spawn
  end.

Definition gateway_spawn_definition api : option (Ctypes.fundef Clight.function) :=
  match gateway_program_definition (gateway_spawn_identifier api) global_definitions with
  | Some (Gfun (External external types result convention)) => Some (External external types result convention)
  | _ => None
  end.

Definition gateway_spawn_operation {World Event} (backend : gateway_backend World Event) api arguments
    before world result after next observed : Prop :=
  exists definition, gateway_spawn_definition api = Some definition /\
    gateway_runtime_operation backend definition arguments before world result after next observed.

Definition gateway_actions_type := Tstruct __8078 noattr.
Definition gateway_attributes_type := Tstruct __8076 noattr.

Definition gateway_spawn_signature api : Ctypes.fundef Clight.function :=
  let unary name ty := External (EF_external name (mksignature [Xptr] Xint cc_default)) [tptr ty] tint cc_default in
  match api with
  | gateway_socketpair_api => External
      (EF_external "socketpair" (mksignature [Xint; Xint; Xint; Xptr] Xint cc_default))
      [tint; tint; tint; tptr tint] tint cc_default
  | gateway_fcntl_api => External
      (EF_external "leancage_host_fcntl" (mksignature [Xint; Xint; Xint] Xint cc_default))
      [tint; tint; tint] tint cc_default
  | gateway_close_api => External (EF_external "close" (mksignature [Xint] Xint cc_default)) [tint] tint cc_default
  | gateway_actions_init_api => unary "posix_spawn_file_actions_init" gateway_actions_type
  | gateway_actions_destroy_api => unary "posix_spawn_file_actions_destroy" gateway_actions_type
  | gateway_actions_dup_api => External
      (EF_external "posix_spawn_file_actions_adddup2" (mksignature [Xptr; Xint; Xint] Xint cc_default))
      [tptr gateway_actions_type; tint; tint] tint cc_default
  | gateway_actions_closefrom_api => External
      (EF_external "posix_spawn_file_actions_addclosefrom_np" (mksignature [Xptr; Xint] Xint cc_default))
      [tptr gateway_actions_type; tint] tint cc_default
  | gateway_attributes_init_api => unary "posix_spawnattr_init" gateway_attributes_type
  | gateway_attributes_destroy_api => unary "posix_spawnattr_destroy" gateway_attributes_type
  | gateway_attributes_group_api => External
      (EF_external "posix_spawnattr_setpgroup" (mksignature [Xptr; Xint] Xint cc_default))
      [tptr gateway_attributes_type; tint] tint cc_default
  | gateway_attributes_flags_api => External
      (EF_external "posix_spawnattr_setflags" (mksignature [Xptr; Xint16signed] Xint cc_default))
      [tptr gateway_attributes_type; tshort] tint cc_default
  | gateway_posix_spawn_api => External
      (EF_external "posix_spawn" (mksignature [Xptr; Xptr; Xptr; Xptr; Xptr; Xptr] Xint cc_default))
      [tptr tint; tptr tschar; tptr gateway_actions_type; tptr gateway_attributes_type;
       tptr (tptr tschar); tptr (tptr tschar)] tint cc_default
  end.

Theorem actual_gateway_spawn_signatures api : gateway_spawn_definition api = Some (gateway_spawn_signature api).
Proof. destruct api; reflexivity. Qed.

Theorem actual_gateway_spawn_layout :
  sizeof (genv_cenv (Clight.globalenv prog)) gateway_actions_type = 80 /\
  sizeof (genv_cenv (Clight.globalenv prog)) gateway_attributes_type = 336.
Proof. vm_compute; split; reflexivity. Qed.

Theorem actual_gateway_spawn_binding api :
  gateway_function_binding (Clight.globalenv prog) (gateway_spawn_identifier api) (gateway_spawn_signature api).
Proof. apply gateway_actual_function_binding; destruct api; vm_compute; reflexivity. Qed.
