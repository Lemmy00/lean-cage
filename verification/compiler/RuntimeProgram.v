(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-compiled-reporting.runtime: Give the compiler a preserved name for the runtime's errno cell. *)
From Stdlib Require Import List String ZArith.
From compcert Require Import Integers AST Globalenvs Ctypes Ctypesdefs Clight Clightdefs.
From LeanCageMain Require Main.
Import ListNotations Clightdefs.ClightNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope clight_scope.
Local Open Scope list_scope.

Definition runtime_errno : ident := $"errno".
Definition errno_storage : globvar type :=
 {|gvar_info:=tint;gvar_init:=[Init_space 4];gvar_readonly:=false;gvar_volatile:=false|}.

(* This is the per-thread logical runtime view. It does not change the helper
   functions and does not assert that a normal global implements physical TLS.
   The native runtime/loader must provide the address interpretation. *)
Definition program : Clight.program :=
 {|prog_defs:=prog_defs Main.prog++[(runtime_errno,Gvar errno_storage)];
   prog_public:=runtime_errno::prog_public Main.prog;
   prog_main:=prog_main Main.prog;
   prog_types:=prog_types Main.prog;
   prog_comp_env:=prog_comp_env Main.prog;
   prog_comp_env_eq:=prog_comp_env_eq Main.prog|}.

Theorem helper_definitions_retained :
 prog_defs program=prog_defs Main.prog++[(runtime_errno,Gvar errno_storage)].
Proof. reflexivity. Qed.
Theorem errno_symbol_fresh : Genv.find_symbol(Clight.globalenv Main.prog)runtime_errno=None.
Proof. vm_compute;reflexivity. Qed.
Theorem errno_symbol : Genv.find_symbol(Clight.globalenv program)runtime_errno=Some 374%positive.
Proof. vm_compute;reflexivity. Qed.
Theorem errno_public : Genv.public_symbol(Clight.globalenv program)runtime_errno=true.
Proof. vm_compute;reflexivity. Qed.

Definition errno_root (ge:Clight.genv) (storage:positive) (offset:Z) :=
 Genv.find_symbol ge runtime_errno=Some storage /\ offset=0 /\
 Genv.public_symbol ge runtime_errno=true.
