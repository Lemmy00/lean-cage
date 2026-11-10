(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Native bootstrap literals match their source initializers and shared byte view. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Globalenvs Ctypes Clight.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewaySource GatewayGlobals GatewayBootstrapImport GatewayLoaderRegions GatewayRegistry.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Definition bootstrap_suffix_bytes := map Byte.repr
  [47;112;121;116;104;111;110;47;108;101;97;110;99;97;103;101;47;95;104;111;115;116;46;97;98;105;51;46;115;111].
Definition bootstrap_executable_bytes := map Byte.repr
  [47;98;105;110;47;108;101;97;110;99;97;103;101;45;104;111;115;116].
Definition bootstrap_results_bytes := map Byte.repr
  [47;46;116;111;111;108;115;47;112;114;111;100;117;99;116;47;114;117;110;115].

Fixpoint bootstrap_imported_bytes bytes : List_inst1 Nat := match bytes with
  | [] => List_nil_inst1 Nat
  | byte :: rest => List_cons_inst1 Nat (Nat_of_nat (Z.to_nat (Byte.unsigned byte))) (bootstrap_imported_bytes rest)
  end.

Theorem actual_bootstrap_constant_bytes :
  bootstrap_imported_bytes bootstrap_suffix_bytes = LeanCage_Host_BootstrapCode_suffix /\
  bootstrap_imported_bytes bootstrap_executable_bytes = LeanCage_Host_BootstrapCode_executable /\
  bootstrap_imported_bytes bootstrap_results_bytes = LeanCage_Host_BootstrapCode_results.
Proof. repeat split; reflexivity. Qed.

Theorem actual_bootstrap_source_literals :
  gateway_static_cstring _suffix v_suffix bootstrap_suffix_bytes /\
  gateway_static_cstring _executable v_executable bootstrap_executable_bytes /\
  gateway_static_cstring _results v_results bootstrap_results_bytes.
Proof.
  split; [|split].
  all: (apply gateway_static_string_from_registration;
      [vm_compute; reflexivity |reflexivity |reflexivity |vm_compute; intuition discriminate |
       change Ptrofs.modulus with 18446744073709551616; cbn; lia]).
Qed.
