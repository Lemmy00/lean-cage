(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual bootstrap fills the root, engine and default-result buffers. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Ctypes Ctypesdefs Cop Clight.
From HostGateway Require Import GatewaySource GatewayBootstrapValidationSource.
Import ListNotations.
Open Scope Z_scope.

Definition bootstrap_after_canonical_validation :=
  match bootstrap_after_canonical_length with Ssequence _ rest => rest | _ => Sskip end.
Definition bootstrap_after_root_size :=
  match bootstrap_after_canonical_validation with Ssequence _ rest => rest | _ => Sskip end.
Definition bootstrap_after_root_bound :=
  match bootstrap_after_root_size with Ssequence _ rest => rest | _ => Sskip end.
Definition bootstrap_copy_start :=
  match bootstrap_after_root_bound with Ssequence _ rest => rest | _ => Sskip end.
Fixpoint bootstrap_copy_after count := match count with
  | O => bootstrap_copy_start
  | S previous => match bootstrap_copy_after previous with Ssequence _ rest => rest | _ => Sskip end
  end.
Definition bootstrap_copy_statement index :=
  match bootstrap_copy_after index with Ssequence first _ => first | _ => Sskip end.
Definition bootstrap_array identifier := Evar identifier (tarray tschar 4096).
Definition bootstrap_root_size := Etempvar _root_size tulong.
Definition bootstrap_api_size := Etempvar _api_size tulong.
Definition bootstrap_copy target source amount := Scall None
  (Evar _memcpy (Tfunction [tptr tvoid; tptr tvoid; tulong] (tptr tvoid) cc_default))
  [target; source; amount].
Definition bootstrap_array_add identifier offset :=
  Ebinop Oadd (bootstrap_array identifier) offset (tptr tschar).

Theorem actual_bootstrap_copy_statements :
  bootstrap_copy_statement 0 = bootstrap_copy (bootstrap_array _host_root)
    (bootstrap_array _resolved) bootstrap_root_size /\
  bootstrap_copy_statement 1 = Sassign (Ederef (bootstrap_array_add _host_root bootstrap_root_size) tschar)
    (Econst_int Int.zero tint) /\
  bootstrap_copy_statement 2 = bootstrap_copy (bootstrap_array _host_engine)
    (bootstrap_array _host_root) bootstrap_root_size /\
  bootstrap_copy_statement 3 = bootstrap_copy (bootstrap_array_add _host_engine bootstrap_root_size)
    (Evar _executable (tarray tschar 19)) (Esizeof (tarray tschar 19) tulong) /\
  bootstrap_copy_statement 4 = Ssequence (Sset _t'14 bootstrap_filename_expression)
    (bootstrap_copy (bootstrap_array _host_default_results) (Etempvar _t'14 (tptr tschar)) bootstrap_api_size) /\
  bootstrap_copy_statement 5 = bootstrap_copy (bootstrap_array_add _host_default_results bootstrap_api_size)
    (Evar _results (tarray tschar 21)) (Esizeof (tarray tschar 21) tulong) /\
  bootstrap_copy_after 6 = Sreturn (Some (Econst_int Int.zero tint)).
Proof. repeat split; reflexivity. Qed.
