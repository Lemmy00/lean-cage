(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-bridge.frames: Exact imported frame operations and source observations. *)
From Stdlib Require Import Arith.
From LeanImport Require Import Lean.
Require Import NormalizedImport.
Local Close Scope lean_scope.
Local Open Scope nat_scope.
Lemma parser_match_exact (A : Type) n (z o t : A) (other : Nat -> A) :
 LeanCageM4_Normalized_parse_match_1 (fun _ => A) n (fun _ => z) (fun _ => o) (fun _ => t) other =
 match n with Nat_zero => z | Nat_succ Nat_zero => o | Nat_succ (Nat_succ Nat_zero) => t | _ => other n end.
Proof. destruct n as [|[|[|n]]]; reflexivity. Qed.
