(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-compiled-reporting.certificate: The outer allocator validates each selected candidate. *)
From Stdlib Require Import ZArith List Bool String.
From compcert Require Import Integers AST Maps Errors RTL LTL RTLtyping Allocation.
Local Open Scope string_scope.
Local Open Scope error_monad_scope.

Record allocation_candidate := {
 candidate_entry : positive;
 candidate_stack : Z;
 candidate_nodes : nat;
 candidate_function : LTL.function
}.

Fixpoint choose_candidate (candidates : list allocation_candidate) (source : RTL.function) : res LTL.function :=
 match candidates with
 | nil => Error(msg "no validated allocation candidate")
 | first::rest =>
   if Pos.eqb(candidate_entry first)(RTL.fn_entrypoint source) &&
      Z.eqb(candidate_stack first)(RTL.fn_stacksize source) &&
      Nat.eqb(candidate_nodes first)(List.length(PTree.elements(RTL.fn_code source)))
   then if signature_eq (LTL.fn_sig(candidate_function first))(RTL.fn_sig source)
     then OK(candidate_function first)
     else choose_candidate rest source
   else choose_candidate rest source
 end.

Definition allocation_candidates candidates (source : RTL.function) : res LTL.function :=
 choose_candidate candidates source.
