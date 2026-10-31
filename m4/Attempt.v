(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-native.evidence: Unfinished effectful proof, intentionally exports no theorem. *)
From Coq Require Import ZArith List String.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events
  Ctypes Ctypesdefs Cop Clight Smallstep.
Require Import Slice Effects.
Import ListNotations.
Open Scope Z_scope.

Definition write_ef := EF_external "write"
  (mksignature [Xint; Xptr; Xlong] Xlong cc_default).

(* This is the return-bound obligation reached at write_all's actual write call.
   Quantify over all initialized owned bytes; do not assume the bound itself.
   The current stock external-call axioms give only typing/relational properties,
   not this syscall contract. No completed simulation is exported. *)
Goal forall ge fd block ofs (bytes : list Byte.int) m t n m',
  0 < Z.of_nat (length bytes) <= 160 ->
  Ptrofs.unsigned ofs + Z.of_nat (length bytes) <= Ptrofs.modulus ->
  Mem.loadbytes m block (Ptrofs.unsigned ofs) (Z.of_nat (length bytes)) = Some (map Byte bytes) ->
  Mem.range_perm m block (Ptrofs.unsigned ofs)
    (Ptrofs.unsigned ofs + Z.of_nat (length bytes)) Cur Readable ->
  external_call write_ef ge
    [Vint fd; Vptr block ofs; Vlong (Int64.repr (Z.of_nat (length bytes)))]
    m t (Vlong n) m' ->
  Int64.signed n = -1 \/ 0 <= Int64.signed n <= Z.of_nat (length bytes).
Proof.
  intros ge fd block ofs bytes m t n m' SIZE NO_WRAP BYTES OWNED CALL.
  unfold external_call, write_ef in CALL.
  Fail solve [auto].
  Show.
Abort.

(* Source connection for the attempted obligation, checked by reduction against
   the generated AST. A source edit changes this equation and fails the gate. *)
Definition actual_write_call :=
  Scall (Some _t'1)
    (Evar _write (Tfunction [tint; tptr tvoid; tulong] tlong cc_default))
    [Etempvar _fd tint; Etempvar _p (tptr tuchar); Etempvar _count tulong].

Fixpoint contains_call (s : statement) : bool :=
  match s with
  | Scall _ (Evar id _) _ => Pos.eqb id _write
  | Ssequence a b | Sloop a b => orb (contains_call a) (contains_call b)
  | Sifthenelse _ a b => orb (contains_call a) (contains_call b)
  | _ => false
  end.
Example attempted_function_calls_write : contains_call (fn_body f_write_all) = true.
Proof. reflexivity. Qed.
Check attempted_function_calls_write.
Print Assumptions attempted_function_calls_write.

Fixpoint first_call (s : statement) : option statement :=
  match s with
  | Scall _ _ _ => Some s
  | Ssequence a b | Sloop a b =>
      match first_call a with Some c => Some c | None => first_call b end
  | Sifthenelse _ a b =>
      match first_call a with Some c => Some c | None => first_call b end
  | _ => None
  end.
Example attempted_call_is_actual : first_call (fn_body f_write_all) = Some actual_write_call.
Proof. reflexivity. Qed.
Check attempted_call_is_actual.
Print Assumptions attempted_call_is_actual.
