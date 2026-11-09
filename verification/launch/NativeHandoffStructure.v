(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Functional regions are projections of the current complete guest AST. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
From EntryNative Require Import EntrySource.
Import ListNotations.

Fixpoint guest_tail (index : nat) (body : statement) : statement :=
  match index, body with
  | O, _ => body
  | S rest, Ssequence _ next => guest_tail rest next
  | _, _ => Sskip
  end.

Definition guest_phase index :=
  match guest_tail index (fn_body f_guest) with
  | Ssequence first _ => first
  | other => other
  end.

Definition guest_argument_tail := guest_tail 11 (fn_body f_guest).
Definition guest_copy_arguments := guest_phase 18.
Definition guest_check_arguments := guest_phase 19.

Theorem guest_argument_start_actual : guest_phase 11 =
  Sassign
    (Ederef (Ebinop Oadd (Evar _args (tarray (tptr tschar) 74))
      (Econst_int (Int.repr 0) tint) (tptr (tptr tschar))) (tptr tschar))
    (Evar ___stringlit_111 (tarray tschar 16)).
Proof. reflexivity. Qed.

Theorem guest_argument_copy_actual :
  guest_copy_arguments =
  Sloop
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset _t'27 (Efield (Evar _policy__1 (Tstruct _policy noattr)) _args (tptr (tptr tschar))))
          (Ssequence
            (Sset _t'28 (Ederef
              (Ebinop Oadd (Etempvar _t'27 (tptr (tptr tschar)))
                (Etempvar _i__2 tulong) (tptr (tptr tschar))) (tptr tschar)))
            (Sifthenelse (Etempvar _t'28 (tptr tschar))
              (Sset _t'20 (Ecast (Ebinop Olt (Etempvar _i__2 tulong)
                (Econst_int (Int.repr 64) tint) tint) tbool))
              (Sset _t'20 (Econst_int (Int.repr 0) tint)))))
        (Sifthenelse (Etempvar _t'20 tint) Sskip Sbreak))
      (Ssequence
        (Ssequence
          (Sset _t'25 (Efield (Evar _policy__1 (Tstruct _policy noattr)) _args (tptr (tptr tschar))))
          (Ssequence
            (Sset _t'26 (Ederef
              (Ebinop Oadd (Etempvar _t'25 (tptr (tptr tschar)))
                (Etempvar _i__2 tulong) (tptr (tptr tschar))) (tptr tschar)))
            (Sassign
              (Ederef (Ebinop Oadd (Evar _args (tarray (tptr tschar) 74))
                (Ebinop Oadd (Econst_int (Int.repr 9) tint) (Etempvar _i__2 tulong) tulong)
                (tptr (tptr tschar))) (tptr tschar))
              (Etempvar _t'26 (tptr tschar)))))
        (Sset _i__2 (Ebinop Oadd (Etempvar _i__2 tulong)
          (Econst_int (Int.repr 1) tint) tulong))))
    Sskip.
Proof. reflexivity. Qed.

Definition guest_argument_source :=
  Efield (Evar _policy__1 (Tstruct _policy noattr)) _args (tptr (tptr tschar)).

Definition guest_copy_body := match guest_copy_arguments with
  | Sloop body _ => body | _ => Sskip
  end.

Definition guest_copy_test := match guest_copy_body with
  | Ssequence test _ => test | _ => Sskip
  end.

Definition guest_copy_store := match guest_copy_body with
  | Ssequence _ (Ssequence store _) => store | _ => Sskip
  end.

Definition guest_copy_increment := match guest_copy_body with
  | Ssequence _ (Ssequence _ increment) => increment | _ => Sskip
  end.

Theorem guest_copy_body_structure : guest_copy_body =
  Ssequence guest_copy_test (Ssequence guest_copy_store guest_copy_increment).
Proof. reflexivity. Qed.

Theorem guest_copy_loop_structure : guest_copy_arguments = Sloop guest_copy_body Sskip.
Proof. reflexivity. Qed.
