(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Both real path checks share one checked source fragment. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Ctypesdefs Cop Clight.
Require Import ClightSteps LocalAccess.
From HostGateway Require Import GatewaySource GatewayBootstrapSource GatewayBootstrapLengthSource.
Import ListNotations.
Open Scope Z_scope.

Definition bootstrap_size_test := Ebinop Ogt (Etempvar _size tulong) (Econst_int (Int.repr 4095) tint) tint.
Definition bootstrap_tail_test := Ebinop Ole (Etempvar _size tulong) (Etempvar _tail tulong) tint.
Definition bootstrap_path_reject := Sreturn (Some (Eunop Oneg (Econst_int Int.one tint) tint)).
Definition bootstrap_suffix_call compared path := Scall (Some compared)
  (Evar _memcmp (Tfunction [tptr tvoid; tptr tvoid; tulong] tint cc_default))
  [Ebinop Osub (Ebinop Oadd path (Etempvar _size tulong) (tptr tschar))
      (Etempvar _tail tulong) (tptr tschar);
   Evar _suffix (tarray tschar 31); Etempvar _tail tulong].

Definition bootstrap_validation low prefix suffix compared character (byte_setup : statement -> statement)
    (prepare_compare : statement -> statement) path :=
  Ssequence
    (Ssequence
      (Ssequence
        (Sifthenelse bootstrap_size_test (Sset low (Econst_int Int.one tint))
          (Sset low (Ecast bootstrap_tail_test tbool)))
        (Sifthenelse (Etempvar low tint) (Sset prefix (Econst_int Int.one tint))
          (byte_setup (Sset prefix (Ecast (Ebinop One (Etempvar character tschar)
              (Econst_int (Int.repr 47) tint) tint) tbool)))))
      (Sifthenelse (Etempvar prefix tint) (Sset suffix (Econst_int Int.one tint))
        (Ssequence (prepare_compare (bootstrap_suffix_call compared path))
          (Sset suffix (Ecast (Etempvar compared tint) tbool)))))
    (Sifthenelse (Etempvar suffix tint) bootstrap_path_reject Sskip).

Definition bootstrap_after_tail := match bootstrap_after_length with Ssequence _ rest => rest | _ => Sskip end.
Definition bootstrap_loaded_validation := match bootstrap_after_tail with Ssequence first _ => first | _ => Sskip end.
Definition bootstrap_after_loaded_validation := match bootstrap_after_tail with Ssequence _ rest => rest | _ => Sskip end.
Definition bootstrap_after_api_size := match bootstrap_after_loaded_validation with Ssequence _ rest => rest | _ => Sskip end.
Definition bootstrap_realpath_sequence := match bootstrap_after_api_size with Ssequence first _ => first | _ => Sskip end.
Definition bootstrap_after_realpath := match bootstrap_after_api_size with Ssequence _ rest => rest | _ => Sskip end.
Definition bootstrap_canonical_length_sequence := match bootstrap_after_realpath with Ssequence first _ => first | _ => Sskip end.
Definition bootstrap_after_canonical_length := match bootstrap_after_realpath with Ssequence _ rest => rest | _ => Sskip end.
Definition bootstrap_canonical_validation := match bootstrap_after_canonical_length with Ssequence first _ => first | _ => Sskip end.

Definition bootstrap_filename_expression :=
  Efield (Evar _information (Tstruct __7533 noattr)) _dli_fname (tptr tschar).
Definition bootstrap_loaded_byte_setup following := Ssequence (Sset _t'18 bootstrap_filename_expression)
  (Ssequence (Sset _t'19 (Ederef (Ebinop Oadd (Etempvar _t'18 (tptr tschar))
    (Econst_int Int.zero tint) (tptr tschar)) tschar)) following).
Definition bootstrap_canonical_byte_setup following := Ssequence (Sset _t'15
  (Ederef (Ebinop Oadd (Evar _resolved (tarray tschar 4096))
    (Econst_int Int.zero tint) (tptr tschar)) tschar)) following.

Theorem actual_bootstrap_validation_fragments :
  bootstrap_loaded_validation = bootstrap_validation _t'4 _t'5 _t'6 _t'7 _t'19
    bootstrap_loaded_byte_setup (fun call => Ssequence (Sset _t'17 bootstrap_filename_expression) call)
    (Etempvar _t'17 (tptr tschar)) /\
  bootstrap_canonical_validation = bootstrap_validation _t'10 _t'11 _t'12 _t'13 _t'15
    bootstrap_canonical_byte_setup (fun call => call) (Evar _resolved (tarray tschar 4096)).
Proof. split; reflexivity. Qed.

Theorem gateway_bootstrap_size_expression ge environment temporaries memory size :
  temporaries ! _size = Some (Vlong size) ->
  expression_value ge environment temporaries memory bootstrap_size_test
    (Val.of_bool (Int64.cmpu Cgt size (Int64.repr 4095))).
Proof.
  intro SIZE; apply old_expression_value; eapply value_binary;
    [apply value_temp; exact SIZE |constructor |reflexivity].
Qed.

Theorem gateway_bootstrap_tail_expression ge environment temporaries memory size :
  temporaries ! _size = Some (Vlong size) -> temporaries ! _tail = Some (Vlong (Int64.repr 30)) ->
  expression_value ge environment temporaries memory bootstrap_tail_test
    (Val.of_bool (Int64.cmpu Cle size (Int64.repr 30))).
Proof.
  intros SIZE TAIL; apply old_expression_value; eapply value_binary;
    [apply value_temp; exact SIZE |apply value_temp; exact TAIL |reflexivity].
Qed.
