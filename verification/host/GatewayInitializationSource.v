(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Actual wrapper guards precede the unchanged initializer. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource.
Import ListNotations.
Open Scope Z_scope.

Definition initialization_interpreter := match fn_body f_PyInit__host with
  Ssequence first _ => first | _ => Sskip end.
Definition initialization_after_interpreter := match fn_body f_PyInit__host with
  Ssequence _ rest => rest | _ => Sskip end.
Definition initialization_active_check := match initialization_after_interpreter with
  Ssequence first _ => first | _ => Sskip end.
Definition initialization_after_active := match initialization_after_interpreter with
  Ssequence _ rest => rest | _ => Sskip end.
Definition initialization_complete_check := match initialization_after_active with
  Ssequence first _ => first | _ => Sskip end.
Definition initialization_after_complete := match initialization_after_active with
  Ssequence _ rest => rest | _ => Sskip end.
Definition initialization_enter := match initialization_after_complete with
  Ssequence first _ => first | _ => Sskip end.
Definition initialization_after_enter := match initialization_after_complete with
  Ssequence _ rest => rest | _ => Sskip end.
Definition initialization_body_sequence := match initialization_after_enter with
  Ssequence first _ => first | _ => Sskip end.
Definition initialization_after_body := match initialization_after_enter with
  Ssequence _ rest => rest | _ => Sskip end.
Definition initialization_body_call := match initialization_body_sequence with
  Ssequence first _ => first | _ => Sskip end.
Definition initialization_bind_result := match initialization_body_sequence with
  Ssequence _ rest => rest | _ => Sskip end.
Definition initialization_success := match initialization_after_body with
  Ssequence first _ => first | _ => Sskip end.
Definition initialization_after_success := match initialization_after_body with
  Ssequence _ rest => rest | _ => Sskip end.
Definition initialization_clear := match initialization_after_success with
  Ssequence first _ => first | _ => Sskip end.
Definition initialization_return := match initialization_after_success with
  Ssequence _ rest => rest | _ => Sskip end.

Theorem actual_initialization_source_structure :
  initialization_active_check = Ssequence (Sset _t'6 (Evar _host_initializing tint))
    (Sifthenelse (Etempvar _t'6 tint)
      (match initialization_active_check with Ssequence _ (Sifthenelse _ rejected _) => rejected | _ => Sskip end)
      Sskip) /\
  initialization_complete_check = Ssequence (Sset _t'4 (Evar _host_initialized tint))
    (Sifthenelse (Etempvar _t'4 tint)
      (match initialization_complete_check with Ssequence _ (Sifthenelse _ rejected _) => rejected | _ => Sskip end)
      Sskip) /\
  initialization_enter = Sassign (Evar _host_initializing tint) (Econst_int Int.one tint) /\
  initialization_body_call = Scall (Some _t'3)
    (Evar _host_initialize (Tfunction [] (tptr (Tstruct __object noattr)) cc_default)) [] /\
  initialization_bind_result = Sset _result (Etempvar _t'3 (tptr (Tstruct __object noattr))) /\
  initialization_success = Sifthenelse (Etempvar _result (tptr (Tstruct __object noattr)))
    (Sassign (Evar _host_initialized tint) (Econst_int Int.one tint)) Sskip /\
  initialization_clear = Sassign (Evar _host_initializing tint) (Econst_int Int.zero tint) /\
  initialization_return = Sreturn (Some (Etempvar _result (tptr (Tstruct __object noattr)))).
Proof. repeat split; reflexivity. Qed.

Theorem initialization_global_word (ge : Clight.genv) temporaries memory identifier object word :
  Genv.find_symbol ge identifier = Some object -> Mem.load Mint32 memory object 0 = Some (Vint word) ->
  expression_value ge empty_env temporaries memory (Evar identifier tint) (Vint word).
Proof.
  intros SYMBOL LOAD; eapply location_read_value.
  - apply global_location_value; [reflexivity |exact SYMBOL].
  - eapply deref_loc_value; [reflexivity |exact LOAD].
Qed.

Theorem initialization_global_store (ge : Clight.genv) temporaries continuation before after identifier object word :
  Genv.find_symbol ge identifier = Some object ->
  Mem.store Mint32 before object 0 (Vint word) = Some after ->
  store_edge ge
    (State f_PyInit__host (Sassign (Evar identifier tint) (Econst_int word tint))
      continuation empty_env temporaries before)
    (State f_PyInit__host Sskip continuation empty_env temporaries after).
Proof.
  intros SYMBOL STORE; eapply assignment_source_edge with (b := object) (ofs := Ptrofs.zero)
    (v := Vint word) (w := Vint word).
  - apply global_location_value; [reflexivity |exact SYMBOL].
  - apply old_expression_value; constructor.
  - reflexivity.
  - eapply assign_loc_value; [reflexivity |exact STORE].
Qed.

Theorem actual_initialization_body_edge (ge : Clight.genv) temporaries continuation memory symbol :
  Genv.find_symbol ge _host_initialize = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some (Internal f_host_initialize) ->
  store_edge ge (State f_PyInit__host initialization_body_call continuation empty_env temporaries memory)
    (Callstate (Internal f_host_initialize) []
      (Kcall (Some _t'3) f_PyInit__host empty_env temporaries continuation) memory).
Proof.
  intros SYMBOL FUNCTION; eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value; eapply value_function;
      [reflexivity |exact SYMBOL |reflexivity].
  - apply no_argument_values.
  - cbn; exact FUNCTION.
  - reflexivity.
Qed.

Theorem actual_initialization_private_body : ~ In _host_initialize public_idents.
Proof.
  assert (ABSENT : existsb (Pos.eqb _host_initialize) public_idents = false) by (vm_compute; reflexivity).
  intro MEMBER.
  assert (PRESENT : existsb (Pos.eqb _host_initialize) public_idents = true).
  { apply existsb_exists; exists _host_initialize; split; [exact MEMBER |apply Pos.eqb_refl]. }
  congruence.
Qed.

Definition initialization_callback_address (definition : ident * globdef (Ctypes.fundef function) type) : bool :=
  match snd definition with
  | Gvar variable => existsb (fun datum => match datum with
      | Init_addrof target _ => Pos.eqb target _host_initialize | _ => false end) (gvar_init variable)
  | Gfun _ => false
  end.

Theorem actual_initialization_body_not_registered :
  existsb initialization_callback_address global_definitions = false.
Proof. vm_compute; reflexivity. Qed.

Theorem initialization_body_no_global_callback identifier variable offset :
  In (identifier, Gvar variable) global_definitions ->
  ~ In (Init_addrof _host_initialize offset) (gvar_init variable).
Proof.
  intros REGISTERED ADDRESS.
  assert (LOCAL : existsb (fun datum => match datum with
    | Init_addrof target _ => Pos.eqb target _host_initialize | _ => false end) (gvar_init variable) = true).
  { apply existsb_exists; exists (Init_addrof _host_initialize offset); split;
      [exact ADDRESS |reflexivity]. }
  assert (GLOBAL : existsb initialization_callback_address global_definitions = true).
  { apply existsb_exists; exists (identifier, Gvar variable); split; [exact REGISTERED |exact LOCAL]. }
  rewrite actual_initialization_body_not_registered in GLOBAL; discriminate.
Qed.
