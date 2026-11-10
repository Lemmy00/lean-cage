(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: All source fcntl calls use status or CLOEXEC duplication. *)
From Stdlib Require Import ZArith List Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Ctypesdefs Cop Clight.
From HostGateway Require Import GatewaySource GatewayRegistry GatewaySpawnABI GatewayMachine.
Import ListNotations.

Definition gateway_fcntl_shape (ty : type) : bool :=
  match classify_fun ty with
  | fun_case_f [Tint I32 Signed _; Tint I32 Signed _; Tint I32 Signed _] (Tint I32 Signed _) _ => true
  | _ => false
  end.

Definition gateway_fcntl_command (value : int) : bool :=
  Int.eq value (Int.repr 3) || Int.eq value (Int.repr 4) || Int.eq value (Int.repr 1030).

Definition gateway_fcntl_local (body : statement) : bool :=
  match body with
  | Scall _ expression arguments =>
    if gateway_fcntl_shape (typeof expression) then
      match arguments with
      | [_; Econst_int command ty; _] => if type_eq ty tint then gateway_fcntl_command command else false
      | _ => false
      end
    else true
  | _ => true
  end.

Fixpoint gateway_fcntl_statement (body : statement) : bool :=
  gateway_fcntl_local body &&
    match body with
    | Ssequence first second | Sifthenelse _ first second | Sloop first second =>
      gateway_fcntl_statement first && gateway_fcntl_statement second
    | Sswitch _ branches => gateway_fcntl_branches branches
    | Slabel _ nested => gateway_fcntl_statement nested
    | _ => true
    end
with gateway_fcntl_branches (branches : labeled_statements) : bool :=
  match branches with
  | LSnil => true
  | LScons _ body rest => gateway_fcntl_statement body && gateway_fcntl_branches rest
  end.

Definition gateway_fcntl_definition definition :=
  match definition with Internal function => gateway_fcntl_statement (fn_body function) | External _ _ _ _ => true end.
Definition gateway_fcntl_definition_entry (entry : ident * globdef (Ctypes.fundef function) type) :=
  match snd entry with Gfun definition => gateway_fcntl_definition definition | Gvar _ => true end.

Theorem actual_gateway_fcntl_profile : forallb gateway_fcntl_definition_entry global_definitions = true.
Proof. vm_compute; reflexivity. Qed.
