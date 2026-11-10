(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Actual exported and registered entries classify callbacks. *)
From Stdlib Require Import List Bool.
From compcert Require Import Coqlib Maps AST Values Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayRegistry GatewayLinkedSource GatewayOrdinarySource.
Import ListNotations.

Definition gateway_callback_export identifier := existsb (Pos.eqb identifier) public_idents.
Definition gateway_callback_relocation identifier (entry : ident * globdef (Ctypes.fundef function) type) :=
  match snd entry with
  | Gvar variable => existsb (fun datum => match datum with
      | Init_addrof target _ => Pos.eqb identifier target | _ => false end) (gvar_init variable)
  | _ => false
  end.

Fixpoint gateway_callback_expression identifier expression : bool :=
  match expression with
  | Evar name (Tfunction _ _ _) => Pos.eqb identifier name
  | Ederef nested _ | Eaddrof nested _ | Eunop _ nested _ | Ecast nested _ | Efield nested _ _ =>
      gateway_callback_expression identifier nested
  | Ebinop _ first second _ => gateway_callback_expression identifier first || gateway_callback_expression identifier second
  | _ => false
  end.

(* Direct C calls enter their source body; they do not hand the callee address
   to the SDK. Function values in arguments, stores and conditions are retained,
   including the real sigaction handler and loader-address query. *)
Fixpoint gateway_callback_body identifier body : bool :=
  match body with
  | Sassign first second => gateway_callback_expression identifier first || gateway_callback_expression identifier second
  | Sset _ value | Sreturn (Some value) => gateway_callback_expression identifier value
  | Scall _ _ arguments | Sbuiltin _ _ _ arguments => existsb (gateway_callback_expression identifier) arguments
  | Ssequence first second | Sloop first second => gateway_callback_body identifier first || gateway_callback_body identifier second
  | Sifthenelse condition first second => gateway_callback_expression identifier condition ||
      gateway_callback_body identifier first || gateway_callback_body identifier second
  | Sswitch condition branches => gateway_callback_expression identifier condition || gateway_callback_cases identifier branches
  | Slabel _ nested => gateway_callback_body identifier nested
  | _ => false
  end
with gateway_callback_cases identifier branches : bool :=
  match branches with
  | LSnil => false
  | LScons _ body rest => gateway_callback_body identifier body || gateway_callback_cases identifier rest
  end.

Definition gateway_callback_dynamic identifier (entry : ident * globdef (Ctypes.fundef function) type) :=
  match snd entry with Gfun (Internal body) => gateway_callback_body identifier (fn_body body) | _ => false end.

Definition gateway_callback_registered identifier :=
  gateway_callback_export identifier ||
    (existsb (gateway_callback_relocation identifier) global_definitions ||
     existsb (gateway_callback_dynamic identifier) global_definitions).

Definition gateway_callback_entry_profile (entry : ident * globdef (Ctypes.fundef function) type) :=
  match snd entry with
  | Gfun (Internal body) => negb (gateway_callback_registered (fst entry)) ||
      gateway_ordinary_function body || Pos.eqb (fst entry) _PyInit__host
  | _ => true
  end.

Theorem actual_gateway_callback_entries : forallb gateway_callback_entry_profile global_definitions = true.
Proof. vm_compute; reflexivity. Qed.

Theorem actual_private_initializer_not_callback : gateway_callback_registered _host_initialize = false.
Proof. vm_compute; reflexivity. Qed.

Theorem actual_native_signal_handler_callback : gateway_callback_registered _host_cli_signal = true.
Proof. vm_compute; reflexivity. Qed.

Lemma gateway_program_definition_unique definitions identifier definition :
  list_norepet (map fst definitions) -> In (identifier, definition) definitions ->
  gateway_program_definition identifier definitions = Some definition.
Proof.
  induction definitions as [|[name current] rest IH]; cbn; intros UNIQUE MEMBER; [contradiction |].
  inversion UNIQUE; subst; destruct MEMBER as [SAME |MEMBER].
  - inversion SAME; subst; rewrite Pos.eqb_refl; reflexivity.
  - destruct (Pos.eqb identifier name) eqn:SAME.
    + apply Pos.eqb_eq in SAME; subst name; exfalso.
      apply H1; apply in_map_iff; exists (identifier, definition); split; [reflexivity |exact MEMBER].
    + apply IH; assumption.
Qed.

Theorem gateway_actual_callback_kind identifier body :
  In (identifier, Gfun (Internal body)) global_definitions -> gateway_callback_registered identifier = true ->
  gateway_ordinary_function body = true \/ body = f_PyInit__host.
Proof.
  intros SOURCE REGISTERED.
  pose proof (proj1 (forallb_forall _ _) actual_gateway_callback_entries
    (identifier, Gfun (Internal body)) SOURCE) as CLASSIFIED.
  change ((negb (gateway_callback_registered identifier) || gateway_ordinary_function body ||
    Pos.eqb identifier _PyInit__host) = true) in CLASSIFIED.
  rewrite REGISTERED in CLASSIFIED.
  apply orb_true_iff in CLASSIFIED as [ORDINARY |INITIALIZER].
  - left; exact ORDINARY.
  - right; apply Pos.eqb_eq in INITIALIZER; subst identifier.
    pose proof (gateway_program_definition_unique global_definitions _ _ actual_gateway_source_names_unique SOURCE) as EXACT.
    change (@Some (globdef (Ctypes.fundef function) type) (Gfun (Internal f_PyInit__host)) = Some (Gfun (Internal body))) in EXACT.
    congruence.
Qed.

Theorem gateway_callback_relocation_registered owner variable identifier delta :
  In (owner, Gvar variable) global_definitions -> In (Init_addrof identifier delta) (gvar_init variable) ->
  gateway_callback_registered identifier = true.
Proof.
  intros OWNER RELOCATION; apply orb_true_iff; right; apply orb_true_iff; left; apply existsb_exists.
  exists (owner, Gvar variable); split; [exact OWNER |].
  change (existsb (fun datum => match datum with
    | Init_addrof target _ => Pos.eqb identifier target | _ => false end) (gvar_init variable) = true); apply existsb_exists; exists (Init_addrof identifier delta).
  split; [exact RELOCATION |apply Pos.eqb_refl].
Qed.

Theorem gateway_callback_body_registered owner body identifier :
  In (owner, Gfun (Internal body)) global_definitions ->
  gateway_callback_body identifier (fn_body body) = true -> gateway_callback_registered identifier = true.
Proof.
  intros OWNER EXPOSED; apply orb_true_iff; right; apply orb_true_iff; right; apply existsb_exists.
  exists (owner, Gfun (Internal body)); split; [exact OWNER |exact EXPOSED].
Qed.
