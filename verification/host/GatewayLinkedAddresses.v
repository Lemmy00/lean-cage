(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Genuine SDK extensions preserve actual source global addresses. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps AST Values Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayRegistry GatewayLinkedSource GatewayGlobalAddresses.
Import ListNotations.
Local Opaque prog.

Definition gateway_environment_core (first second : Genv.t (Ctypes.fundef function) type) : Prop :=
  Genv.genv_symb first = Genv.genv_symb second /\
  Genv.genv_defs first = Genv.genv_defs second /\ Genv.genv_next first = Genv.genv_next second.

Lemma gateway_environment_core_add first second definition :
  gateway_environment_core first second ->
  gateway_environment_core (Genv.add_global first definition) (Genv.add_global second definition).
Proof.
  intros [SYMBOLS [DEFINITIONS NEXT]]; destruct definition as [identifier definition].
  change (PTree.set identifier (Genv.genv_next first) (Genv.genv_symb first) =
      PTree.set identifier (Genv.genv_next second) (Genv.genv_symb second) /\
    PTree.set (Genv.genv_next first) definition (Genv.genv_defs first) =
      PTree.set (Genv.genv_next second) definition (Genv.genv_defs second) /\
    Pos.succ (Genv.genv_next first) = Pos.succ (Genv.genv_next second));
    rewrite SYMBOLS, DEFINITIONS, NEXT; repeat split; reflexivity.
Qed.

Lemma gateway_environment_core_globals definitions first second :
  gateway_environment_core first second ->
  gateway_environment_core (Genv.add_globals first definitions) (Genv.add_globals second definitions).
Proof.
  revert first second; induction definitions as [|definition rest IH]; intros first second SAME;
    [exact SAME |apply IH, gateway_environment_core_add; exact SAME].
Qed.

Lemma gateway_source_public_core (public : list ident) :
  gateway_environment_core
    (Genv.add_globals (Genv.empty_genv (Ctypes.fundef function) type public) (Ctypes.prog_defs prog)) (Genv.globalenv prog).
Proof.
  apply gateway_environment_core_globals; repeat split; reflexivity.
Qed.

Theorem gateway_linked_source_symbol runtime identifier definition :
  gateway_runtime_registration runtime -> In (identifier, definition) global_definitions ->
  Genv.find_symbol (Clight.globalenv (gateway_linked_program runtime)) identifier =
    Genv.find_symbol (Clight.globalenv prog) identifier.
Proof.
  intros [_ [UNIQUE SEPARATE]] MEMBER.
  change (Genv.find_symbol
    (Genv.add_globals (Genv.empty_genv (Ctypes.fundef function) type (Ctypes.prog_public prog ++ map fst runtime))
      (Ctypes.prog_defs prog ++ map (fun entry => (fst entry, Gfun (snd entry))) runtime)) identifier =
    Genv.find_symbol (Genv.globalenv prog) identifier).
  rewrite Genv.add_globals_app.
  eapply Genv.add_globals_unique_preserves with (id := identifier).
  - intros ge name current SAME _ OTHER.
    change ((PTree.set name (Genv.genv_next ge) (Genv.genv_symb ge)) ! identifier =
      (Genv.genv_symb (Genv.globalenv prog)) ! identifier).
    rewrite PTree.gso by congruence; exact SAME.
  - rewrite map_map; intro RUNTIME.
    exact (SEPARATE identifier identifier (in_map fst _ _ MEMBER) RUNTIME eq_refl).
  - unfold Genv.find_symbol; rewrite (proj1 (gateway_source_public_core (Ctypes.prog_public prog ++ map fst runtime)));
      reflexivity.
Qed.

Theorem gateway_linked_private_symbol runtime identifier :
  gateway_runtime_registration runtime -> gateway_private_cell_name identifier = true ->
  Genv.find_symbol (Clight.globalenv (gateway_linked_program runtime)) identifier =
    Genv.find_symbol (Clight.globalenv prog) identifier.
Proof.
  intros REGISTERED PRIVATE.
  destruct (gateway_private_cell_initializers identifier PRIVATE) as [variable [DEFINITION REST]].
  eapply gateway_linked_source_symbol; [exact REGISTERED |].
  eapply gateway_program_definition_present; exact DEFINITION.
Qed.

Theorem gateway_linked_private_cells runtime object :
  gateway_runtime_registration runtime ->
  (gateway_private_cell (Clight.globalenv (gateway_linked_program runtime)) object <->
    gateway_private_cell (Clight.globalenv prog) object).
Proof.
  intro REGISTERED; split; intros [identifier [PRIVATE SYMBOL]]; exists identifier; split; [exact PRIVATE | |exact PRIVATE |].
  - rewrite <- (gateway_linked_private_symbol runtime identifier REGISTERED PRIVATE); exact SYMBOL.
  - rewrite (gateway_linked_private_symbol runtime identifier REGISTERED PRIVATE); exact SYMBOL.
Qed.
