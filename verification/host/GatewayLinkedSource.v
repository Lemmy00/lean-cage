(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Genuine runtime callbacks extend the actual source unit. *)
From Stdlib Require Import List Bool.
From compcert Require Import Coqlib Maps AST Values Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayRegistry GatewayPointerControl GatewayBindings.
Import ListNotations.
Local Opaque prog.

Definition gateway_runtime_function (entry : ident * Ctypes.fundef function) : bool :=
  match snd entry with External _ _ _ _ => true | Internal _ => false end.

Definition gateway_linked_program (runtime : list (ident * Ctypes.fundef function)) : Clight.program :=
  {| Ctypes.prog_defs := Ctypes.prog_defs prog ++ map (fun entry => (fst entry, Gfun (snd entry))) runtime;
     Ctypes.prog_public := Ctypes.prog_public prog ++ map fst runtime;
     Ctypes.prog_main := Ctypes.prog_main prog;
     Ctypes.prog_types := Ctypes.prog_types prog;
     Ctypes.prog_comp_env := Ctypes.prog_comp_env prog;
     Ctypes.prog_comp_env_eq := Ctypes.prog_comp_env_eq prog |}.

Theorem gateway_linked_composite_layout runtime :
  Clight.genv_cenv (Clight.globalenv (gateway_linked_program runtime)) = Clight.genv_cenv (Clight.globalenv prog).
Proof. cbv beta iota zeta delta [Clight.globalenv gateway_linked_program Clight.genv_cenv Ctypes.prog_comp_env]; reflexivity. Qed.


Theorem gateway_linked_internal_origin runtime value body :
  forallb gateway_runtime_function runtime = true ->
  Genv.find_funct (Clight.globalenv (gateway_linked_program runtime)) value = Some (Internal body) ->
  exists identifier, In (identifier, Gfun (Internal body)) global_definitions.
Proof.
  intros RUNTIME FOUND.
  change (Genv.find_funct (Genv.globalenv (gateway_linked_program runtime)) value = Some (Internal body)) in FOUND.
  destruct (@Genv.find_funct_inversion (Ctypes.fundef function) type
    (gateway_linked_program runtime) value (Internal body) FOUND) as [identifier MEMBER].
  change (In (identifier, Gfun (Internal body))
    (Ctypes.prog_defs prog ++ map (fun entry => (fst entry, Gfun (snd entry))) runtime)) in MEMBER.
  apply in_app_or in MEMBER as [SOURCE |FOREIGN].
  - exists identifier; rewrite gateway_actual_program_definitions in SOURCE; exact SOURCE.
  - apply in_map_iff in FOREIGN as [[name definition] [SAME REGISTERED]].
    cbn in SAME; inversion SAME; subst.
    pose proof (proj1 (forallb_forall _ _) RUNTIME (identifier, Internal body) REGISTERED) as EXTERNAL.
    discriminate EXTERNAL.
Qed.

Theorem gateway_linked_pointer_function runtime value definition :
  forallb gateway_runtime_function runtime = true ->
  Genv.find_funct (Clight.globalenv (gateway_linked_program runtime)) value = Some definition ->
  gateway_pointer_definition definition = true.
Proof.
  intros RUNTIME FOUND; destruct definition as [body |]; [|reflexivity].
  destruct (gateway_linked_internal_origin runtime value body RUNTIME FOUND) as [identifier MEMBER].
  exact (proj1 (forallb_forall _ _) actual_gateway_pointer_control (identifier, Gfun (Internal body)) MEMBER).
Qed.

Theorem gateway_linked_empty : gateway_linked_program [] = prog.
Proof. unfold gateway_linked_program; destruct prog; cbn; rewrite !app_nil_r; reflexivity. Qed.

Theorem actual_gateway_source_names_unique : list_norepet (map fst global_definitions).
Proof.
  assert (CERT : (if list_norepet_dec peq (map fst global_definitions) then true else false) = true).
  { vm_compute; reflexivity. }
  destruct (list_norepet_dec peq (map fst global_definitions)); [assumption |discriminate CERT].
Qed.

Definition gateway_runtime_registration runtime : Prop :=
  forallb gateway_runtime_function runtime = true /\
  list_norepet (map fst runtime) /\ list_disjoint (map fst global_definitions) (map fst runtime).

Theorem gateway_linked_names_unique runtime :
  gateway_runtime_registration runtime -> list_norepet (prog_defs_names (gateway_linked_program runtime)).
Proof.
  intros [_ [UNIQUE SEPARATE]].
  unfold prog_defs_names; change (list_norepet (map fst
    (Ctypes.prog_defs prog ++ map (fun entry => (fst entry, Gfun (snd entry))) runtime))).
  rewrite map_app, map_map, gateway_actual_program_definitions.
  apply list_norepet_app; repeat split; assumption || apply actual_gateway_source_names_unique.
Qed.

Theorem gateway_linked_source_binding runtime identifier definition :
  gateway_runtime_registration runtime -> In (identifier, Gfun definition) global_definitions ->
  gateway_function_binding (Clight.globalenv (gateway_linked_program runtime)) identifier definition.
Proof.
  intros REGISTERED SOURCE.
  assert (DEFINED : (prog_defmap (gateway_linked_program runtime)) ! identifier = Some (Gfun definition)).
  { apply prog_defmap_norepet; [apply gateway_linked_names_unique; exact REGISTERED |].
    change (In (identifier, Gfun definition)
      (Ctypes.prog_defs prog ++ map (fun entry => (fst entry, Gfun (snd entry))) runtime)).
    apply in_or_app; left; rewrite gateway_actual_program_definitions; exact SOURCE. }
  destruct (proj1 (Genv.find_def_symbol _ _ _) DEFINED) as [object [SYMBOL DEFINITION]].
  exists object; split; [exact SYMBOL |apply Genv.find_funct_ptr_iff; exact DEFINITION].
Qed.

Theorem gateway_linked_runtime_binding runtime identifier definition :
  gateway_runtime_registration runtime -> In (identifier, definition) runtime ->
  gateway_function_binding (Clight.globalenv (gateway_linked_program runtime)) identifier definition.
Proof.
  intros REGISTERED RUNTIME.
  assert (DEFINED : (prog_defmap (gateway_linked_program runtime)) ! identifier = Some (Gfun definition)).
  { apply prog_defmap_norepet; [apply gateway_linked_names_unique; exact REGISTERED |].
    change (In (identifier, Gfun definition)
      (Ctypes.prog_defs prog ++ map (fun entry => (fst entry, Gfun (snd entry))) runtime)).
    apply in_or_app; right; apply in_map_iff; exists (identifier, definition); split; [reflexivity |exact RUNTIME]. }
  destruct (proj1 (Genv.find_def_symbol _ _ _) DEFINED) as [object [SYMBOL DEFINITION]].
  exists object; split; [exact SYMBOL |apply Genv.find_funct_ptr_iff; exact DEFINITION].
Qed.
