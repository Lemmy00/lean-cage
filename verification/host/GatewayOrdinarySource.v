(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Ordinary application calls exclude initializer entries. *)
From Stdlib Require Import List Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Cop Clight.
Require Import Machine ClightSteps LocalAccess.
From HostGateway Require Import GatewaySource GatewayRegistry GatewayBindings GatewayGlobalAddresses
  GatewayLinkedSource GatewayStackAllocation.
Import ListNotations.
Local Opaque prog.

Definition gateway_ordinary_signature (arguments : list type) (result : type) : bool :=
  match arguments, result with [], Tpointer _ _ => false | _, _ => true end.
Definition gateway_ordinary_function body :=
  gateway_ordinary_signature (type_of_params (fn_params body)) (fn_return body).
Definition gateway_ordinary_definition definition :=
  match definition with Internal body => gateway_ordinary_function body | External _ _ _ _ => true end.

Definition gateway_ordinary_callee expression : bool :=
  match classify_fun (typeof expression) with
  | fun_case_f arguments result _ =>
      gateway_ordinary_signature arguments result ||
      match expression with
      | Evar identifier (Tfunction _ _ _) =>
          match gateway_program_definition identifier global_definitions with
          | Some (Gfun (External _ _ _ _)) => true
          | _ => false
          end
      | _ => false
      end
  | _ => false
  end.

Definition gateway_ordinary_action body :=
  match body with
  | Sassign (Evar identifier _) _ => negb (gateway_private_cell_name identifier)
  | Scall _ expression _ => gateway_ordinary_callee expression
  | _ => true
  end.

Fixpoint gateway_ordinary_statement body : bool :=
  gateway_ordinary_action body && match body with
  | Ssequence first second | Sifthenelse _ first second | Sloop first second =>
      gateway_ordinary_statement first && gateway_ordinary_statement second
  | Sswitch _ branches => gateway_ordinary_branches branches
  | Slabel _ nested => gateway_ordinary_statement nested
  | _ => true
  end
with gateway_ordinary_branches branches : bool :=
  match branches with LSnil => true | LScons _ body rest =>
    gateway_ordinary_statement body && gateway_ordinary_branches rest end.

Definition gateway_source_name identifier := existsb (Pos.eqb identifier) (map fst global_definitions).
Definition gateway_ordinary_entry (entry : ident * globdef (Ctypes.fundef function) type) :=
  match snd entry with
  | Gfun (Internal body) =>
      negb (gateway_ordinary_function body) ||
        (gateway_ordinary_statement (fn_body body) &&
         forallb (fun local => negb (gateway_source_name (fst local))) (fn_vars body))
  | _ => true
  end.

Theorem actual_gateway_ordinary_source : forallb gateway_ordinary_entry global_definitions = true.
Proof. vm_compute; reflexivity. Qed.

Definition gateway_global_names_unshadowed (environment : env) : Prop :=
  forall identifier, gateway_source_name identifier = true -> environment ! identifier = None.

Theorem gateway_source_name_present identifier definition :
  In (identifier, definition) global_definitions -> gateway_source_name identifier = true.
Proof.
  intro MEMBER; apply existsb_exists; exists identifier; split; [apply in_map_iff; exists (identifier, definition); split; [reflexivity |exact MEMBER] |apply Pos.eqb_refl].
Qed.

Theorem gateway_actual_ordinary_body identifier body :
  In (identifier, Gfun (Internal body)) global_definitions ->
  gateway_ordinary_function body = true ->
  gateway_ordinary_statement (fn_body body) = true /\
  forall name, gateway_source_name name = true -> ~ In name (map fst (fn_vars body)).
Proof.
  intros MEMBER ORDINARY.
  pose proof (proj1 (forallb_forall _ _) actual_gateway_ordinary_source
    (identifier, Gfun (Internal body)) MEMBER) as PROFILE.
  change ((negb (gateway_ordinary_function body) ||
    (gateway_ordinary_statement (fn_body body) &&
     forallb (fun local => negb (gateway_source_name (fst local))) (fn_vars body))) = true) in PROFILE.
  rewrite ORDINARY in PROFILE; cbn in PROFILE.
  apply andb_true_iff in PROFILE as [BODY LOCALS]; split; [exact BODY |].
  intros name GLOBAL PRESENT; apply in_map_iff in PRESENT as [[local ty] [SAME PRESENT]]; cbn in SAME; subst local.
  pose proof (proj1 (forallb_forall _ _) LOCALS (name, ty) PRESENT) as ABSENT.
  change (negb (gateway_source_name name) = true) in ABSENT; rewrite GLOBAL in ABSENT; discriminate.
Qed.

Theorem gateway_linked_ordinary_body runtime value body :
  forallb gateway_runtime_function runtime = true ->
  Genv.find_funct (Clight.globalenv (gateway_linked_program runtime)) value = Some (Internal body) ->
  gateway_ordinary_function body = true ->
  gateway_ordinary_statement (fn_body body) = true /\
  forall identifier, gateway_source_name identifier = true -> ~ In identifier (map fst (fn_vars body)).
Proof.
  intros RUNTIME FOUND ORDINARY.
  destruct (gateway_linked_internal_origin runtime value body RUNTIME FOUND) as [identifier MEMBER].
  pose proof (proj1 (forallb_forall _ _) actual_gateway_ordinary_source
    (identifier, Gfun (Internal body)) MEMBER) as PROFILE.
  change ((negb (gateway_ordinary_function body) ||
    (gateway_ordinary_statement (fn_body body) &&
     forallb (fun local => negb (gateway_source_name (fst local))) (fn_vars body))) = true) in PROFILE.
  rewrite ORDINARY in PROFILE; cbn in PROFILE.
  apply andb_true_iff in PROFILE as [BODY LOCALS]; split; [exact BODY |].
  intros name GLOBAL PRESENT; apply in_map_iff in PRESENT as [[local ty] [SAME PRESENT]]; cbn in SAME; subst local.
  pose proof (proj1 (forallb_forall _ _) LOCALS (name, ty) PRESENT) as ABSENT.
  change (negb (gateway_source_name name) = true) in ABSENT; rewrite GLOBAL in ABSENT; discriminate.
Qed.

Theorem gateway_ordinary_called_definition runtime environment temporaries memory expression value definition arguments result convention :
  gateway_runtime_registration runtime -> gateway_global_names_unshadowed environment ->
  gateway_ordinary_callee expression = true ->
  classify_fun (typeof expression) = fun_case_f arguments result convention ->
  eval_expr (Clight.globalenv (gateway_linked_program runtime)) environment temporaries memory expression value ->
  Genv.find_funct (Clight.globalenv (gateway_linked_program runtime)) value = Some definition ->
  type_of_fundef definition = Tfunction arguments result convention -> gateway_ordinary_definition definition = true.
Proof.
  intros REGISTERED GLOBALS PROFILE SIGNATURE EVALUATED FOUND TYPE.
  unfold gateway_ordinary_callee in PROFILE; rewrite SIGNATURE in PROFILE.
  apply orb_true_iff in PROFILE as [ORDINARY |DIRECT].
  - destruct definition as [body |]; [|reflexivity].
    cbn [type_of_fundef] in TYPE; inversion TYPE; subst.
    exact ORDINARY.
  - destruct expression; try discriminate DIRECT; destruct t; try discriminate DIRECT.
    destruct (gateway_program_definition i global_definitions) as [[actual |variable] |] eqn:LOOKUP;
      try discriminate DIRECT; destruct actual as [body |external types return_type calling]; try discriminate DIRECT.
    pose proof (gateway_program_definition_present _ _ _ LOOKUP) as MEMBER.
    destruct (gateway_linked_source_binding runtime i (External external types return_type calling) REGISTERED MEMBER)
      as [symbol [SYMBOL FUNCTION]].
    assert (ACTUAL : expression_value (Clight.globalenv (gateway_linked_program runtime))
      environment temporaries memory (Evar i (Tfunction l t c)) (Vptr symbol Ptrofs.zero)).
    { apply old_expression_value, value_function;
        [apply GLOBALS; eapply gateway_source_name_present; exact MEMBER |exact SYMBOL |reflexivity]. }
    destruct ACTUAL as [REAL UNIQUE]; pose proof (UNIQUE _ EVALUATED) as SAME; subst value.
    change (Genv.find_funct_ptr (Clight.globalenv (gateway_linked_program runtime)) symbol = Some definition) in FOUND.
    rewrite FUNCTION in FOUND; inversion FOUND; reflexivity.
Qed.

Theorem gateway_ordinary_entry_unshadowed ge body arguments before environment temporaries after :
  (forall identifier, gateway_source_name identifier = true -> ~ In identifier (map fst (fn_vars body))) ->
  function_entry2 ge body arguments before environment temporaries after -> gateway_global_names_unshadowed environment.
Proof.
  intros LOCALS ENTRY; inversion ENTRY; subst; intros identifier GLOBAL.
  erewrite gateway_alloc_variables_lookup; [apply PTree.gempty |eassumption |apply LOCALS; exact GLOBAL].
Qed.
