(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Private class and guard cell addresses are not application values. *)
From Stdlib Require Import ZArith List Bool Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayRegistry GatewayInitializationInventory
  GatewayPointerOrigins GatewayPointerMemory GatewayPointerExpressions GatewayLoaderRegions.
Import ListNotations.

Definition gateway_private_cell_name identifier :=
  existsb (Pos.eqb identifier)
    [_host_path_class; _host_cancellation_class; _host_outcome_class; _host_initializing; _host_initialized].

Definition gateway_private_cell (ge : Clight.genv) object : Prop :=
  exists identifier, gateway_private_cell_name identifier = true /\ Genv.find_symbol ge identifier = Some object.

Theorem gateway_private_cell_initializers identifier :
  gateway_private_cell_name identifier = true ->
  exists variable,
    gateway_program_definition identifier global_definitions = Some (Gvar variable) /\
    gvar_volatile variable = false /\ 0 < init_data_list_size (gvar_init variable).
Proof.
  unfold gateway_private_cell_name; intro SELECTED; apply existsb_exists in SELECTED.
  destruct SELECTED as [name [MEMBER SAME]]; apply Pos.eqb_eq in SAME; subst name.
  cbn [In] in MEMBER; repeat destruct MEMBER as [SAME |MEMBER]; try contradiction; subst identifier.
  - exists v_host_path_class; repeat split; vm_compute; reflexivity.
  - exists v_host_cancellation_class; repeat split; vm_compute; reflexivity.
  - exists v_host_outcome_class; repeat split; vm_compute; reflexivity.
  - exists v_host_initializing; repeat split; vm_compute; reflexivity.
  - exists v_host_initialized; repeat split; vm_compute; reflexivity.
Qed.

Theorem gateway_loaded_private_cells_valid ge memory :
  gateway_native_loader_boundary ge memory ->
  forall object, gateway_private_cell ge object -> Mem.valid_block memory object.
Proof.
  intros LOADER object [identifier [PRIVATE SYMBOL]].
  destruct (gateway_private_cell_initializers identifier PRIVATE) as [variable [DEFINITION [NONVOLATILE POSITIVE]]].
  destruct (gateway_native_initialized ge memory LOADER identifier variable DEFINITION NONVOLATILE POSITIVE)
    as [actual [_ [_ [BOUND REGION]]]].
  assert (SAME : actual = object) by congruence; subst actual.
  eapply Mem.perm_valid_block; apply (gateway_loaded_region_readable ge memory variable object REGION 0); lia.
Qed.

Theorem gateway_nonprivate_symbol (ge : Clight.genv) identifier object :
  Genv.find_symbol ge identifier = Some object ->
  gateway_global_address_allowed gateway_private_cell_name identifier = true -> ~ gateway_private_cell ge object.
Proof.
  intros SYMBOL ALLOWED [private [PRIVATE SAME]].
  assert (DISTINCT : identifier <> private).
  { intro EQUAL; subst; unfold gateway_global_address_allowed in ALLOWED; rewrite PRIVATE in ALLOWED; discriminate. }
  exact (Genv.global_addresses_distinct ge DISTINCT SYMBOL SAME eq_refl).
Qed.

Definition gateway_assignment_address_inputs expression :=
  match expression with
  | Evar _ _ => true
  | Ederef nested _ | Efield nested _ _ => gateway_expression_addresses gateway_private_cell_name nested
  | _ => false
  end.

Definition gateway_statement_addresses body :=
  match body with
  | Sassign lhs rhs => gateway_assignment_address_inputs lhs &&
      gateway_expression_addresses gateway_private_cell_name rhs
  | Sset _ expression | Sifthenelse expression _ _ | Sswitch expression _ =>
      gateway_expression_addresses gateway_private_cell_name expression
  | Scall _ function arguments => gateway_expression_addresses gateway_private_cell_name function &&
      forallb (gateway_expression_addresses gateway_private_cell_name) arguments
  | Sbuiltin _ _ _ arguments => forallb (gateway_expression_addresses gateway_private_cell_name) arguments
  | Sreturn (Some expression) => gateway_expression_addresses gateway_private_cell_name expression
  | _ => true
  end.

Definition gateway_source_addresses (entry : ident * globdef (Ctypes.fundef function) type) :=
  match snd entry with
  | Gfun (Internal function) =>
      negb (initialization_statement_any (fun body => negb (gateway_statement_addresses body)) (fn_body function))
  | Gvar variable => negb (existsb (fun datum => match datum with
      | Init_addrof identifier _ => gateway_private_cell_name identifier | _ => false end) (gvar_init variable))
  | _ => true
  end.

Theorem actual_gateway_private_address_inventory : forallb gateway_source_addresses global_definitions = true.
Proof. vm_compute; reflexivity. Qed.

Theorem gateway_actual_function_address_inventory identifier function :
  In (identifier, Gfun (Internal function)) global_definitions ->
  initialization_statement_any (fun body => negb (gateway_statement_addresses body)) (fn_body function) = false.
Proof.
  intro MEMBER; pose proof (proj1 (forallb_forall _ _) actual_gateway_private_address_inventory
    (identifier, Gfun (Internal function)) MEMBER) as SCOPED.
  cbn [gateway_source_addresses] in SCOPED; apply negb_true_iff; exact SCOPED.
Qed.

Theorem gateway_actual_initializer_address_absent identifier variable offset private :
  In (identifier, Gvar variable) global_definitions -> gateway_private_cell_name private = true ->
  ~ In (Init_addrof private offset) (gvar_init variable).
Proof.
  intros MEMBER PRIVATE ADDRESS.
  pose proof (proj1 (forallb_forall _ _) actual_gateway_private_address_inventory
    (identifier, Gvar variable) MEMBER) as SCOPED.
  cbn [gateway_source_addresses] in SCOPED; apply negb_true_iff in SCOPED.
  assert (EXPOSED : existsb (fun datum => match datum with
      | Init_addrof target _ => gateway_private_cell_name target | _ => false end) (gvar_init variable) = true).
  { apply existsb_exists; exists (Init_addrof private offset); split; [exact ADDRESS |exact PRIVATE]. }
  congruence.
Qed.

Theorem gateway_private_arguments (ge : Clight.genv) (environment : env) (temporaries : temp_env)
    memory expressions types values :
  (forall identifier object ty, environment ! identifier = Some (object, ty) -> ~ gateway_private_cell ge object) ->
  (forall identifier value, temporaries ! identifier = Some value -> gateway_pointer_avoids (gateway_private_cell ge) value) ->
  gateway_memory_avoids (gateway_private_cell ge) memory ->
  Forall (fun expression => gateway_expression_addresses gateway_private_cell_name expression = true) expressions ->
  eval_exprlist ge environment temporaries memory expressions types values ->
  Forall (gateway_pointer_avoids (gateway_private_cell ge)) values.
Proof.
  intros LOCALS TEMPORARIES MEMORY SCOPED EVALUATED.
  pose proof (proj1 (gateway_expression_lvalue_avoids ge environment temporaries memory
    (gateway_private_cell ge) gateway_private_cell_name LOCALS
    (gateway_nonprivate_symbol ge) TEMPORARIES MEMORY)) as EXPRESSIONS.
  induction EVALUATED; [constructor |].
  inversion SCOPED; subst; constructor.
  - eapply gateway_cast_avoids; [eapply EXPRESSIONS; eassumption |eassumption].
  - apply IHEVALUATED; assumption.
Qed.

Theorem gateway_assignment_private_target (ge : Clight.genv) (environment : env) (temporaries : temp_env)
    memory expression object offset field :
  (forall identifier object ty, environment ! identifier = Some (object, ty) -> ~ gateway_private_cell ge object) ->
  (forall identifier value, temporaries ! identifier = Some value -> gateway_pointer_avoids (gateway_private_cell ge) value) ->
  gateway_memory_avoids (gateway_private_cell ge) memory ->
  gateway_assignment_address_inputs expression = true ->
  eval_lvalue ge environment temporaries memory expression object offset field ->
  gateway_private_cell ge object ->
  exists identifier ty, expression = Evar identifier ty /\ gateway_private_cell_name identifier = true /\
    environment ! identifier = None /\ Genv.find_symbol ge identifier = Some object.
Proof.
  intros LOCALS TEMPORARIES MEMORY SCOPED LOCATION PRIVATE.
  pose proof (proj1 (gateway_expression_lvalue_avoids ge environment temporaries memory
    (gateway_private_cell ge) gateway_private_cell_name LOCALS
    (gateway_nonprivate_symbol ge) TEMPORARIES MEMORY)) as EXPRESSIONS.
  inversion LOCATION; subst.
  - exfalso; exact (LOCALS _ _ _ H PRIVATE).
  - exists id, ty; split; [reflexivity |]. split.
    + destruct (gateway_private_cell_name id) eqn:NAME; [reflexivity |].
      exfalso; eapply gateway_nonprivate_symbol; [exact H0 |unfold gateway_global_address_allowed; rewrite NAME; reflexivity |exact PRIVATE].
    + split; assumption.
  - exfalso; exact (EXPRESSIONS _ _ H SCOPED PRIVATE).
  - exfalso; exact (EXPRESSIONS _ _ H SCOPED PRIVATE).
  - exfalso; exact (EXPRESSIONS _ _ H SCOPED PRIVATE).
Qed.
