(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Actual Clight expression evaluation preserves private address exclusion. *)
From Stdlib Require Import ZArith List Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Cop Clight.
From HostGateway Require Import GatewayPointerOrigins GatewayPointerMemory.
Import ListNotations.

Definition gateway_global_address_allowed (private_name : ident -> bool) identifier := negb (private_name identifier).

Fixpoint gateway_expression_addresses (private_name : ident -> bool) (expression : expr) : bool :=
  match expression with
  | Evar identifier ty =>
      match access_mode ty with By_value _ => true | _ => gateway_global_address_allowed private_name identifier end
  | Etempvar _ _ | Econst_int _ _ | Econst_long _ _ | Econst_float _ _ | Econst_single _ _ |
      Esizeof _ _ | Ealignof _ _ => true
  | Ederef nested _ | Eunop _ nested _ | Ecast nested _ | Efield nested _ _ =>
      gateway_expression_addresses private_name nested
  | Eaddrof nested _ => gateway_lvalue_addresses private_name nested
  | Ebinop _ first second _ =>
      gateway_expression_addresses private_name first && gateway_expression_addresses private_name second
  end
with gateway_lvalue_addresses (private_name : ident -> bool) (expression : expr) : bool :=
  match expression with
  | Evar identifier _ => gateway_global_address_allowed private_name identifier
  | Ederef nested _ | Efield nested _ _ => gateway_expression_addresses private_name nested
  | _ => false
  end.

Lemma gateway_reference_expression_addresses ge environment temporaries memory private_name expression object offset field :
  eval_lvalue ge environment temporaries memory expression object offset field ->
  (access_mode (typeof expression) = By_reference \/ access_mode (typeof expression) = By_copy) ->
  gateway_expression_addresses private_name expression = true ->
  gateway_lvalue_addresses private_name expression = true.
Proof.
  intros LOCATION MODE CHECK; inversion LOCATION; subst; cbn [gateway_expression_addresses gateway_lvalue_addresses typeof] in *;
    try exact CHECK; destruct MODE as [MODE |MODE]; rewrite MODE in CHECK; exact CHECK.
Qed.

Theorem gateway_expression_lvalue_avoids (ge : Clight.genv) (environment : env) (temporaries : temp_env)
    memory private private_name :
  (forall identifier object ty, environment ! identifier = Some (object, ty) -> ~ private object) ->
  (forall identifier object, Genv.find_symbol ge identifier = Some object ->
    gateway_global_address_allowed private_name identifier = true -> ~ private object) ->
  (forall identifier value, temporaries ! identifier = Some value -> gateway_pointer_avoids private value) ->
  gateway_memory_avoids private memory ->
  (forall expression value, eval_expr ge environment temporaries memory expression value ->
    gateway_expression_addresses private_name expression = true -> gateway_pointer_avoids private value) /\
  (forall expression object offset field, eval_lvalue ge environment temporaries memory expression object offset field ->
    gateway_lvalue_addresses private_name expression = true -> ~ private object).
Proof.
  intros LOCALS GLOBALS TEMPORARIES MEMORY.
  apply eval_expr_lvalue_ind.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros; exact I.
  - intros identifier ty value LOOKUP CHECK; eapply TEMPORARIES; exact LOOKUP.
  - intros expression ty object offset LOCATION IH CHECK; apply IH; exact CHECK.
  - intros operation expression ty first value EVAL IH OPERATION CHECK.
    destruct value; try exact I; exfalso; eapply gateway_unary_pointer_impossible; exact OPERATION.
  - intros operation first second ty left right value LEFT LEFT_IH RIGHT RIGHT_IH OPERATION CHECK.
    cbn [gateway_expression_addresses] in CHECK; apply andb_true_iff in CHECK as [FIRST SECOND].
    eapply gateway_binary_avoids; [apply LEFT_IH; exact FIRST |apply RIGHT_IH; exact SECOND |exact OPERATION].
  - intros expression ty first value EVAL IH CAST CHECK.
    eapply gateway_cast_avoids; [apply IH; exact CHECK |exact CAST].
  - intros; unfold Vptrofs; destruct Archi.ptr64; exact I.
  - intros; unfold Vptrofs; destruct Archi.ptr64; exact I.
  - intros a object offset field value LOCATION IH DEREF CHECK.
    inversion DEREF; subst.
    + eapply gateway_loadv_avoids; [exact MEMORY |eassumption].
    + apply IH; eapply gateway_reference_expression_addresses; [exact LOCATION |left; eassumption |exact CHECK].
    + apply IH; eapply gateway_reference_expression_addresses; [exact LOCATION |right; eassumption |exact CHECK].
    + match goal with LOAD : load_bitfield _ _ _ _ _ _ _ _ |- _ => inversion LOAD; subst; exact I end.
  - intros identifier object ty LOOKUP CHECK; eapply LOCALS; exact LOOKUP.
  - intros identifier object ty ABSENT SYMBOL CHECK; eapply GLOBALS; [exact SYMBOL |exact CHECK].
  - intros expression ty object offset EVAL IH CHECK; apply IH; exact CHECK.
  - intros expression identifier ty object offset composite_name composite attributes delta field
      EVAL IH TYPE COMPOSITE FIELD CHECK; apply IH; exact CHECK.
  - intros expression identifier ty object offset composite_name composite attributes delta field
      EVAL IH TYPE COMPOSITE FIELD CHECK; apply IH; exact CHECK.
Qed.
