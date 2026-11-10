(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Inspect actual class writers, private callers and
   address exposure. *)
From Stdlib Require Import List Bool.
From compcert Require Import Coqlib AST Ctypes Clight.
From HostGateway Require Import GatewaySource.
Import ListNotations.

Definition initialization_class_cell identifier :=
  existsb (Pos.eqb identifier) [_host_path_class; _host_cancellation_class; _host_outcome_class].

Fixpoint initialization_statement_any (test : statement -> bool) (body : statement) : bool :=
  test body || match body with
  | Ssequence first rest | Sifthenelse _ first rest | Sloop first rest =>
      initialization_statement_any test first || initialization_statement_any test rest
  | Slabel _ nested => initialization_statement_any test nested
  | Sswitch _ branches => initialization_branches_any test branches
  | _ => false
  end
with initialization_branches_any (test : statement -> bool) (branches : labeled_statements) : bool :=
  match branches with
  | LSnil => false
  | LScons _ body rest => initialization_statement_any test body || initialization_branches_any test rest
  end.

Definition initialization_class_store body := match body with
  | Sassign (Evar identifier _) _ => initialization_class_cell identifier | _ => false end.
Definition initialization_private_call body := match body with
  | Scall _ (Evar identifier (Tfunction _ _ _)) _ => Pos.eqb identifier _host_initialize | _ => false end.
Definition initialization_unknown_call body := match body with
  | Scall _ (Evar _ (Tfunction _ _ _)) _ => false | Scall _ _ _ => true | _ => false end.

Fixpoint initialization_class_address (expression : expr) : bool :=
  match expression with
  | Eaddrof (Evar identifier _) _ => initialization_class_cell identifier
  | Ederef nested _ | Eaddrof nested _ | Eunop _ nested _ | Ecast nested _ | Efield nested _ _ =>
      initialization_class_address nested
  | Ebinop _ lhs rhs _ => initialization_class_address lhs || initialization_class_address rhs
  | _ => false
  end.

Definition initialization_expression_exposure body := match body with
  | Sassign lhs rhs => initialization_class_address lhs || initialization_class_address rhs
  | Sset _ value | Sifthenelse value _ _ | Sswitch value _ => initialization_class_address value
  | Scall _ function arguments => initialization_class_address function || existsb initialization_class_address arguments
  | Sbuiltin _ _ _ arguments => existsb initialization_class_address arguments
  | Sreturn (Some value) => initialization_class_address value
  | _ => false end.

Definition initialization_writer_entry (entry : ident * globdef (Ctypes.fundef function) type) :=
  match snd entry with
  | Gfun (Internal body) =>
      negb (initialization_statement_any initialization_class_store (fn_body body)) || Pos.eqb (fst entry) _host_initialize
  | _ => true end.
Definition initialization_caller_entry (entry : ident * globdef (Ctypes.fundef function) type) :=
  match snd entry with
  | Gfun (Internal body) =>
      negb (initialization_statement_any initialization_private_call (fn_body body)) || Pos.eqb (fst entry) _PyInit__host
  | _ => true end.
Definition initialization_call_classification_entry (entry : ident * globdef (Ctypes.fundef function) type) :=
  match snd entry with
  | Gfun (Internal body) => negb (initialization_statement_any initialization_unknown_call (fn_body body)) || Pos.eqb (fst entry) _host_outcome_traverse
  | _ => true end.
Definition initialization_unexposed_entry (entry : ident * globdef (Ctypes.fundef function) type) :=
  match snd entry with
  | Gfun (Internal body) => negb (initialization_statement_any initialization_expression_exposure (fn_body body))
  | Gvar variable => negb (existsb (fun datum => match datum with
      | Init_addrof identifier _ => initialization_class_cell identifier | _ => false end) (gvar_init variable))
  | _ => true end.

Theorem actual_initialization_class_writer_inventory : forallb initialization_writer_entry global_definitions = true.
Proof. vm_compute; reflexivity. Qed.
Theorem actual_initialization_private_caller_inventory : forallb initialization_caller_entry global_definitions = true.
Proof. vm_compute; reflexivity. Qed.
Theorem actual_initialization_indirect_call_inventory : forallb initialization_call_classification_entry global_definitions = true.
Proof. vm_compute; reflexivity. Qed.
Theorem actual_initialization_class_address_inventory : forallb initialization_unexposed_entry global_definitions = true.
Proof. vm_compute; reflexivity. Qed.

Theorem gateway_actual_class_global_writer identifier function :
  In (identifier, Gfun (Internal function)) global_definitions ->
  initialization_statement_any initialization_class_store (fn_body function) = true -> identifier = _host_initialize.
Proof.
  intros MEMBER WRITES.
  pose proof (proj1 (forallb_forall _ _) actual_initialization_class_writer_inventory
    (identifier, Gfun (Internal function)) MEMBER) as SELECTED.
  unfold initialization_writer_entry in SELECTED; cbn in SELECTED; rewrite WRITES in SELECTED; cbn in SELECTED.
  apply Pos.eqb_eq; exact SELECTED.
Qed.

Theorem gateway_actual_private_initializer_caller identifier function :
  In (identifier, Gfun (Internal function)) global_definitions ->
  initialization_statement_any initialization_private_call (fn_body function) = true -> identifier = _PyInit__host.
Proof.
  intros MEMBER CALLS.
  pose proof (proj1 (forallb_forall _ _) actual_initialization_private_caller_inventory
    (identifier, Gfun (Internal function)) MEMBER) as SELECTED.
  unfold initialization_caller_entry in SELECTED; cbn in SELECTED; rewrite CALLS in SELECTED; cbn in SELECTED.
  apply Pos.eqb_eq; exact SELECTED.
Qed.
