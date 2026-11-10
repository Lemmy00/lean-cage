(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: The maintained program has explicit pointer scopes at every continuation. *)
From Stdlib Require Import ZArith List Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayRegistry GatewayGlobalAddresses GatewayPointerEntry
  GatewayPointerOrigins GatewayPointerMemory.
Require Import Machine.
Import ListNotations.

Fixpoint gateway_pointer_statement (body : statement) : bool :=
  gateway_statement_addresses body &&
    match body with
    | Ssequence first second | Sifthenelse _ first second | Sloop first second =>
        gateway_pointer_statement first && gateway_pointer_statement second
    | Sswitch _ branches => gateway_pointer_branches branches
    | Slabel _ nested => gateway_pointer_statement nested
    | _ => true
    end
with gateway_pointer_branches (branches : labeled_statements) : bool :=
  match branches with
  | LSnil => true
  | LScons _ body rest => gateway_pointer_statement body && gateway_pointer_branches rest
  end.

Definition gateway_pointer_definition definition :=
  match definition with Internal function => gateway_pointer_statement (fn_body function) | External _ _ _ _ => true end.

Definition gateway_pointer_definition_entry (entry : ident * globdef (Ctypes.fundef function) type) :=
  match snd entry with Gfun definition => gateway_pointer_definition definition | Gvar _ => true end.

Theorem actual_gateway_pointer_control : forallb gateway_pointer_definition_entry global_definitions = true.
Proof. vm_compute; reflexivity. Qed.

Local Opaque prog.

Theorem gateway_actual_pointer_function value definition :
  Genv.find_funct (Clight.globalenv prog) value = Some definition -> gateway_pointer_definition definition = true.
Proof.
  intro FOUND.
  change (Genv.find_funct (Genv.globalenv prog) value = Some definition) in FOUND.
  destruct (@Genv.find_funct_inversion (Ctypes.fundef function) type prog value definition FOUND)
    as [identifier REGISTERED].
  change (In (identifier, Gfun definition) (prog_defs prog)) in REGISTERED.
  rewrite gateway_actual_program_definitions in REGISTERED.
  exact (proj1 (forallb_forall _ _) actual_gateway_pointer_control (identifier, Gfun definition) REGISTERED).
Qed.

Theorem gateway_pointer_switch_sequence branches :
  gateway_pointer_branches branches = true ->
  gateway_pointer_statement (seq_of_labeled_statement branches) = true.
Proof.
  induction branches; cbn [gateway_pointer_branches seq_of_labeled_statement gateway_pointer_statement gateway_statement_addresses];
    intro SAFE; [reflexivity |].
  apply andb_true_iff in SAFE as [FIRST REST]; rewrite FIRST, (IHbranches REST); reflexivity.
Qed.

Theorem gateway_pointer_switch_default branches :
  gateway_pointer_branches branches = true -> gateway_pointer_branches (select_switch_default branches) = true.
Proof.
  induction branches as [|label body rest IH]; [intro; reflexivity |].
  intro SAFE; destruct label; cbn [select_switch_default]; [apply IH |exact SAFE].
  exact (proj2 (proj1 (andb_true_iff _ _) SAFE)).
Qed.

Theorem gateway_pointer_switch_case selector branches selected :
  gateway_pointer_branches branches = true -> select_switch_case selector branches = Some selected ->
  gateway_pointer_branches selected = true.
Proof.
  revert selected; induction branches as [|label body rest IH]; intros selected SAFE FOUND; [discriminate |].
  cbn [select_switch_case] in FOUND; destruct label.
  - destruct (zeq z selector); [inversion FOUND; subst; exact SAFE |].
    eapply IH; [exact (proj2 (proj1 (andb_true_iff _ _) SAFE)) |exact FOUND].
  - eapply IH; [exact (proj2 (proj1 (andb_true_iff _ _) SAFE)) |exact FOUND].
Qed.

Theorem gateway_pointer_switch selector branches :
  gateway_pointer_branches branches = true -> gateway_pointer_statement
    (seq_of_labeled_statement (select_switch selector branches)) = true.
Proof.
  intro SAFE; apply gateway_pointer_switch_sequence; unfold select_switch.
  destruct (select_switch_case selector branches) as [selected |] eqn:SELECT.
  - eapply gateway_pointer_switch_case; eassumption.
  - apply gateway_pointer_switch_default; exact SAFE.
Qed.

Fixpoint gateway_pointer_cont private (continuation : cont) : Prop :=
  match continuation with
  | Kstop => True
  | Kseq body rest => gateway_pointer_statement body = true /\ gateway_pointer_cont private rest
  | Kloop1 first second rest | Kloop2 first second rest =>
      gateway_pointer_statement first = true /\ gateway_pointer_statement second = true /\ gateway_pointer_cont private rest
  | Kswitch rest => gateway_pointer_cont private rest
  | Kcall _ function environment temporaries rest => gateway_pointer_statement (fn_body function) = true /\
      gateway_locals_avoid private environment /\ gateway_temporaries_avoid private temporaries /\ gateway_pointer_cont private rest
  end.

Theorem gateway_pointer_call_cont private continuation :
  gateway_pointer_cont private continuation -> gateway_pointer_cont private (call_cont continuation).
Proof. induction continuation; cbn; tauto. Qed.

Definition gateway_pointer_source (ge : Clight.genv) source : Prop :=
  let private := gateway_private_cell ge in
  gateway_memory_avoids private (memory_of source) /\
  (forall object, private object -> Mem.valid_block (memory_of source) object) /\
  match source with
  | State function body continuation environment temporaries _ =>
      gateway_pointer_statement (fn_body function) = true /\
      gateway_pointer_statement body = true /\ gateway_pointer_cont private continuation /\
      gateway_locals_avoid private environment /\ gateway_temporaries_avoid private temporaries
  | Callstate definition arguments continuation _ => gateway_pointer_definition definition = true /\
      gateway_pointer_cont private continuation /\ Forall (gateway_pointer_avoids private) arguments
  | Returnstate value continuation _ => gateway_pointer_cont private continuation /\ gateway_pointer_avoids private value
  end.
