(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Actual control retains the checked fcntl call profile. *)
From Stdlib Require Import ZArith List Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Cop Clight.
From HostGateway Require Import GatewaySource GatewayRegistry GatewaySpawnABI GatewayMachine GatewayFcntlProfile.
Import ListNotations.
Local Opaque prog.

Theorem gateway_actual_fcntl_function value definition :
  Genv.find_funct (Clight.globalenv prog) value = Some definition -> gateway_fcntl_definition definition = true.
Proof.
  intro FOUND.
  change (Genv.find_funct (Genv.globalenv prog) value = Some definition) in FOUND.
  destruct (@Genv.find_funct_inversion (Ctypes.fundef function) type prog value definition FOUND)
    as [identifier REGISTERED].
  change (In (identifier, Gfun definition) (prog_defs prog)) in REGISTERED.
  rewrite gateway_actual_program_definitions in REGISTERED.
  exact (proj1 (forallb_forall _ _) actual_gateway_fcntl_profile (identifier, Gfun definition) REGISTERED).
Qed.

Theorem gateway_fcntl_switch_sequence branches :
  gateway_fcntl_branches branches = true -> gateway_fcntl_statement (seq_of_labeled_statement branches) = true.
Proof.
  induction branches; cbn [gateway_fcntl_branches seq_of_labeled_statement gateway_fcntl_statement gateway_fcntl_local];
    intro GOOD; [reflexivity |].
  apply andb_true_iff in GOOD as [FIRST REST]; rewrite FIRST, (IHbranches REST); reflexivity.
Qed.

Theorem gateway_fcntl_switch_default branches :
  gateway_fcntl_branches branches = true -> gateway_fcntl_branches (select_switch_default branches) = true.
Proof.
  induction branches as [|label body rest IH]; [intro; reflexivity |].
  intro GOOD; destruct label; cbn [select_switch_default]; [apply IH |exact GOOD].
  exact (proj2 (proj1 (andb_true_iff _ _) GOOD)).
Qed.

Theorem gateway_fcntl_switch_case selector branches selected :
  gateway_fcntl_branches branches = true -> select_switch_case selector branches = Some selected ->
  gateway_fcntl_branches selected = true.
Proof.
  revert selected; induction branches as [|label body rest IH]; intros selected GOOD FOUND; [discriminate |].
  cbn [select_switch_case] in FOUND; destruct label.
  - destruct (zeq z selector); [inversion FOUND; subst; exact GOOD |].
    eapply IH; [exact (proj2 (proj1 (andb_true_iff _ _) GOOD)) |exact FOUND].
  - eapply IH; [exact (proj2 (proj1 (andb_true_iff _ _) GOOD)) |exact FOUND].
Qed.

Theorem gateway_fcntl_switch selector branches :
  gateway_fcntl_branches branches = true -> gateway_fcntl_statement
    (seq_of_labeled_statement (select_switch selector branches)) = true.
Proof.
  intro GOOD; apply gateway_fcntl_switch_sequence; unfold select_switch.
  destruct (select_switch_case selector branches) as [selected |] eqn:SELECT.
  - eapply gateway_fcntl_switch_case; eassumption.
  - apply gateway_fcntl_switch_default; exact GOOD.
Qed.

Fixpoint gateway_fcntl_cont (continuation : cont) : Prop :=
  match continuation with
  | Kstop => True
  | Kseq body rest => gateway_fcntl_statement body = true /\ gateway_fcntl_cont rest
  | Kloop1 first second rest | Kloop2 first second rest =>
      gateway_fcntl_statement first = true /\ gateway_fcntl_statement second = true /\ gateway_fcntl_cont rest
  | Kswitch rest => gateway_fcntl_cont rest
  | Kcall _ function _ _ rest => gateway_fcntl_statement (fn_body function) = true /\ gateway_fcntl_cont rest
  end.

Theorem gateway_fcntl_call_cont continuation :
  gateway_fcntl_cont continuation -> gateway_fcntl_cont (call_cont continuation).
Proof. induction continuation; cbn; tauto. Qed.

Definition gateway_fcntl_values (arguments : list Values.val) : Prop :=
  exists first command last, arguments = [first; Vint command; last] /\
    (command = Int.repr 3 \/ command = Int.repr 4 \/ command = Int.repr 1030).

Definition gateway_fcntl_source source : Prop :=
  match source with
  | State function body continuation _ _ _ =>
    gateway_fcntl_statement (fn_body function) = true /\ gateway_fcntl_statement body = true /\ gateway_fcntl_cont continuation
  | Callstate definition arguments continuation _ => gateway_fcntl_definition definition = true /\
    gateway_fcntl_cont continuation /\ (definition = gateway_spawn_signature gateway_fcntl_api -> gateway_fcntl_values arguments)
  | Returnstate _ continuation _ => gateway_fcntl_cont continuation
  end.
