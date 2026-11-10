(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Original Workspace construction retains both unassigned result temporaries. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayFunctionEntry GatewayMandatoryCut
  GatewayMandatoryPairs GatewayFailurePaths GatewayWorkspaceOutcomeSource.
Import ListNotations.

Definition gateway_workspace_constructor_call := Scall (Some _t'31)
  (Evar _host_outcome_from (Tfunction [tptr (Tstruct __object noattr)] (tptr (Tstruct __object noattr)) cc_default))
  [Etempvar _data (tptr (Tstruct __object noattr))].
Definition gateway_workspace_constructor_tail :=
  Kseq (Sset _outcome (Etempvar _t'31 (tptr (Tstruct __object noattr)))) (Kseq gateway_workspace_after_outcome Kstop).

Ltac gateway_workspace_constructor_marker :=
  first [solve [left; split; reflexivity] |
    lazymatch goal with
    | |- gateway_mandatory_body ?protected ?marker ?tail ?body ?continuation =>
      let actual := eval hnf in body in lazymatch actual with
      | Ssequence ?first ?second =>
        change (gateway_mandatory_body protected marker tail actual continuation);
        first [right; right; split; [reflexivity |gateway_workspace_constructor_marker] |
               right; left; gateway_workspace_constructor_marker]
      end
    end].

Theorem gateway_workspace_constructor_profiles :
  gateway_mandatory_body _t'31 gateway_workspace_constructor_call gateway_workspace_constructor_tail
    (fn_body f_host_workspace_execute) Kstop /\
  gateway_mandatory_body _outcome gateway_workspace_constructor_call gateway_workspace_constructor_tail
    (fn_body f_host_workspace_execute) Kstop.
Proof. split; gateway_workspace_constructor_marker. Qed.

Theorem gateway_workspace_entry_result_undef ge self arguments keywords run before environment parameters allocated :
  function_entry2 ge f_host_workspace_execute [self; arguments; keywords; run] before environment parameters allocated ->
  parameters ! _t'31 = Some Vundef /\ parameters ! _outcome = Some Vundef.
Proof.
  intro ENTRY; inversion ENTRY; subst.
  match goal with BIND : bind_parameter_temps _ _ _ = Some _ |- _ =>
    change (Some (PTree.set _run run (PTree.set _keywords keywords (PTree.set _args arguments
      (PTree.set _self self (create_undef_temps (fn_temps f_host_workspace_execute)))))) = Some parameters) in BIND;
    inversion BIND; subst parameters end.
  split; repeat rewrite PTree.gso by discriminate; vm_compute; reflexivity.
Qed.

Theorem gateway_actual_workspace_constructor_temps {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    self arguments keywords run before world events value after next :
  gateway_steps backend ge
    (gateway_live (Callstate (Internal f_host_workspace_execute) [self; arguments; keywords; run] Kstop before) world)
    events (gateway_live (Returnstate value Kstop after) next) -> value <> Vnullptr ->
  exists prefix suffix environment parameters memory current,
    events = prefix ++ suffix /\ parameters ! _t'31 = Some Vundef /\ parameters ! _outcome = Some Vundef /\
    gateway_steps backend ge
      (gateway_live (Callstate (Internal f_host_workspace_execute) [self; arguments; keywords; run] Kstop before) world) prefix
      (gateway_live (State f_host_workspace_execute gateway_workspace_constructor_call gateway_workspace_constructor_tail
        environment parameters memory) current) /\
    gateway_steps backend ge
      (gateway_live (State f_host_workspace_execute gateway_workspace_constructor_call gateway_workspace_constructor_tail
        environment parameters memory) current) suffix (gateway_live (Returnstate value Kstop after) next).
Proof.
  intros RUN NONNULL.
  destruct (actual_gateway_function_entry_ambient backend ge f_host_workspace_execute [self; arguments; keywords; run] Kstop
    before world events value Kstop after next RUN)
    as (pending & rest & called & owner & environment & parameters & allocated & EVENTS & AMBIENT & PREFIX & ENTRY & REST).
  destruct (gateway_workspace_entry_result_undef _ _ _ _ _ _ _ _ _ ENTRY) as [FIRST SECOND].
  assert (INITIAL : gateway_mandatory_source f_host_workspace_execute environment _t'31 Vundef
    gateway_workspace_constructor_call gateway_workspace_constructor_tail
    (State f_host_workspace_execute (fn_body f_host_workspace_execute) Kstop environment parameters allocated)).
  { left; split; [reflexivity |split; [reflexivity |split; [exact FIRST |split; [reflexivity |left;
      exact (proj1 gateway_workspace_constructor_profiles)]]]]. }
  assert (OTHER : gateway_mandatory_source f_host_workspace_execute environment _outcome Vundef
    gateway_workspace_constructor_call gateway_workspace_constructor_tail
    (State f_host_workspace_execute (fn_body f_host_workspace_execute) Kstop environment parameters allocated)).
  { left; split; [reflexivity |split; [reflexivity |split; [exact SECOND |split; [reflexivity |left;
      exact (proj2 gateway_workspace_constructor_profiles)]]]]. }
  destruct (gateway_mandatory_pair_cut backend ge f_host_workspace_execute environment _t'31 Vundef _outcome Vundef
    gateway_workspace_constructor_call gateway_workspace_constructor_tail _ owner rest value after next
    ltac:(repeat eexists) eq_refl eq_refl INITIAL OTHER REST NONNULL)
    as (prelude & suffix & selected & memory & current & TAIL & FIRST_AT & SECOND_AT & TO_CALL & SUFFIX).
  exists (pending ++ gateway_source E0 :: prelude), suffix, environment, selected, memory, current.
  split; [rewrite EVENTS, TAIL, <- app_assoc; reflexivity |split; [exact FIRST_AT |split; [exact SECOND_AT |split]]].
  - eapply gateway_steps_append; [exact PREFIX |].
    econstructor; [apply gateway_internal; [exact I |apply step_internal_function; exact ENTRY] |exact TO_CALL].
  - exact SUFFIX.
Qed.
