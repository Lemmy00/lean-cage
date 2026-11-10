(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Bootstrap starts in the actual local environment and calls the real loader. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayBootstrapABI GatewayPrefix GatewayStackAllocation GatewayRegistry.
Import ListNotations.
Open Scope Z_scope.

Definition bootstrap_environment information resolved :=
  PTree.set _resolved (resolved, tarray tschar 4096)
    (PTree.set _information (information, gateway_loader_information_type) empty_env).
Definition bootstrap_temporaries := create_undef_temps (fn_temps f_host_bootstrap).
Definition bootstrap_first := match fn_body f_host_bootstrap with Ssequence first _ => first | _ => Sskip end.
Definition bootstrap_after_first := match fn_body f_host_bootstrap with Ssequence _ rest => rest | _ => Sskip end.
Definition bootstrap_loader_boolean := match bootstrap_first with Ssequence first _ => first | _ => Sskip end.
Definition bootstrap_loader_test := match bootstrap_first with Ssequence _ rest => rest | _ => Sskip end.
Definition bootstrap_loader_call := match bootstrap_loader_boolean with Ssequence first _ => first | _ => Sskip end.
Definition bootstrap_loader_bind := match bootstrap_loader_boolean with Ssequence _ rest => rest | _ => Sskip end.
Definition bootstrap_loader_cont information resolved :=
  Kcall (Some _t'1) f_host_bootstrap (bootstrap_environment information resolved) bootstrap_temporaries
    (Kseq bootstrap_loader_bind (Kseq bootstrap_loader_test (Kseq bootstrap_after_first Kstop))).

Lemma actual_bootstrap_structure :
  fn_body f_host_bootstrap = Ssequence bootstrap_first bootstrap_after_first /\
  bootstrap_first = Ssequence bootstrap_loader_boolean bootstrap_loader_test /\
  bootstrap_loader_boolean = Ssequence bootstrap_loader_call bootstrap_loader_bind.
Proof. repeat split; reflexivity. Qed.

Lemma actual_bootstrap_local_entry (ge : Clight.genv) before information first resolved after :
  Mem.alloc before 0 (sizeof ge gateway_loader_information_type) = (first, information) ->
  Mem.alloc first 0 4096 = (after, resolved) ->
  function_entry2 ge f_host_bootstrap [] before (bootstrap_environment information resolved) bootstrap_temporaries after.
Proof.
  intros INFO RESOLVED; constructor.
  - repeat (apply list_norepet_cons; [cbn; intuition discriminate |]); apply list_norepet_nil.
  - repeat (apply list_norepet_cons; [cbn; intuition discriminate |]); apply list_norepet_nil.
  - unfold list_disjoint, var_names; cbn; tauto.
  - econstructor; [exact INFO |]. econstructor; [exact RESOLVED |constructor].
  - reflexivity.
Qed.

Theorem actual_bootstrap_allocations (ge : Clight.genv) before :
  exists information first resolved after,
    Mem.alloc before 0 (sizeof ge gateway_loader_information_type) = (first, information) /\
    Mem.alloc first 0 4096 = (after, resolved) /\
    information <> resolved /\ ~ Mem.valid_block before information /\ ~ Mem.valid_block before resolved /\
    Mem.range_perm after information 0 (sizeof ge gateway_loader_information_type) Cur Freeable /\
    Mem.range_perm after resolved 0 4096 Cur Freeable /\
    function_entry2 ge f_host_bootstrap [] before (bootstrap_environment information resolved) bootstrap_temporaries after.
Proof.
  destruct (Mem.alloc before 0 (sizeof ge gateway_loader_information_type)) as [first information] eqn:INFO.
  destruct (Mem.alloc first 0 4096) as [after resolved] eqn:RESOLVED.
  assert (INFO_LIVE : Mem.valid_block first information) by (eapply Mem.valid_new_block; exact INFO).
  assert (RESOLVED_FRESH : ~ Mem.valid_block first resolved) by (eapply Mem.fresh_block_alloc; exact RESOLVED).
  exists information, first, resolved, after.
  split; [reflexivity |]. split; [exact RESOLVED |]. split; [congruence |].
  split; [eapply Mem.fresh_block_alloc; exact INFO |]. split.
  - intro LIVE; apply RESOLVED_FRESH; eapply Mem.valid_block_alloc; eassumption.
  - split.
    + intros position INSIDE; eapply Mem.perm_alloc_1; [exact RESOLVED |].
      eapply Mem.perm_alloc_2; eassumption.
    + split.
      * intros position INSIDE; eapply Mem.perm_alloc_2; eassumption.
      * eapply actual_bootstrap_local_entry; eassumption.
Qed.

Lemma actual_bootstrap_loader_edge (ge : Clight.genv) information resolved memory symbol entry_symbol :
  Genv.find_symbol ge _dladdr = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some (gateway_bootstrap_signature gateway_loader_address_api) ->
  Genv.find_symbol ge _PyInit__host = Some entry_symbol ->
  store_edge ge
    (State f_host_bootstrap bootstrap_loader_call
      (Kseq bootstrap_loader_bind (Kseq bootstrap_loader_test (Kseq bootstrap_after_first Kstop)))
      (bootstrap_environment information resolved) bootstrap_temporaries memory)
    (Callstate (gateway_bootstrap_signature gateway_loader_address_api)
      [Vptr entry_symbol Ptrofs.zero; Vptr information Ptrofs.zero]
      (bootstrap_loader_cont information resolved) memory).
Proof.
  intros SYMBOL FUNCTION ENTRY; eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value; eapply value_function; [reflexivity |exact SYMBOL |reflexivity].
  - eapply cons_argument_values with (v := Vptr entry_symbol Ptrofs.zero).
    + apply old_expression_value; eapply value_cast.
      * eapply value_function; [reflexivity |exact ENTRY |reflexivity].
      * reflexivity.
    + reflexivity.
    + eapply cons_argument_values with (v := Vptr information Ptrofs.zero).
      * apply local_address_expression; reflexivity.
      * reflexivity.
      * apply no_argument_values.
  - cbn; exact FUNCTION.
  - reflexivity.
Qed.

Theorem actual_bootstrap_entry_canonical (ge : Clight.genv) before environment temporaries allocated :
  function_entry2 ge f_host_bootstrap [] before environment temporaries allocated ->
  exists information first resolved,
    environment = bootstrap_environment information resolved /\ temporaries = bootstrap_temporaries /\
    Mem.alloc before 0 (sizeof ge gateway_loader_information_type) = (first, information) /\
    Mem.alloc first 0 4096 = (allocated, resolved).
Proof.
  intro ENTRY.
  destruct (actual_bootstrap_allocations ge before)
    as (information & first & resolved & after & INFO & RESOLVED & DISTINCT & FRESH_INFO & FRESH_RESOLVED &
      INFO_ACCESS & RESOLVED_ACCESS & CANONICAL).
  destruct (function_entry_unique _ _ _ _ _ _ _ _ _ _ CANONICAL ENTRY) as [ENV [TEMPS MEMORY]].
  subst environment temporaries allocated; exists information, first, resolved; repeat split; assumption || reflexivity.
Qed.
