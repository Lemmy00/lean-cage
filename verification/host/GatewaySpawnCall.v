(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The real setup test selects one fixed posix_spawn call. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayMemoryPrefixes GatewayFramedRuntime GatewayPrefix
  GatewaySpawnABI GatewaySpawnVectors GatewaySpawnVectorMemory GatewaySpawnVectorStores.
Import ListNotations.
Open Scope Z_scope.

Definition spawn_decision_sequence := match spawn_vector_after 6 with Ssequence first _ => first | _ => Sskip end.
Definition spawn_after_decision := match spawn_vector_after 6 with Ssequence _ rest => rest | _ => Sskip end.
Definition spawn_decision := match spawn_decision_sequence with Ssequence first _ => first | _ => Sskip end.
Definition spawn_bind_started := match spawn_decision_sequence with Ssequence _ rest => rest | _ => Sskip end.
Definition spawn_selected_sequence := match spawn_decision with Sifthenelse _ _ selected => selected | _ => Sskip end.
Definition spawn_selected_call := match spawn_selected_sequence with Ssequence call _ => call | _ => Sskip end.
Definition spawn_selected_cast := match spawn_selected_sequence with Ssequence _ cast => cast | _ => Sskip end.

Definition gateway_spawn_call_values blocks symbols actions attributes :=
  [Vptr (spawn_child_block blocks) Ptrofs.zero; Vptr (spawn_engine_symbol symbols) Ptrofs.zero;
   Vptr actions Ptrofs.zero; Vptr attributes Ptrofs.zero;
   Vptr (spawn_arguments_block blocks) Ptrofs.zero; Vptr (spawn_environment_block blocks) Ptrofs.zero].

Definition gateway_spawn_call_cont environment temporaries continuation :=
  Kcall (Some _t'27) f_host_exchange environment temporaries
    (Kseq spawn_selected_cast (Kseq spawn_bind_started (Kseq spawn_after_decision continuation))).

Lemma actual_spawn_call_edge (ge : Clight.genv) environment temporaries blocks symbols actions attributes before continuation symbol :
  gateway_spawn_vector_locations ge environment blocks symbols ->
  environment ! _actions = Some (actions, gateway_actions_type) ->
  environment ! _attributes = Some (attributes, gateway_attributes_type) ->
  environment ! _posix_spawn = None ->
  Genv.find_symbol ge _posix_spawn = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some (gateway_spawn_signature gateway_posix_spawn_api) ->
  store_edge ge (State f_host_exchange spawn_selected_call
      (Kseq spawn_selected_cast (Kseq spawn_bind_started (Kseq spawn_after_decision continuation)))
      environment temporaries before)
    (Callstate (gateway_spawn_signature gateway_posix_spawn_api)
      (gateway_spawn_call_values blocks symbols actions attributes)
      (gateway_spawn_call_cont environment temporaries continuation) before).
Proof.
  intros [CHILD ARGUMENTS ENVIRONMENT ENGINE_LOCAL PATH_LOCAL LOCALE_LOCAL ENGINE PATH LOCALE]
    ACTIONS ATTRIBUTES NOT_LOCAL SYMBOL FUNCTION.
  eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value; eapply value_function; [exact NOT_LOCAL |exact SYMBOL |reflexivity].
  - eapply cons_argument_values with (v := Vptr (spawn_child_block blocks) Ptrofs.zero).
    + apply local_address_expression; exact CHILD.
    + reflexivity.
    + eapply cons_argument_values with (v := Vptr (spawn_engine_symbol symbols) Ptrofs.zero).
      * eapply spawn_global_array_reference; [exact ENGINE_LOCAL |exact ENGINE |reflexivity].
      * reflexivity.
      * eapply cons_argument_values with (v := Vptr actions Ptrofs.zero).
        -- apply local_address_expression; exact ACTIONS.
        -- reflexivity.
        -- eapply cons_argument_values with (v := Vptr attributes Ptrofs.zero).
           ++ apply local_address_expression; exact ATTRIBUTES.
           ++ reflexivity.
           ++ eapply cons_argument_values with (v := Vptr (spawn_arguments_block blocks) Ptrofs.zero).
              ** apply spawn_array_reference; exact ARGUMENTS.
              ** reflexivity.
              ** eapply cons_argument_values with (v := Vptr (spawn_environment_block blocks) Ptrofs.zero).
                 --- apply spawn_array_reference; exact ENVIRONMENT.
                 --- reflexivity.
                 --- apply no_argument_values.
  - cbn; exact FUNCTION.
  - reflexivity.
Qed.

Theorem actual_spawn_selected_script {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    property environment temporaries blocks symbols actions attributes continuation template symbol :
  gateway_ambient_closed backend property -> gateway_spawn_vector_locations ge environment blocks symbols ->
  environment ! _actions = Some (actions, gateway_actions_type) ->
  environment ! _attributes = Some (attributes, gateway_attributes_type) -> environment ! _posix_spawn = None ->
  Genv.find_symbol ge _posix_spawn = Some symbol ->
  Genv.find_funct_ptr ge symbol = Some (gateway_spawn_signature gateway_posix_spawn_api) ->
  temporaries ! _setup = Some (Vint Int.zero) ->
  gateway_memory_prefix backend ge
    (Callstate (gateway_spawn_signature gateway_posix_spawn_api) (gateway_spawn_call_values blocks symbols actions attributes)
      (gateway_spawn_call_cont environment temporaries continuation) template)
    property property (State f_host_exchange (spawn_vector_after 6) continuation environment temporaries template).
Proof.
  intros CLOSED LOCATIONS ACTIONS ATTRIBUTES NOT_LOCAL SYMBOL FUNCTION SETUP.
  eapply gateway_memory_same with (following := State f_host_exchange spawn_decision_sequence
    (Kseq spawn_after_decision continuation) environment temporaries template);
    [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_seq |].
  eapply gateway_memory_same with (following := State f_host_exchange spawn_decision
    (Kseq spawn_bind_started (Kseq spawn_after_decision continuation)) environment temporaries template);
    [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_seq |].
  eapply gateway_memory_same with (following := State f_host_exchange spawn_selected_sequence
    (Kseq spawn_bind_started (Kseq spawn_after_decision continuation)) environment temporaries template).
  - exact CLOSED.
  - cbn; tauto.
  - intros before world READY; apply certified_if_edge with (v := Vint Int.zero) (b := false).
    + apply old_expression_value, value_temp; exact SETUP.
    + reflexivity.
  - eapply gateway_memory_same with (following := State f_host_exchange spawn_selected_call
      (Kseq spawn_selected_cast (Kseq spawn_bind_started (Kseq spawn_after_decision continuation)))
      environment temporaries template);
      [exact CLOSED |cbn; tauto |intros; apply unchanged_store_edge, edge_seq |].
    eapply gateway_memory_same with (following := Callstate (gateway_spawn_signature gateway_posix_spawn_api)
      (gateway_spawn_call_values blocks symbols actions attributes) (gateway_spawn_call_cont environment temporaries continuation) template).
    + exact CLOSED.
    + cbn; tauto.
    + intros before world READY; eapply actual_spawn_call_edge; eassumption.
    + apply gateway_memory_identity.
Qed.
