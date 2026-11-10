(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Nonpositive actual validation results take the maintained NULL path. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayOutcomeConstruction GatewayOutcomeEntry
  GatewaySourceCuts GatewaySourcePaths GatewaySourceBoundCalls GatewaySourceSegmentAutomation GatewayFailurePaths
  GatewayFramedRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_outcome_validation_loop_block :=
  match gateway_outcome_first_validation_tail with Ssequence first _ => first | _ => Sskip end.
Definition gateway_outcome_validation_loop :=
  match gateway_outcome_validation_loop_block with Ssequence _ loop => loop | _ => Sskip end.
Definition gateway_outcome_validation_loop_body :=
  match gateway_outcome_validation_loop with Sloop body _ => body | _ => Sskip end.
Definition gateway_outcome_validation_loop_update :=
  match gateway_outcome_validation_loop with Sloop _ update => update | _ => Sskip end.
Definition gateway_outcome_after_field_validation := gateway_outcome_right_suffix 2 (fn_body f_host_outcome_from).
Definition gateway_outcome_after_json_validation := gateway_outcome_right_suffix 3 (fn_body f_host_outcome_from).
Definition gateway_outcome_invalid_guard :=
  match gateway_outcome_after_json_validation with Ssequence guard _ => guard | _ => Sskip end.
Definition gateway_outcome_field_type_cont environment parameters :=
  Kcall (Some _t'10) f_host_outcome_from environment parameters
    (Kseq (Sset _valid (Etempvar _t'10 tint))
      (Kloop1 gateway_outcome_validation_loop_body gateway_outcome_validation_loop_update
        (Kseq gateway_outcome_after_field_validation Kstop))).
Definition gateway_outcome_json_type_cont environment parameters :=
  Kcall (Some _t'12) f_host_outcome_from environment parameters
    (Kseq (Sset _valid (Etempvar _t'12 tint)) (Kseq gateway_outcome_after_json_validation Kstop)).

Lemma gateway_nonpositive_gt (ge : Clight.genv) memory word :
  Int.signed word <= 0 ->
  sem_binary_operation ge Ogt (Vint word) tint (Vint Int.zero) tint memory = Some (Vint Int.zero).
Proof.
  intro NONPOS; change (Some (Val.of_bool (Int.lt Int.zero word)) = Some (Vint Int.zero)).
  assert (LESS : Int.lt Int.zero word = false).
  { unfold Int.lt; change ((if zlt 0 (Int.signed word) then true else false) = false); destruct zlt; [lia |reflexivity]. }
  rewrite LESS; reflexivity.
Qed.

Lemma gateway_nonpositive_le (ge : Clight.genv) memory word :
  Int.signed word <= 0 ->
  sem_binary_operation ge Ole (Vint word) tint (Vint Int.zero) tint memory = Some (Vint Int.one).
Proof.
  intro NONPOS; change (Some (Val.of_bool (negb (Int.lt Int.zero word))) = Some (Vint Int.one)).
  assert (LESS : Int.lt Int.zero word = false).
  { unfold Int.lt; change ((if zlt 0 (Int.signed word) then true else false) = false); destruct zlt; [lia |reflexivity]. }
  rewrite LESS; reflexivity.
Qed.

(* Each step constructs the real Clight edge. In particular, a rejected loop
   iteration takes Sbreak rather than deleting its hostile helper transitions. *)
Ltac gateway_validation_failure closed loads reduce pointer :=
  first [solve [apply gateway_failure_when_selected, gateway_failure_selected;
    [exact pointer |vm_compute; tauto |reflexivity]] |
  lazymatch goal with
  | |- gateway_failure_when _ _ _ (Returnstate ?value ?saved ?memory) =>
    let call := eval hnf in saved in lazymatch call with
    | Kcall ?destination ?function ?environment ?parameters ?continuation =>
      eapply gateway_failure_when_same with
        (target := State function Sskip continuation environment (set_opttemp destination value parameters) memory);
        [exact closed |cbn; tauto |intros; apply unchanged_store_edge, edge_returnstate |
         gateway_validation_failure closed loads reduce pointer]
    end
  | |- gateway_failure_when _ _ _ (State ?function ?body ?continuation ?environment ?parameters ?memory) =>
    let statement := eval hnf in body in lazymatch statement with
    | (if ?flag then ?yes else ?no) =>
      let selected := eval vm_compute in flag in lazymatch selected with
      | true => change body with yes; gateway_validation_failure closed loads reduce pointer
      | false => change body with no; gateway_validation_failure closed loads reduce pointer
      end
    | Ssequence ?first ?rest =>
      eapply gateway_failure_when_same with (target := State function first (Kseq rest continuation) environment parameters memory);
        [exact closed |cbn; tauto |intros; apply unchanged_store_edge, edge_seq |
         gateway_validation_failure closed loads reduce pointer]
    | Sset ?identifier ?expression =>
      let result := open_constr:(_ : val) in
      eapply gateway_failure_when_same with (target := State function Sskip continuation environment (PTree.set identifier result parameters) memory);
        [exact closed |cbn; tauto |intros; apply certified_set_edge; gateway_segment_expression loads reduce |
         gateway_validation_failure closed loads reduce pointer]
    | Sifthenelse ?expression ?yes ?no =>
      let flag := open_constr:(_ : bool) in
      eapply gateway_failure_when_same with (target := State function (if flag then yes else no) continuation environment parameters memory);
        [exact closed |cbn; tauto |intros; eapply certified_if_edge;
          [gateway_segment_expression loads reduce |reduce ()] |gateway_validation_failure closed loads reduce pointer]
    | Sloop ?first ?second =>
      eapply gateway_failure_when_same with
        (target := State function first (Kloop1 first second continuation) environment parameters memory);
        [exact closed |cbn; tauto |intros; apply unchanged_store_edge, edge_loop |
         gateway_validation_failure closed loads reduce pointer]
    | Sskip => let rest := eval hnf in continuation in lazymatch rest with
      | Kseq ?following ?rest =>
        eapply gateway_failure_when_same with (target := State function following rest environment parameters memory);
          [exact closed |cbn; tauto |intros; apply unchanged_store_edge, edge_skip_seq |
           gateway_validation_failure closed loads reduce pointer]
      | Kloop1 ?first ?second ?rest =>
        eapply gateway_failure_when_same with (target := State function second (Kloop2 first second rest) environment parameters memory);
          [exact closed |cbn; tauto |intros; apply unchanged_store_edge, edge_skip_loop1 |
           gateway_validation_failure closed loads reduce pointer]
      | Kloop2 ?first ?second ?rest =>
        eapply gateway_failure_when_same with (target := State function (Sloop first second) rest environment parameters memory);
          [exact closed |cbn; tauto |intros; apply unchanged_store_edge, edge_skip_loop2 |
           gateway_validation_failure closed loads reduce pointer]
      end
    | Sbreak => let rest := eval hnf in continuation in lazymatch rest with
      | Kseq ?following ?rest =>
        eapply gateway_failure_when_same with (target := State function Sbreak rest environment parameters memory);
          [exact closed |cbn; tauto |intros; apply unchanged_store_edge, edge_break_seq |
           gateway_validation_failure closed loads reduce pointer]
      | Kloop1 ?first ?second ?rest =>
        eapply gateway_failure_when_same with (target := State function Sskip rest environment parameters memory);
          [exact closed |cbn; tauto |intros; apply unchanged_store_edge, edge_break_loop1 |
           gateway_validation_failure closed loads reduce pointer]
      end
    end
  end].

Theorem gateway_outcome_first_nonpositive_null {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    environment parameters memory word : Int.signed word <= 0 ->
  gateway_failure_when backend ge (fun _ _ => True)
    (Returnstate (Vint word) (gateway_outcome_first_type_cont environment parameters) memory).
Proof.
  intro NONPOS.
  assert (CLOSED : gateway_ambient_closed backend (fun _ _ => True)) by (unfold gateway_ambient_closed; intros; exact I).
  assert (POINTER : gateway_pointer_return f_host_outcome_from) by (repeat eexists).
  gateway_validation_failure CLOSED ltac:(fun _ => fail)
    ltac:(fun _ => first [apply gateway_nonpositive_gt; exact NONPOS |apply gateway_nonpositive_le; exact NONPOS |reflexivity]) POINTER.
Qed.

Theorem gateway_outcome_json_nonpositive_null {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    environment parameters memory word : Int.signed word <= 0 ->
  gateway_failure_when backend ge (fun _ _ => True)
    (Returnstate (Vint word) (gateway_outcome_json_type_cont environment parameters) memory).
Proof.
  intro NONPOS.
  assert (CLOSED : gateway_ambient_closed backend (fun _ _ => True)) by (unfold gateway_ambient_closed; intros; exact I).
  assert (POINTER : gateway_pointer_return f_host_outcome_from) by (repeat eexists).
  gateway_validation_failure CLOSED ltac:(fun _ => fail)
    ltac:(fun _ => first [apply gateway_nonpositive_le; exact NONPOS |reflexivity]) POINTER.
Qed.

Theorem gateway_outcome_field_nonpositive_null {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    environment parameters memory word index : parameters ! _index = Some (Vint index) -> Int.signed word <= 0 ->
  gateway_failure_when backend ge (fun _ _ => True)
    (Returnstate (Vint word) (gateway_outcome_field_type_cont environment parameters) memory).
Proof.
  intros INDEX NONPOS.
  assert (CLOSED : gateway_ambient_closed backend (fun _ _ => True)) by (unfold gateway_ambient_closed; intros; exact I).
  assert (POINTER : gateway_pointer_return f_host_outcome_from) by (repeat eexists).
  gateway_validation_failure CLOSED ltac:(fun _ => fail)
    ltac:(fun _ => first [apply gateway_nonpositive_gt; exact NONPOS |apply gateway_nonpositive_le; exact NONPOS |reflexivity]) POINTER.
Qed.
