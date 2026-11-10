(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: A deterministic comparison of actual source-word prefixes. *)
From Stdlib Require Import List Arith Lia.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewayImport GatewayWordData GatewayCanonicalBytes GatewayCanonicalSubject.
Import ListNotations.
Local Close Scope lean_scope.
Local Open Scope nat_scope.

Local Abbreviation Subject := LeanCage_Host_GatewayResponseCode_Subject.
Local Abbreviation SValue := LeanCage_Host_GatewayResponseCode_Subject_value.
Local Abbreviation SValues := LeanCage_Host_GatewayResponseCode_Subject_values.
Local Abbreviation SFields := LeanCage_Host_GatewayResponseCode_Subject_fields.
Local Abbreviation VNull := LeanCage_Host_GatewayResponseCode_Value_null.
Local Abbreviation VBool := LeanCage_Host_GatewayResponseCode_Value_boolean.
Local Abbreviation VScalar := LeanCage_Host_GatewayResponseCode_Value_scalar.
Local Abbreviation VArray := LeanCage_Host_GatewayResponseCode_Value_array.
Local Abbreviation VObject := LeanCage_Host_GatewayResponseCode_Value_object.

Inductive gateway_prefix_mode :=
| gateway_prefix_value
| gateway_prefix_values (count : nat)
| gateway_prefix_fields (count : nat).

Definition gateway_subject_mode (subject : Subject) : gateway_prefix_mode :=
  match subject with
  | SValue _ => gateway_prefix_value
  | SValues values => gateway_prefix_values (nat_of_Nat (List_length_inst1 _ values))
  | SFields fields => gateway_prefix_fields (nat_of_Nat (List_length_inst1 _ fields))
  end.

Definition gateway_prefix_word width bytes :=
  (gateway_natural_decode (firstn width bytes), skipn width bytes).

Lemma gateway_prefix_word_actual width value bytes tail :
  LeanCage_Host_GatewayWords_Encoding width value bytes ->
  gateway_prefix_word (nat_of_Nat width) (gateway_plain_nats bytes ++ tail) = (nat_of_Nat value, tail).
Proof.
  intro WORD; destruct (gateway_plain_word_encoding _ _ _ WORD) as [SIZE VALUE].
  unfold gateway_prefix_word; rewrite <- SIZE, firstn_app, firstn_all, Nat.sub_diag,
    skipn_app, skipn_all, Nat.sub_diag; cbn; rewrite !app_nil_r, VALUE; reflexivity.
Qed.

Definition gateway_prefix_scalar tag width bytes : option (Subject * list nat) :=
  let '(count, rest) := gateway_prefix_word width bytes in
  Some (SValue (VScalar (Nat_of_nat tag) (gateway_imported_nats (firstn count rest))), skipn count rest).

Definition gateway_prefix_step
    (previous : gateway_prefix_mode -> list nat -> option (Subject * list nat))
    (mode : gateway_prefix_mode) (bytes : list nat) : option (Subject * list nat) :=
  match mode with
  | gateway_prefix_value =>
    match bytes with
    | [] => None
    | tag :: rest =>
      match tag with
      | 0 => Some (SValue VNull, rest)
      | 1 => Some (SValue (VBool Bool_false), rest)
      | 2 => Some (SValue (VBool Bool_true), rest)
      | 3 => gateway_prefix_scalar 3 4 rest
      | 4 => gateway_prefix_scalar 4 8 rest
      | 5 => gateway_prefix_scalar 5 8 rest
      | 6 => gateway_prefix_scalar 6 8 rest
      | 7 => let '(count, after) := gateway_prefix_word 4 rest in
        match previous (gateway_prefix_values count) after with
        | Some (SValues values, tail) => Some (SValue (VArray values), tail)
        | _ => None
        end
      | 8 => let '(count, after) := gateway_prefix_word 4 rest in
        match previous (gateway_prefix_fields count) after with
        | Some (SFields fields, tail) => Some (SValue (VObject fields), tail)
        | _ => None
        end
      | 9 => gateway_prefix_scalar 9 8 rest
      | _ => None
      end
    end
  | gateway_prefix_values 0 => Some (SValues (List_nil_inst1 _), bytes)
  | gateway_prefix_values (S count) =>
    match previous gateway_prefix_value bytes with
    | Some (SValue value, after) =>
      match previous (gateway_prefix_values count) after with
      | Some (SValues values, tail) => Some (SValues (List_cons_inst1 _ value values), tail)
      | _ => None
      end
    | _ => None
    end
  | gateway_prefix_fields 0 => Some (SFields (List_nil_inst1 _), bytes)
  | gateway_prefix_fields (S count) =>
    match previous gateway_prefix_value bytes with
    | Some (SValue key, afterKey) =>
      match previous gateway_prefix_value afterKey with
      | Some (SValue value, afterValue) =>
        match previous (gateway_prefix_fields count) afterValue with
        | Some (SFields fields, tail) => Some (SFields
            (List_cons_inst1 _ (Prod_mk_inst3 _ _ key value) fields), tail)
        | _ => None
        end
      | _ => None
      end
    | _ => None
    end
  end.

Fixpoint gateway_prefix_read fuel : gateway_prefix_mode -> list nat -> option (Subject * list nat) :=
  match fuel with
  | 0 => fun _ _ => None
  | S fuel => gateway_prefix_step (gateway_prefix_read fuel)
  end.

Definition gateway_prefix_refines
    (earlier second : gateway_prefix_mode -> list nat -> option (Subject * list nat)) : Prop :=
  forall mode bytes value, earlier mode bytes = Some value -> second mode bytes = Some value.

Ltac gateway_prefix_refine_using contract :=
  lazymatch type of contract with
  | gateway_prefix_refines ?initial ?later =>
    let source := fresh "SOURCE" in intro source;
    repeat first
    [ progress cbn in source |- *
    | discriminate source
    | lazymatch type of source with
      | context [initial ?mode ?input] =>
        let call := fresh "CALL" in
        let subject := fresh "subject" in let tail := fresh "tail" in
        destruct (initial mode input) as [[subject tail] |] eqn:call;
          [rewrite (contract _ _ _ call); destruct subject |discriminate source]
      end ]; congruence
  end.

Lemma gateway_prefix_step_refines earlier second :
  gateway_prefix_refines earlier second ->
  gateway_prefix_refines (gateway_prefix_step earlier) (gateway_prefix_step second).
Proof.
  intros REFINES mode bytes value; unfold gateway_prefix_step.
  destruct mode as [|[|count]|[|count]]; try (intro; assumption).
  - destruct bytes as [|tag rest]; [discriminate |].
    destruct tag as [|[|[|[|[|[|[|[|[|[|tag]]]]]]]]]];
      cbn [gateway_prefix_step]; try (intro; assumption).
    all: match goal with CONTRACT : gateway_prefix_refines _ _ |- _ => gateway_prefix_refine_using CONTRACT end.
  - match goal with CONTRACT : gateway_prefix_refines _ _ |- _ => gateway_prefix_refine_using CONTRACT end.
  - match goal with CONTRACT : gateway_prefix_refines _ _ |- _ => gateway_prefix_refine_using CONTRACT end.
Qed.

Theorem gateway_prefix_read_monotone earlier second :
  earlier <= second -> gateway_prefix_refines (gateway_prefix_read earlier) (gateway_prefix_read second).
Proof.
  revert second; induction earlier as [|earlier IH]; intros [|second] BOUND mode bytes value RESULT;
    cbn in *; try discriminate; try lia.
  eapply gateway_prefix_step_refines; [apply IH; lia |exact RESULT].
Qed.

(* SProp witnesses retain the source relation's strict proposition sort. Their
   fuel is used only inside strict equalities, never to inspect a proof at runtime. *)
Inductive gateway_prefix_readable (subject : Subject) (bytes : list nat) : SProp :=
| gateway_prefix_readable_intro : forall fuel,
    (forall tail, Lean.eq (gateway_prefix_read fuel (gateway_subject_mode subject) (bytes ++ tail))
      (Some (subject, tail))) -> gateway_prefix_readable subject bytes.
