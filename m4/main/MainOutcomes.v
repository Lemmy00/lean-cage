(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.main-inputs: Exact success vector and the first rejected numeric field. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Integers.
From LeanCageMainNumber Require Import NumberMath.
From LeanCageMain Require Import MainMemory MainPacked.
Import ListNotations.
Open Scope Z_scope.
Fixpoint field_values fields : list Z := match fields with
 | []=>[]|bytes::rest=>match decimal_number bytes with Some v=>v::field_values rest|None=>[]end end.
Fixpoint fields_complete fields : bool := match fields with
 | []=>true|bytes::rest=>match decimal_number bytes with Some _=>fields_complete rest|None=>false end end.
Lemma numeric_values_data inputs : numeric_values inputs=field_values(map input_bytes inputs).
Proof. induction inputs as[|x rest IH];cbn;[reflexivity|]. destruct(decimal_number(input_bytes x));[rewrite IH|];reflexivity. Qed.
Lemma numeric_complete_data inputs : numeric_complete inputs=fields_complete(map input_bytes inputs).
Proof. induction inputs as[|x rest IH];cbn;[reflexivity|]. destruct(decimal_number(input_bytes x));auto. Qed.
Theorem fields_success fields : fields_complete fields=true <->
 Forall2(fun bytes value=>decimal_number bytes=Some value)fields(field_values fields).
Proof.
 induction fields as[|bytes rest IH];cbn;[split;intros;constructor|].
 destruct(decimal_number bytes)as[value|]eqn:PARSED.
 - rewrite IH;split;[intro ALL;constructor;assumption|intro ALL;inversion ALL;assumption].
 - split;[discriminate|intro ALL;inversion ALL].
Qed.
Theorem fields_first_rejection fields : fields_complete fields=false ->
 exists before rejected after,
 fields=before++rejected::after /\ decimal_number rejected=None /\
 Forall2(fun bytes value=>decimal_number bytes=Some value)before(field_values fields).
Proof.
 induction fields as[|bytes rest IH];[discriminate|]. cbn.
 destruct(decimal_number bytes)as[value|]eqn:PARSED;intros REJECT.
 - destruct(IH REJECT)as[before[bad[after[EQ[NONE PREFIX]]]]].
   exists(bytes::before),bad,after;split;[cbn;congruence|]. split;[exact NONE|constructor;assumption].
 - exists [],bytes,rest;split;[reflexivity|]. split;[exact PARSED|constructor].
Qed.
Theorem fields_successful_count fields : (length(field_values fields)<=length fields)%nat /\
 (fields_complete fields=true <-> length(field_values fields)=length fields).
Proof.
 pose proof(numeric_values_length(packed_inputs 1%positive 0 fields))as LEN.
 pose proof(numeric_complete_length(packed_inputs 1%positive 0 fields))as COMPLETE.
 rewrite numeric_values_data,packed_inputs_data,packed_inputs_length in LEN.
 rewrite numeric_values_data,numeric_complete_data,packed_inputs_data,packed_inputs_length in COMPLETE;auto.
Qed.
