(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.main-inputs: Independent argument ownership and sequential policy stores. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata.
Require Import ScalarMemory.
From LeanCageMainNumber Require Import NumberMath NumberMemory NumberStorage NumberSafety.
Import ListNotations.
Open Scope Z_scope.
Record numeric_input := {
 input_block : Values.block; input_offset : Ptrofs.int; input_bytes : list byte
}.
Definition input_pointer x := Vptr(input_block x)(input_offset x).
Definition argument_offset ofs i := Ptrofs.add ofs (Ptrofs.repr(8*(i+2))).
Fixpoint numeric_values inputs : list Z := match inputs with
 | []=>[] | x::rest=>match decimal_number(input_bytes x) with Some v=>v::numeric_values rest|None=>[] end end.
Fixpoint numeric_complete inputs : bool := match inputs with
 | []=>true | x::rest=>match decimal_number(input_bytes x) with Some _=>numeric_complete rest|None=>false end end.
Fixpoint policy_cells i values : list scalar_cell := match values with
 | []=>[] | v::rest=>{|scalar_chunk:=Mint64;scalar_offset:=8*i;scalar_value:=Vlong(Int64.repr v)|}::policy_cells(i+1)rest end.
Definition policy_stores policy i before values after := scalar_stores policy before (policy_cells i values) after.
Definition policy_prefix policy i before values after :=
 exists done rest, values=done++rest /\ policy_stores policy i before done after.
Definition fields_mapping m fields policy := forall i, 0<=i<10 ->
 Mem.loadv Mptr m (Vptr fields (Ptrofs.repr(8*i)))=Some(Vptr policy(Ptrofs.repr(8*i))).
Fixpoint arguments_ready m policy argv ofs i inputs : Prop := match inputs with
 | []=>True | x::rest=>
 number_input m (input_block x)(input_offset x)(input_bytes x) /\ input_block x<>policy /\
 Mem.loadv Mptr m (Vptr argv(argument_offset ofs i))=Some(input_pointer x) /\
 arguments_ready m policy argv ofs (i+1)rest end.
Definition policy_writable m policy := forall i, 0<=i<10 -> number_output m policy(Ptrofs.repr(8*i)).
Definition numeric_buffers m policy fields argv ofs i inputs :=
 fields<>policy /\ argv<>policy /\ fields_mapping m fields policy /\
 arguments_ready m policy argv ofs i inputs /\ policy_writable m policy.
Lemma numeric_values_length inputs : (length(numeric_values inputs)<=length inputs)%nat.
Proof. induction inputs as [|x rest IH];cbn;[lia|]. destruct(decimal_number(input_bytes x));cbn;lia. Qed.
Lemma numeric_complete_length inputs : numeric_complete inputs=true <-> length(numeric_values inputs)=length inputs.
Proof.
 induction inputs as [|x rest IH];cbn;[tauto|].
 destruct(decimal_number(input_bytes x));cbn;[rewrite IH;lia|split;discriminate].
Qed.
Lemma number_memory_loadv_other before policy ofs parsed after chunk b pos :
 number_memory before policy ofs parsed after -> b<>policy ->
 Mem.loadv chunk after (Vptr b pos)=Mem.loadv chunk before (Vptr b pos).
Proof.
 intros [SAME|POST] NE;[subst;reflexivity|].
 destruct parsed;[|cbn in POST;subst;reflexivity]. apply number_post_store in POST.
 unfold Mem.loadv;destruct(zle _ _);[|reflexivity]. eapply Mem.load_store_other;[exact POST|auto].
Qed.
Lemma number_memory_input_other before policy ofs parsed after x :
 number_memory before policy ofs parsed after -> input_block x<>policy ->
 number_input before(input_block x)(input_offset x)(input_bytes x) ->
 number_input after(input_block x)(input_offset x)(input_bytes x).
Proof.
 intros MEMORY NE [BOUND [NOZERO LOAD]]. split;[exact BOUND|]. split;[exact NOZERO|].
 destruct MEMORY as [SAME|POST];[subst;exact LOAD|].
 destruct parsed;[|cbn in POST;subst;exact LOAD]. apply number_post_store in POST.
 rewrite (Mem.loadbytes_store_other _ _ _ _ _ _ POST) by auto;exact LOAD.
Qed.
Lemma number_memory_output before policy ofs parsed after pos :
 number_memory before policy ofs parsed after -> number_output before policy pos ->
 number_output after policy pos.
Proof.
 intros MEMORY [BOUND [PERM ALIGN]]. split;[exact BOUND|]. split;[|exact ALIGN].
 red;intros q RANGE;apply(number_memory_permissions _ _ _ _ _ MEMORY);apply PERM;exact RANGE.
Qed.
Lemma numeric_buffers_preserved before policy outofs parsed after fields argv ofs i inputs :
 number_memory before policy outofs parsed after ->
 numeric_buffers before policy fields argv ofs i inputs ->
 numeric_buffers after policy fields argv ofs i inputs.
Proof.
 intros MEMORY [FIELDS [ARGV [TABLE [ARGS OUTPUT]]]].
 split;[exact FIELDS|]. split;[exact ARGV|]. split.
 - intros j BOUND;rewrite(number_memory_loadv_other _ _ _ _ _ _ _ _ MEMORY FIELDS);apply TABLE;exact BOUND.
 - split.
   + revert i ARGS;induction inputs as [|x rest IH];intros i ARGS;[exact I|].
     destruct ARGS as [INPUT [NE [LOAD TAIL]]];split.
     * eapply number_memory_input_other;eassumption.
     * split;[exact NE|]. split.
       -- rewrite(number_memory_loadv_other _ _ _ _ _ _ _ _ MEMORY ARGV);exact LOAD.
       -- apply IH;exact TAIL.
   + intros j BOUND;eapply number_memory_output;[exact MEMORY|apply OUTPUT;exact BOUND].
Qed.
Lemma numeric_buffers_tail m policy fields argv ofs i x rest :
 numeric_buffers m policy fields argv ofs i (x::rest) ->
 numeric_buffers m policy fields argv ofs (i+1) rest.
Proof. intros [F [A [T [ARGS O]]]];destruct ARGS as [_ [_ [_ TAIL]]];split;[exact F|]. split;[exact A|]. split;[exact T|]. split;assumption. Qed.
Lemma policy_prefix_initial policy i m values : policy_prefix policy i m values m.
Proof. exists [],values;split;[reflexivity|constructor]. Qed.
Lemma policy_prefix_head policy i before value values after : 0<=i<10 ->
 number_memory before policy(Ptrofs.repr(8*i))(Some value)after ->
 policy_prefix policy i before(value::values)after.
Proof.
 intros INDEX [SAME|POST];[subst;apply policy_prefix_initial|].
 exists [value],values;split;[reflexivity|].
 apply number_post_store in POST.
 rewrite Ptrofs.unsigned_repr in POST by (change (0<=8*i<=18446744073709551615);lia).
 econstructor;[exact POST|constructor].
Qed.
Lemma policy_prefix_cons policy i before value values mid after : 0<=i<10 ->
 number_post before policy(Ptrofs.repr(8*i))(Some value)mid ->
 policy_prefix policy(i+1)mid values after -> policy_prefix policy i before(value::values)after.
Proof.
 intros INDEX POST [done [rest [EQ STORES]]]. exists(value::done),rest;split;[cbn;congruence|].
 apply number_post_store in POST.
 rewrite Ptrofs.unsigned_repr in POST by (change (0<=8*i<=18446744073709551615);lia).
 econstructor;eassumption.
Qed.
Lemma policy_stores_cons policy i before value values mid after : 0<=i<10 ->
 number_post before policy(Ptrofs.repr(8*i))(Some value)mid ->
 policy_stores policy(i+1)mid values after -> policy_stores policy i before(value::values)after.
Proof.
 intros INDEX POST STORES;apply number_post_store in POST.
 rewrite Ptrofs.unsigned_repr in POST by (change (0<=8*i<=18446744073709551615);lia).
 econstructor;eassumption.
Qed.
