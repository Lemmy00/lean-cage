(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-parent.inputs: Bytes, pointers and strings inhabit the very run's starting memory. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers Values Memory.
Require Import Library.
From LeanCageMain Require Import MainMemory MainEntry.
From LeanCageArguments Require Import ArgumentMemory.
From LeanCageParent Require Import ValidationInputs.
Import ListNotations.

Definition validation_input_representation before fields argv textfields bytes export_bytes tree_bytes stdin_bytes sources
 inputs export tree stdin x rest :=
 exists numbers parent_arg export_arg tree_arg stdin_arg,
 map guest_bytes numbers=textfields /\guest_bytes parent_arg=bytes /\
 guest_bytes export_arg=export_bytes /\guest_bytes tree_arg=tree_bytes /\guest_bytes stdin_arg=stdin_bytes /\
 map guest_bytes(x::rest)=sources /\inputs=map guest_numeric numbers /\
 export=guest_pointer export_arg /\tree=guest_pointer tree_arg /\stdin=guest_pointer stdin_arg /\
 guest_arguments_owned before argv Ptrofs.zero 2(numbers++parent_arg::export_arg::tree_arg::stdin_arg::x::rest) /\
 numeric_entry_buffers before fields argv Ptrofs.zero inputs.

Theorem representation_has_owned_argv before fields argv textfields bytes export_bytes tree_bytes stdin_bytes sources
 inputs export tree stdin x rest :
 validation_input_representation before fields argv textfields bytes export_bytes tree_bytes stdin_bytes sources
 inputs export tree stdin x rest->
 exists all,map guest_bytes all=textfields++bytes::export_bytes::tree_bytes::stdin_bytes::sources /\
 guest_arguments_owned before argv Ptrofs.zero 2 all /\numeric_entry_buffers before fields argv Ptrofs.zero inputs.
Proof.
 intros(numbers & p & ex & tr & st & NB & PB & EB & TB & SB & GB & NUM & E & T & S & OWN & READY).
 exists(numbers++p::ex::tr::st::x::rest);split.
 - rewrite map_app.
   change(map guest_bytes numbers++guest_bytes p::guest_bytes ex::guest_bytes tr::guest_bytes st::map guest_bytes(x::rest)=
    textfields++bytes::export_bytes::tree_bytes::stdin_bytes::sources).
   rewrite NB,PB,EB,TB,SB,GB;reflexivity.
 - auto.
Qed.

Theorem representation_numeric_data before fields argv textfields bytes export_bytes tree_bytes stdin_bytes sources
 inputs export tree stdin x rest :
 validation_input_representation before fields argv textfields bytes export_bytes tree_bytes stdin_bytes sources
 inputs export tree stdin x rest->map input_bytes inputs=textfields /\map guest_bytes(x::rest)=sources.
Proof.
 intros(numbers & p & ex & tr & st & NB & PB & EB & TB & SB & GB & NUM & REST).
 subst inputs;split;[rewrite map_map;exact NB|exact GB].
Qed.
