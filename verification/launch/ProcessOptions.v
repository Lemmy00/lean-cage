(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.origin: The real SETOPTIONS argument excludes seccomp suspension. *)
From Stdlib Require Import List ZArith.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps.
From EntryProcess Require Import ProcessTrace.
Import ListNotations.

Lemma caller_options_evaluated ge e le memory:
  evaluated ge e le memory tracer_options(Vlong(Int64.repr 1048592)).
Proof.
  unfold tracer_options;eapply value_cast with(v:=Vlong(Int64.repr 1048592));[|reflexivity].
  eapply value_cast with(v:=Vint(Int.repr 1048592));[|reflexivity].
  eapply value_binary;[apply value_int|apply value_int|reflexivity].
Qed.

Theorem caller_options_argument_values ge e le memory request child address values:
  eval_exprlist ge e le memory
    [Econst_int request tint;child;address;tracer_options]
    [tint;tint;tptr tvoid;tptr tvoid]values ->
  exists actual_child actual_address,
    values=[Vint request;actual_child;actual_address;Vlong(Int64.repr 1048592)].
Proof.
  intro VALUES.
  inversion VALUES as[|a rest ty types v11 v12 tail1 HEAD1 CAST1 REST1];subst;clear VALUES.
  apply literal_value_exact in HEAD1;subst v11;cbn in CAST1;inversion CAST1;subst v12;clear CAST1.
  inversion REST1 as[|a rest ty types v21 v22 tail2 HEAD2 CAST2 REST2];subst;clear REST1.
  inversion REST2 as[|a rest ty types v31 v32 tail3 HEAD3 CAST3 REST3];subst;clear REST2.
  inversion REST3 as[|a rest ty types v41 v42 tail4 HEAD4 CAST4 REST4];subst;clear REST3.
  pose proof(evaluated_unique _ _ _ _ _ _(caller_options_evaluated ge e le memory)_ HEAD4)as EXACT;subst v41.
  change(Some(Vlong(Int64.repr 1048592))=Some v42)in CAST4;inversion CAST4;subst v42.
  inversion REST4;subst;do 2 eexists;reflexivity.
Qed.
