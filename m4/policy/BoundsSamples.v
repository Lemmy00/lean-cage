(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.bounds: Accepted boundaries and each distinct rejected condition. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine.
From LeanCageMain Require Import Main MainStructure MainMemory MainSamples.
From LeanCageBounds Require Import BoundsStructure BoundsSource BoundsWitnesses.
Import ListNotations.
Open Scope Z_scope.
Record bounds_case := {case_argc:Z;case_bytes:Z;case_values:list Z}.
Definition maximum_values:list Z :=
 [1073741824;256;100000;3600000000;3600000;268435456;65536;67108864;16777216;16777216].
Definition replace_value (i:nat) value := firstn i minimal_values++[value]++skipn(S i)minimal_values.
Definition rejected_numeric_values :=
 [replace_value 0%nat 16777215;
  replace_value 0%nat 1073741825;
  replace_value 0%nat 16777217;
  replace_value 1%nat 3;
  replace_value 1%nat 257;
  replace_value 2%nat 999;
  replace_value 2%nat 100001;
  replace_value 3%nat 9999;
  replace_value 3%nat 3600000001;
  replace_value 4%nat 9;
  replace_value 4%nat 3600001;
  replace_value 5%nat 1048575;
  replace_value 5%nat 268435457;
  replace_value 5%nat 1048577;
  replace_value 6%nat 63;
  replace_value 6%nat 65537;
  replace_value 7%nat 67108865;
  replace_value 8%nat 16777217;
  replace_value 9%nat 16777217].
Definition bounds_cases :=
 [Build_bounds_case 17 8 minimal_values;Build_bounds_case 80 16384 maximum_values;
  Build_bounds_case 17 0 minimal_values;
  Build_bounds_case 81 8 minimal_values;Build_bounds_case 17 16385 minimal_values]++
 map(Build_bounds_case 17 8)rejected_numeric_values++
 [Build_bounds_case 17 8(replace_value 0 18446744073709551615);
  Build_bounds_case 2147483647 18446744073709551615 minimal_values].
Definition case_rejected c := bounds_rejected(case_argc c)(case_bytes c)(case_values c).
Definition case_owned c :=
 (17<=?case_argc c)&&(case_argc c<=?2147483647)&&
 (0<=?case_bytes c)&&(case_bytes c<=?Int64.max_unsigned)&&Nat.eqb(length(case_values c))10&&
 forallb(fun x=>(0<=?x)&&(x<=?Int64.max_unsigned))(case_values c).
Lemma case_owned_sound c : case_owned c=true ->
 17<=case_argc c<=2147483647 /\ 0<=case_bytes c<=Int64.max_unsigned /\
 length(case_values c)=10%nat /\ Forall(fun x=>0<=x<=Int64.max_unsigned)(case_values c).
Proof.
 unfold case_owned;rewrite !andb_true_iff;intros[[[[[LOW HIGH]ZERO]BYTES]LEN]VALUES].
 apply Z.leb_le in LOW;apply Z.leb_le in HIGH;apply Z.leb_le in ZERO;apply Z.leb_le in BYTES.
 apply Nat.eqb_eq in LEN;split;[lia|]. split;[lia|]. split;[exact LEN|].
 apply Forall_forall;intros x IN;rewrite forallb_forall in VALUES;specialize(VALUES x IN).
 rewrite andb_true_iff,!Z.leb_le in VALUES;exact VALUES.
Qed.
Theorem bounds_cases_owned : forallb case_owned bounds_cases=true.
Proof. vm_compute;reflexivity. Qed.
Theorem bounds_cases_results : map case_rejected bounds_cases=repeat false 3++repeat true 23.
Proof. vm_compute;reflexivity. Qed.
Fixpoint first_rejected_guard values guards : option nat := match guards with
 | []=>None | g::rest=>if guard_bad g(nth(Z.to_nat(guard_index g))values 0)
 then Some 0%nat else option_map S(first_rejected_guard values rest)end.
Theorem every_numeric_rejection :
 map(fun values=>first_rejected_guard values policy_guards)rejected_numeric_values=
 map(@Some nat)(seq 0 19).
Proof. vm_compute;reflexivity. Qed.
Theorem bounds_cases_allocated : forall c,In c bounds_cases ->
 exists initial m count final,Genv.init_mem Main.prog=Some initial /\
 policy_stores main_policy_block 0 initial(case_values c)m /\ (count<=140)%nat /\ forall cell k,
 steps main_ge cell(live(State f_main bounds_region k empty_env
  (bounds_fixture_temps(case_argc c)(case_bytes c))m))
 (repeat(source_step E0)count)(live(bounds_endpoint empty_env final k m(case_rejected c))) /\
 (forall n,(n<=count)%nat ->
 steps main_ge cell(live(State f_main bounds_region k empty_env
  (bounds_fixture_temps(case_argc c)(case_bytes c))m))
 (repeat(source_step E0)n++[loss_step])(dead m)).
Proof.
 intros c IN;pose proof bounds_cases_owned as OWN;rewrite forallb_forall in OWN.
 destruct(case_owned_sound c(OWN c IN))as[COUNT[BYTES[LEN RANGE]]].
 apply bounds_allocated_execution;assumption.
Qed.
