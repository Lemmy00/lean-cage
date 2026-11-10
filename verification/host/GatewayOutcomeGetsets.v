(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: All maintained Outcome properties come from the same source getset table. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayGetsets GatewayOutcome GatewayOutcomeType GatewayGlobals GatewayRegistry
  GatewayErrorRuntime GatewayLoaderRegions.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_observation_name:=map Byte.repr[111;98;115;101;114;118;97;116;105;111;110].
Definition gateway_outcome_property_sources:list gateway_getset_source:=
  map(fun named=>{|gateway_getset_name_symbol:=fst(fst named);gateway_getset_source_name:=map Byte.repr(snd(fst named));
    gateway_getset_getter_symbol:=_host_outcome_get;gateway_getset_setter_symbol:=Some _host_outcome_set;
    gateway_getset_source_closure:=Z.of_nat(snd named)|})
    (combine(combine gateway_outcome_name_symbols gateway_outcome_names)(seq 0 14))++
  [{|gateway_getset_name_symbol:=_host_observation_name;gateway_getset_source_name:=gateway_observation_name;
    gateway_getset_getter_symbol:=_host_outcome_observation;gateway_getset_setter_symbol:=None;
    gateway_getset_source_closure:=0|}].

Theorem actual_outcome_property_initializer_prefix:
  exists trailing,gvar_init v_host_outcome_properties=gateway_getset_initial_data gateway_outcome_property_sources++trailing.
Proof. eexists;reflexivity. Qed.

Theorem actual_outcome_property_names_unique:
  NoDup(map gateway_getset_source_name gateway_outcome_property_sources).
Proof.
  vm_compute;repeat(apply NoDup_cons;[cbn;intuition discriminate|]);apply NoDup_nil.
Qed.

Theorem actual_outcome_observation_source:
  nth_error gateway_outcome_property_sources 14=Some
    {|gateway_getset_name_symbol:=_host_observation_name;gateway_getset_source_name:=gateway_observation_name;
      gateway_getset_getter_symbol:=_host_outcome_observation;gateway_getset_setter_symbol:=None;
      gateway_getset_source_closure:=0|}.
Proof. reflexivity. Qed.

Theorem actual_observation_name_literal:
  gateway_static_cstring _host_observation_name v_host_observation_name gateway_observation_name.
Proof.
  eapply gateway_static_string_from_registration.
  - vm_compute;reflexivity.
  - reflexivity.
  - reflexivity.
  - vm_compute;intuition discriminate.
  - change(12<=18446744073709551616);lia.
Qed.

Definition gateway_outcome_property_names memory:Prop:=
  forall source name,In source gateway_outcome_property_sources ->
    Genv.find_symbol(Clight.globalenv prog)(gateway_getset_name_symbol source)=Some name ->
    gateway_error_cstring memory(Vptr name Ptrofs.zero)(gateway_getset_source_name source).

Definition gateway_outcome_property_literals:list(globvar type):=
  [v___stringlit_50;v___stringlit_29;v___stringlit_49;v___stringlit_48;v___stringlit_47;v___stringlit_46;
   v___stringlit_45;v___stringlit_44;v___stringlit_43;v___stringlit_42;v___stringlit_41;v___stringlit_40;
   v___stringlit_39;v___stringlit_38;v_host_observation_name].

Theorem actual_outcome_property_literal_bindings:
  Forall2(fun source variable=>
    gateway_program_definition(gateway_getset_name_symbol source)global_definitions=Some(Gvar variable) /\
    gateway_static_cstring(gateway_getset_name_symbol source)variable(gateway_getset_source_name source))
    gateway_outcome_property_sources gateway_outcome_property_literals.
Proof.
  unfold gateway_outcome_property_sources,gateway_outcome_property_literals,gateway_outcome_name_symbols,
    gateway_outcome_names,gateway_observation_name;cbn[combine seq map fst snd app].
  repeat(apply Forall2_cons;
    [split;[vm_compute;reflexivity|];eapply gateway_static_string_from_registration;
      [vm_compute;reflexivity|reflexivity|reflexivity|vm_compute;intuition discriminate|
       change Ptrofs.modulus with 18446744073709551616;cbn;lia]|]).
  apply Forall2_nil.
Qed.

Theorem gateway_outcome_property_literal_registered source:
  In source gateway_outcome_property_sources ->exists variable,
    gateway_program_definition(gateway_getset_name_symbol source)global_definitions=Some(Gvar variable) /\
    gateway_static_cstring(gateway_getset_name_symbol source)variable(gateway_getset_source_name source).
Proof.
  pose proof actual_outcome_property_literal_bindings as MATCH.
  induction MATCH;intros MEMBER;[contradiction|].
  destruct MEMBER as[SAME|MEMBER];[subst x;exists y;exact H|apply IHMATCH;exact MEMBER].
Qed.

Theorem gateway_outcome_property_names_from_loader memory:
  gateway_native_loader_boundary(Clight.globalenv prog)memory ->gateway_outcome_property_names memory.
Proof.
  intros LOADER source name MEMBER SYMBOL.
  destruct(gateway_outcome_property_literal_registered source MEMBER)as(variable &DEFINITION &LITERAL).
  destruct LITERAL as[DEF[NONVOLATILE[NONZERO[BOUND[SIZE CONTENTS]]]]].
  assert(POSITIVE:0<init_data_list_size(gvar_init variable))by(rewrite SIZE;lia).
  destruct(gateway_native_initialized _ _ LOADER _ _ DEFINITION NONVOLATILE POSITIVE)as(actual &VIEW).
  assert(SAME:actual=name)by(destruct VIEW as[_[_[ACTUAL REST]]];congruence);subst actual.
  eapply gateway_loaded_region_cstring;[|exact VIEW].
  exact(conj DEF(conj NONVOLATILE(conj NONZERO(conj BOUND(conj SIZE CONTENTS))))).
Qed.

Theorem actual_outcome_properties_from_regions memory table:
  gateway_outcome_property_names memory ->
  Genv.load_store_init_data(Clight.genv_genv(Clight.globalenv prog))memory table 0(gvar_init v_host_outcome_properties) ->
  exists entries,Forall2(gateway_getset_resolves(Clight.globalenv prog))gateway_outcome_property_sources entries /\
    gateway_getsets_memory memory table 0 entries /\NoDup(map gateway_getset_name entries) /\
    exists observation getter,
      nth_error entries 14=Some observation /\gateway_getset_name observation=gateway_observation_name /\
      Genv.find_symbol(Clight.globalenv prog)_host_outcome_observation=Some getter /\
      gateway_getset_getter observation=Vptr getter Ptrofs.zero /\
      gateway_getset_setter observation=Vnullptr /\gateway_getset_closure observation=Vnullptr.
Proof.
  intros NAMES INITIAL.
  destruct actual_outcome_property_initializer_prefix as[trailing SOURCE];rewrite SOURCE in INITIAL.
  pose proof(gateway_relocated_initial_prefix(Clight.globalenv prog)memory table 0 _ _ INITIAL)as PREFIX.
  destruct(gateway_getsets_from_relocated_initializers(Clight.globalenv prog)memory table 0 gateway_outcome_property_sources NAMES PREFIX)
    as(entries &RESOLVES &MEMORY).
  pose proof(gateway_resolved_getset_names _ _ _ RESOLVES)as NAMES_EQUAL.
  assert(SELECTED:exists observation,nth_error entries 14=Some observation /\
    gateway_getset_resolves(Clight.globalenv prog)
      {|gateway_getset_name_symbol:=_host_observation_name;gateway_getset_source_name:=gateway_observation_name;
        gateway_getset_getter_symbol:=_host_outcome_observation;gateway_getset_setter_symbol:=None;
        gateway_getset_source_closure:=0|}observation).
  { eapply gateway_resolved_getset_at;[exact RESOLVES|exact actual_outcome_observation_source]. }
  exists entries;split;[exact RESOLVES|]. split;[exact MEMORY|].
  split;[rewrite NAMES_EQUAL;exact actual_outcome_property_names_unique|].
  destruct SELECTED as(observation &POSITION &NAME &[getter[GETTER TARGET]] &SETTER &CLOSURE).
  exists observation,getter;split;[exact POSITION|]. split;[exact NAME|]. split;[exact GETTER|].
  split;[exact TARGET|]. split;[exact SETTER|exact CLOSURE].
Qed.
