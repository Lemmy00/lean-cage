(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: SDK count effects do not select a source ownership ticket. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers Values Memory Globalenvs Clight.
From HostGateway Require Import GatewayMachine GatewayPython GatewayObjects GatewayReferences
  GatewayReferenceLedger GatewayReferenceAccounting GatewayTypeRuntime GatewayOutcomeType GatewayOutcomeAllocation.
Import ListNotations.
Open Scope Z_scope.

Record gateway_reference_credit (before after:python_world)(pointer:Values.val):Prop:={
  gateway_reference_credit_target:python_native_strong after pointer=S(python_native_strong before pointer);
  gateway_reference_credit_other:forall other,other<>pointer->
    python_native_strong after other=python_native_strong before other
}.

Lemma gateway_constructor_reference_credit before heap memory pointer after after_heap changed value:
  gateway_constructor_return before heap memory pointer after after_heap changed value->
  gateway_reference_credit before after pointer.
Proof.
  intro EFFECT;constructor;[exact(gateway_constructor_owned _ _ _ _ _ _ _ _ EFFECT)|].
  intros other DIFFERENT;apply(gateway_constructor_refs _ _ _ _ _ _ _ _ EFFECT).
  intros[HEAD|TAIL];[congruence|contradiction].
Qed.

Lemma gateway_incref_reference_credit before pointer memory after changed:
  python_incref_return before pointer memory after changed->gateway_reference_credit before after pointer.
Proof.
  intro EFFECT;constructor;[exact(python_incref_native _ _ _ _ _ EFFECT)|].
  intros other DIFFERENT;exact(proj2(python_incref_others _ _ _ _ _ EFFECT other DIFFERENT)).
Qed.

Theorem gateway_reference_credit_mints ledger owner pointer before after:
  gateway_reference_ledger_well_formed ledger->gateway_reference_counts_fit ledger before->
  gateway_reference_take owner(gateway_reference_entries ledger)=None->
  gateway_reference_credit before after pointer->
  exists next,
    gateway_reference_apply(gateway_reference_mint owner pointer)(gateway_reference_valid ledger)=
      gateway_reference_valid next /\gateway_reference_ledger_well_formed next /\
    gateway_reference_counts_fit next after /\
    gateway_reference_owns next owner(gateway_reference_next ledger)pointer /\
    (forall place ticket value,gateway_reference_owns ledger place ticket value->
      gateway_reference_owns next place ticket value).
Proof.
  intros FORMED FIT VACANT CREDIT;eapply gateway_reference_mint_counts;
    [exact FORMED|exact FIT|exact VACANT|exact(gateway_reference_credit_target _ _ _ CREDIT)|
      exact(gateway_reference_credit_other _ _ _ CREDIT)].
Qed.

(* Counts project the current source invocation's C-owned references. SDK
   internal references and other invocations are not a global count frame. *)
Definition gateway_source_outcome_type(description:gateway_type_description):Prop:=
  exists new initialize destroy traverse clear methods properties,
    description=GatewayOutcomeType.gateway_outcome_description new initialize destroy traverse clear methods properties /\
    Globalenvs.Genv.find_symbol(Clight.globalenv GatewaySource.prog)GatewaySource._PyType_GenericNew=Some new /\
    Globalenvs.Genv.find_symbol(Clight.globalenv GatewaySource.prog)GatewaySource._host_outcome_init=Some initialize /\
    Globalenvs.Genv.find_symbol(Clight.globalenv GatewaySource.prog)GatewaySource._host_outcome_free=Some destroy /\
    Globalenvs.Genv.find_symbol(Clight.globalenv GatewaySource.prog)GatewaySource._host_outcome_traverse=Some traverse /\
    Globalenvs.Genv.find_symbol(Clight.globalenv GatewaySource.prog)GatewaySource._host_outcome_clear=Some clear /\
    Globalenvs.Genv.find_symbol(Clight.globalenv GatewaySource.prog)GatewaySource._host_outcome_methods=Some methods /\
    Globalenvs.Genv.find_symbol(Clight.globalenv GatewaySource.prog)GatewaySource._host_outcome_properties=Some properties.

Definition gateway_source_outcome_spec(pointer:Values.val):Prop:=exists object,
  Globalenvs.Genv.find_symbol(Clight.globalenv GatewaySource.prog)GatewaySource._host_outcome_spec=Some object /\
    pointer=Vptr object Ptrofs.zero.

(* Only the actual native type roles enter these count laws. Raw descriptions,
   layout, allocator selection and call arguments remain separately checked. *)
Record gateway_type_reference_runtime {World Event}(backend:gateway_backend World Event)
    (python:World->python_world)(objects:World->gateway_object_heap)
    (types:World->Values.val->option gateway_type_description)(allocator:World->Values.val->Prop)
    (normal:mem->World->Prop):Prop:={
  gateway_type_reference_from_spec:forall before world pointer description result after next observed,
    normal before world->gateway_source_outcome_spec pointer->gateway_source_outcome_type description->
    gateway_type_spec_memory before pointer description->
    16<=gateway_type_basicsize description<=Int.max_signed->gateway_type_itemsize description=0->
    gateway_type_operation backend gateway_type_from_spec[pointer]before world result after next observed->
    result<>Vnullptr->gateway_reference_credit(python world)(python next)result;
  gateway_type_reference_generic_alloc:forall before world class description result after next observed,
    gateway_objects_ready(python world)(objects world)before->
    gateway_source_outcome_type description->
    gateway_rooted(python world)(objects world)class->types world class=Some description->allocator world class->
    gateway_type_basicsize description=24->gateway_type_itemsize description=0->
    Int.and(gateway_type_flags description)(Int.repr 256)=Int.repr 256->
    gateway_object_operation backend gateway_api_generic_alloc[class;Vlong Int64.zero]
      before world result after next observed->result<>Vnullptr->
    gateway_reference_credit(python world)(python next)result
}.
