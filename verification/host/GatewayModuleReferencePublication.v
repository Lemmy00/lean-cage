(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Publication borrows the retained class reference. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayRuntime GatewayPython GatewayObjects
  GatewayTypeRuntime GatewayModulePublication GatewayErrorRuntime GatewayThreadRuntime GatewayReferenceLedger
  GatewayReferencePlaces GatewayReferenceAccounting GatewayReferenceHistory GatewayReferenceAbandon
  GatewayReferenceHistoryMove.
Import ListNotations.

(* The pool counts this source invocation, designated C globals and their
   unreleased retired references. It does not count SDK graph edges or freeze
   public module attributes, presentation records or other invocations. *)
Record gateway_module_reference_runtime {World Event}(backend:gateway_backend World Event)
    (python:World->python_world)(objects:World->gateway_object_heap)(normal:mem->World->Prop):Prop:={
  gateway_module_add_ref_pool:forall before world module name name_bytes class result after next observed,
    normal before world->gateway_rooted(python world)(objects world)module->
    gateway_rooted(python world)(objects world)class->gateway_error_cstring before name name_bytes->
    gateway_type_operation backend gateway_module_add_object_ref[module;name;class]
      before world result after next observed->
    gateway_native_references_frame(python world)(python next)[]
}.

Theorem gateway_module_publication_reference_pool {World Event}(backend:gateway_backend World Event)
    python objects types allocator instances leases normal attached io native stable
    (runtime:gateway_type_runtime backend python objects types allocator instances leases normal attached io native stable)
    (references:gateway_module_reference_runtime backend python objects normal)
    (ge:Clight.genv)before world module name name_bytes class symbol returned after next observed position ledger retired ticket:
  gateway_history_well_formed position ledger retired->gateway_history_counts_fit ledger retired(python world)->
  gateway_reference_owns ledger(gateway_reference_global _host_outcome_class)ticket class->
  normal before world->gateway_rooted(python world)(objects world)module->
  gateway_error_cstring before name name_bytes->
  Genv.find_symbol ge _host_outcome_class=Some symbol->native world symbol->
  Mem.load Mptr before symbol 0=Some class->
  gateway_type_operation backend gateway_module_add_object_ref[module;name;class]
    before world returned after next observed->
  gateway_history_well_formed(S position)ledger retired /\
  gateway_history_counts_fit ledger retired(python next) /\
  gateway_reference_owns ledger(gateway_reference_global _host_outcome_class)ticket class /\
  gateway_reference_place_value ge(Returnstate returned Kstop after)(gateway_reference_global _host_outcome_class)class /\
  Mem.load Mptr after symbol 0=Some class /\native next symbol /\
  gateway_rooted(python next)(objects next)class /\attached after next /\
  (exists status,returned=Vint status /\(status=Int.zero->normal after next)) /\
  io observed=None /\
  (forall pointer,python_native_strong(python next)pointer=python_native_strong(python world)pointer).
Proof.
  intros FORMED FIT OWNED NORMAL MODULE NAME SYMBOL PRIVATE GLOBAL OPERATION.
  assert(POSITIVE:(0<python_native_strong(python world)class)%nat).
  { pose proof(gateway_reference_owned_count_positive _ _ _ _ OWNED)as ACTIVE.
    specialize(FIT class);unfold gateway_history_total_count in FIT;lia. }
  assert(CLASS:gateway_rooted(python world)(objects world)class)by(apply gateway_direct_root;exact POSITIVE).
  pose proof(gateway_module_add_ref_pool _ _ _ _ references _ _ _ _ _ _ _ _ _ _
    NORMAL MODULE CLASS NAME OPERATION)as COUNTS.
  assert(SAME:forall pointer,python_native_strong(python next)pointer=python_native_strong(python world)pointer).
  { intro pointer;apply COUNTS;intro BAD;inversion BAD. }
  destruct(@gateway_module_add_ref_effect World Event backend python objects types allocator instances leases
    normal attached io native stable runtime before world module name name_bytes class returned after next observed
    NORMAL MODULE CLASS NAME OPERATION)as[STATUS[ATTACHED[OLD_LEASES[ACCESS[FRAME QUIET]]]]].
  assert(LOAD:Mem.load Mptr after symbol 0=Some class).
  { eapply Mem.load_unchanged_on;[exact FRAME| |exact GLOBAL].
    intros;split;[left;exact PRIVATE|cbn;tauto]. }
  assert(LIVE:Mem.valid_block before symbol).
  { eapply Mem.valid_access_valid_block,Mem.valid_access_implies;
      [eapply Mem.load_valid_access;exact GLOBAL|constructor]. }
  split;[apply gateway_history_keep_formed;exact FORMED|]. split.
  - intro pointer;rewrite SAME;apply FIT.
  - split;[exact OWNED|]. split;[eapply gateway_reference_global_binding;eassumption|].
    split;[exact LOAD|]. split;[apply(proj1 ACCESS);assumption|]. split.
    + apply gateway_direct_root;rewrite SAME;exact POSITIVE.
    + split;[exact ATTACHED|]. split;[exact STATUS|]. split;[exact QUIET|exact SAME].
Qed.

Definition gateway_module_reference_publication_select {World Event}:gateway_history_selector World Event:=
  fun _ _ _ _ _=>gateway_history_current gateway_reference_keep.

Definition gateway_module_reference_add_definition:Ctypes.fundef Clight.function:=External
  (EF_external "PyModule_AddObjectRef"(mksignature[Xptr;Xptr;Xptr]Xint cc_default))
  [tptr(Tstruct __object noattr);tptr tschar;tptr(Tstruct __object noattr)]tint cc_default.

Theorem gateway_actual_module_reference_publication {World Event}(backend:gateway_backend World Event)
    python objects types allocator instances leases normal attached io native stable
    (runtime:gateway_type_runtime backend python objects types allocator instances leases normal attached io native stable)
    (references:gateway_module_reference_runtime backend python objects normal)
    before world module name name_bytes class symbol parameters continuation returned after next observed
    position ledger retired ticket:
  gateway_history_well_formed position ledger retired->gateway_history_counts_fit ledger retired(python world)->
  gateway_reference_owns ledger(gateway_reference_global _host_outcome_class)ticket class->
  normal before world->gateway_rooted(python world)(objects world)module->
  gateway_error_cstring before name name_bytes->
  Genv.find_symbol(Clight.globalenv prog)_host_outcome_class=Some symbol->native world symbol->
  Mem.load Mptr before symbol 0=Some class->
  gateway_step backend(Clight.globalenv prog)
    (gateway_live(Callstate gateway_module_reference_add_definition[module;name;class]
      (module_outcome_add_cont parameters continuation)before)world)(gateway_primitive observed)
    (gateway_live(Returnstate returned(module_outcome_add_cont parameters continuation)after)next)->
  gateway_history_execution backend(Clight.globalenv prog)gateway_module_reference_publication_select position
    (gateway_live(Callstate gateway_module_reference_add_definition[module;name;class]
      (module_outcome_add_cont parameters continuation)before)world)
    {|gateway_history_active:=gateway_reference_valid ledger;gateway_history_abandoned:=retired|}
    [gateway_primitive observed]
    (gateway_live(Returnstate returned(module_outcome_add_cont parameters continuation)after)next)
    {|gateway_history_active:=gateway_reference_valid ledger;gateway_history_abandoned:=retired|} /\
  gateway_history_well_formed(S position)ledger retired /\
  gateway_history_counts_fit ledger retired(python next) /\
  gateway_reference_place_value(Clight.globalenv prog)
    (Returnstate returned(module_outcome_add_cont parameters continuation)after)
    (gateway_reference_global _host_outcome_class)class /\
  Mem.load Mptr after symbol 0=Some class /\native next symbol /\
  gateway_rooted(python next)(objects next)class /\attached after next /\
  (exists status,returned=Vint status /\(status=Int.zero->normal after next)) /\io observed=None.
Proof.
  intros FORMED FIT OWNED NORMAL MODULE NAME SYMBOL PRIVATE GLOBAL STEP.
  assert(OPERATION:gateway_type_operation backend gateway_module_add_object_ref[module;name;class]
    before world returned after next observed).
  { exists gateway_module_reference_add_definition;split;[reflexivity|].
    inversion STEP;subst;cbn[gateway_runtime_operation gateway_module_reference_add_definition];eassumption. }
  destruct(gateway_module_publication_reference_pool backend python objects types allocator instances leases normal attached
    io native stable runtime references(Clight.globalenv prog)before world module name name_bytes class symbol returned after
    next observed position ledger retired ticket FORMED FIT OWNED NORMAL MODULE NAME SYMBOL PRIVATE GLOBAL OPERATION)
    as[WELL[COUNTS[SAME_OWNER[BINDING[LOAD[NATIVE[CLASS[ATTACHED[STATUS[QUIET POOL]]]]]]]]]].
  split.
  - econstructor;[exact STEP|constructor].
  - split;[exact WELL|]. split;[exact COUNTS|]. split.
    + eapply gateway_reference_global_binding;eassumption.
    + exact(conj LOAD(conj NATIVE(conj CLASS(conj ATTACHED(conj STATUS QUIET))))).
Qed.
