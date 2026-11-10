(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Capture the same returned reference while retaining
  archived aliases. *)
From Stdlib Require Import List Lia.
From compcert Require Import Maps Values Memory Events Clight.
Require Import ClightSteps StoreSteps.
From HostGateway Require Import GatewayMachine GatewayRuntimeCuts GatewayFramedRuntime
  GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceHistory GatewayReferenceAbandon
  GatewayReferenceHistoryMove GatewayReferenceGlobalStore.
Import ListNotations.

Lemma gateway_history_ambient_execution {World Event}(backend:gateway_backend World Event)ge
    position first events last ledger retired:
  gateway_steps backend ge first events last ->Forall(fun event=>event=gateway_ambient)events ->
  gateway_history_execution backend ge gateway_history_global_store_select position first
    {|gateway_history_active:=gateway_reference_valid ledger;gateway_history_abandoned:=retired|}events last
    {|gateway_history_active:=gateway_reference_valid ledger;gateway_history_abandoned:=retired|}.
Proof.
  intro RUN;revert position;induction RUN;intros position AMBIENT;[constructor|].
  inversion AMBIENT;subst observed;econstructor;[exact H|].
  cbn[gateway_history_global_store_select gateway_history_apply gateway_reference_apply];apply IHRUN;assumption.
Qed.

Theorem gateway_actual_history_return_capture {World Event}(backend:gateway_backend World Event)ge
    (property:mem->World->Prop)function identifier environment parameters continuation object offset
    before world events value after next position ledger retired ticket:
  gateway_ambient_closed backend property ->property before world ->
  gateway_history_well_formed position ledger retired ->
  gateway_reference_owns ledger(gateway_reference_result(S(gateway_reference_depth continuation)))ticket(Vptr object offset) ->
  gateway_reference_take(gateway_reference_temporary(gateway_reference_depth continuation)identifier)
    (gateway_reference_entries ledger)=None ->
  gateway_steps backend ge
    (gateway_live(Returnstate(Vptr object offset)(Kcall(Some identifier)function environment parameters continuation)before)world)
    events(gateway_live(Returnstate value Kstop after)next) ->
  exists moved prefix suffix memory current,
    events=prefix++suffix /\property memory current /\
    gateway_history_execution backend ge gateway_history_global_store_select position
      (gateway_live(Returnstate(Vptr object offset)(Kcall(Some identifier)function environment parameters continuation)before)world)
      {|gateway_history_active:=gateway_reference_valid ledger;gateway_history_abandoned:=retired|}prefix
      (gateway_live(State function Sskip continuation environment(PTree.set identifier(Vptr object offset)parameters)memory)current)
      {|gateway_history_active:=gateway_reference_valid moved;gateway_history_abandoned:=retired|} /\
    gateway_history_well_formed(position+length prefix)moved retired /\
    gateway_reference_owns moved(gateway_reference_temporary(gateway_reference_depth continuation)identifier)ticket(Vptr object offset) /\
    (forall pointer,gateway_history_total_count moved retired pointer=gateway_history_total_count ledger retired pointer) /\
    gateway_steps backend ge
      (gateway_live(State function Sskip continuation environment(PTree.set identifier(Vptr object offset)parameters)memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros CLOSED INITIAL WELL OWNED VACANT RUN.
  destruct(gateway_uniform_edge_side_cut backend ge property CLOSED
    (Returnstate(Vptr object offset)(Kcall(Some identifier)function environment parameters continuation)before)
    (State function Sskip continuation environment(PTree.set identifier(Vptr object offset)parameters)before)
    before world events value after next ltac:(cbn;tauto)
    ltac:(intros;apply unchanged_store_edge,edge_returnstate)INITIAL RUN)
    as(pending &suffix &memory &current &EVENTS &AMBIENT &PREFIX &GOOD &SUFFIX).
  assert(BEFORE_WELL:gateway_history_well_formed(position+length pending)ledger retired).
  { eapply(gateway_history_well_formed_advance position(position+length pending)ledger retired);[lia|exact WELL]. }
  destruct(gateway_history_move_owned(position+length pending)ledger retired
    (gateway_reference_result(S(gateway_reference_depth continuation)))
    (gateway_reference_temporary(gateway_reference_depth continuation)identifier)ticket(Vptr object offset)
    BEFORE_WELL OWNED VACANT)as(moved &MOVE &MOVED_WELL &MOVED_OWNER &COUNTS &RETAINED).
  exists moved,(pending++[gateway_source E0]),suffix,memory,current.
  split;[rewrite EVENTS;rewrite<-app_assoc;reflexivity|]. split;[exact GOOD|]. split.
  - eapply gateway_history_execution_append with(prefix:=pending);
      [eapply gateway_history_ambient_execution;[exact PREFIX|exact AMBIENT]|].
    econstructor;[apply gateway_internal;[exact I|apply step_returnstate]|].
    change(gateway_history_execution backend ge gateway_history_global_store_select(S(position+length pending))
      (gateway_live(State function Sskip continuation environment(PTree.set identifier(Vptr object offset)parameters)memory)current)
      (gateway_history_apply(position+length pending)
        (if Val.eq(Vptr object offset)Vnullptr then gateway_history_current gateway_reference_keep else
          gateway_history_current(gateway_reference_move(gateway_reference_result(S(gateway_reference_depth continuation)))
            (gateway_reference_temporary(gateway_reference_depth continuation)identifier)))
        {|gateway_history_active:=gateway_reference_valid ledger;gateway_history_abandoned:=retired|})[]
      (gateway_live(State function Sskip continuation environment(PTree.set identifier(Vptr object offset)parameters)memory)current)
      {|gateway_history_active:=gateway_reference_valid moved;gateway_history_abandoned:=retired|}).
    destruct(Val.eq(Vptr object offset)Vnullptr);[discriminate|]. rewrite MOVE;constructor.
  - split;[rewrite length_app;cbn;replace(position+(length pending+1))%nat with(S(position+length pending))by lia;exact MOVED_WELL|].
    exact(conj MOVED_OWNER(conj COUNTS SUFFIX)).
Qed.

Theorem gateway_actual_history_skip_sequence {World Event}(backend:gateway_backend World Event)ge
    (property:mem->World->Prop)function following continuation environment parameters
    before world events value after next position ledger retired:
  gateway_ambient_closed backend property ->property before world ->gateway_history_well_formed position ledger retired ->
  gateway_steps backend ge(gateway_live(State function Sskip(Kseq following continuation)environment parameters before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->
  exists prefix suffix memory current,
    events=prefix++suffix /\property memory current /\
    gateway_history_execution backend ge gateway_history_global_store_select position
      (gateway_live(State function Sskip(Kseq following continuation)environment parameters before)world)
      {|gateway_history_active:=gateway_reference_valid ledger;gateway_history_abandoned:=retired|}prefix
      (gateway_live(State function following continuation environment parameters memory)current)
      {|gateway_history_active:=gateway_reference_valid ledger;gateway_history_abandoned:=retired|} /\
    gateway_history_well_formed(position+length prefix)ledger retired /\
    gateway_steps backend ge(gateway_live(State function following continuation environment parameters memory)current)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros CLOSED INITIAL WELL RUN.
  destruct(gateway_uniform_edge_side_cut backend ge property CLOSED
    (State function Sskip(Kseq following continuation)environment parameters before)
    (State function following continuation environment parameters before)
    before world events value after next ltac:(cbn;tauto)
    ltac:(intros;apply unchanged_store_edge,edge_skip_seq)INITIAL RUN)
    as(pending &suffix &memory &current &EVENTS &AMBIENT &PREFIX &GOOD &SUFFIX).
  exists(pending++[gateway_source E0]),suffix,memory,current.
  split;[rewrite EVENTS;rewrite<-app_assoc;reflexivity|]. split;[exact GOOD|]. split.
  - eapply gateway_history_execution_append with(prefix:=pending);
      [eapply gateway_history_ambient_execution;[exact PREFIX|exact AMBIENT]|].
    econstructor;[apply gateway_internal;[exact I|apply step_skip_seq]|constructor].
  - split;[eapply(gateway_history_well_formed_advance position(position+length(pending++[gateway_source E0]))ledger retired);[lia|exact WELL]|exact SUFFIX].
Qed.
