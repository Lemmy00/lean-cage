(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: The same returned reference reaches its actual owning-global store. *)
From Stdlib Require Import List.
From compcert Require Import Maps Values Memory Events Ctypes Clight.
From HostGateway Require Import GatewayMachine GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceHistory
  GatewayReferenceAbandon GatewayReferenceOverwrite GatewayReferenceHistoryMove GatewayReferenceGlobalStore.
Import ListNotations.

Theorem gateway_history_actual_store_sequence {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    function global identifier pointer_type continuation environment parameters object offset before after world
    following position ledger retired ticket:
  gateway_history_well_formed position ledger retired->
  gateway_reference_owns ledger(gateway_reference_result(S(gateway_reference_depth continuation)))ticket(Vptr object offset)->
  gateway_reference_take(gateway_reference_temporary(gateway_reference_depth continuation)identifier)
    (gateway_reference_entries ledger)=None->
  gateway_step backend ge
    (gateway_live(State function(Sassign(Evar global pointer_type)(Etempvar identifier pointer_type))
      (Kseq following continuation)environment(PTree.set identifier(Vptr object offset)parameters)before)world)
    (gateway_source E0)
    (gateway_live(State function Sskip(Kseq following continuation)environment
      (PTree.set identifier(Vptr object offset)parameters)after)world)->
  exists next archived,
    gateway_history_execution backend ge gateway_history_global_store_select position
      (gateway_live(Returnstate(Vptr object offset)
        (Kcall(Some identifier)function environment parameters
          (Kseq(Sassign(Evar global pointer_type)(Etempvar identifier pointer_type))
            (Kseq following continuation)))before)world)
      {|gateway_history_active:=gateway_reference_valid ledger;gateway_history_abandoned:=retired|}
      (repeat(gateway_source E0)4)
      (gateway_live(State function following continuation environment
        (PTree.set identifier(Vptr object offset)parameters)after)world)
      {|gateway_history_active:=gateway_reference_valid next;gateway_history_abandoned:=archived|} /\
    gateway_history_well_formed(S(S(S(S position))))next archived /\
    gateway_reference_owns next(gateway_reference_global global)ticket(Vptr object offset) /\
    (forall value,gateway_history_total_count next archived value=gateway_history_total_count ledger retired value).
Proof.
  intros FORMED OWNED VACANT SOURCE.
  destruct(gateway_history_move_owned position ledger retired
    (gateway_reference_result(S(gateway_reference_depth continuation)))
    (gateway_reference_temporary(gateway_reference_depth continuation)identifier)ticket(Vptr object offset)
    FORMED OWNED VACANT)as[temporary[MOVE[TEMP_WELL[TEMP_OWNED[TEMP_COUNTS TEMP_RETAINED]]]]].
  pose proof(gateway_history_keep_formed _ _ _ TEMP_WELL)as BEFORE_STORE.
  destruct(gateway_history_actual_owned_global_store backend ge function global identifier pointer_type
    (Kseq following continuation)environment(PTree.set identifier(Vptr object offset)parameters)object offset
    before after world(S(S position))temporary retired ticket(PTree.gss _ _ _)BEFORE_STORE TEMP_OWNED SOURCE)
    as[next[archived[STORE[NEXT_WELL[NEXT_OWNED NEXT_COUNTS]]]]].
  exists next,archived;split.
  - econstructor.
    + apply gateway_internal;[exact I|apply step_returnstate].
    + change(gateway_history_execution backend ge gateway_history_global_store_select(S position)
        (gateway_live(State function Sskip
          (Kseq(Sassign(Evar global pointer_type)(Etempvar identifier pointer_type))(Kseq following continuation))
          environment(PTree.set identifier(Vptr object offset)parameters)before)world)
        (gateway_history_apply position
          (if Val.eq(Vptr object offset)Vnullptr then gateway_history_current gateway_reference_keep
           else gateway_history_current(gateway_reference_move
             (gateway_reference_result(S(gateway_reference_depth continuation)))
             (gateway_reference_temporary(gateway_reference_depth continuation)identifier)))
          {|gateway_history_active:=gateway_reference_valid ledger;gateway_history_abandoned:=retired|})
        (repeat(gateway_source E0)3)
        (gateway_live(State function following continuation environment
          (PTree.set identifier(Vptr object offset)parameters)after)world)
        {|gateway_history_active:=gateway_reference_valid next;gateway_history_abandoned:=archived|}).
      destruct(Val.eq(Vptr object offset)Vnullptr);[discriminate|]. rewrite MOVE.
      econstructor.
      * apply gateway_internal;[exact I|apply step_skip_seq].
      * change(gateway_history_execution backend ge gateway_history_global_store_select(S(S position))
          (gateway_live(State function(Sassign(Evar global pointer_type)(Etempvar identifier pointer_type))
            (Kseq following continuation)environment(PTree.set identifier(Vptr object offset)parameters)before)world)
          {|gateway_history_active:=gateway_reference_valid temporary;gateway_history_abandoned:=retired|}
          [gateway_source E0;gateway_source E0]
          (gateway_live(State function following continuation environment
            (PTree.set identifier(Vptr object offset)parameters)after)world)
          {|gateway_history_active:=gateway_reference_valid next;gateway_history_abandoned:=archived|}).
        eapply gateway_history_execution_append with(prefix:=[gateway_source E0])
          (middle:=gateway_live(State function Sskip(Kseq following continuation)environment
            (PTree.set identifier(Vptr object offset)parameters)after)world)
          (intermediate:={|gateway_history_active:=gateway_reference_valid next;gateway_history_abandoned:=archived|}).
        -- exact STORE.
        -- econstructor;[apply gateway_internal;[exact I|apply step_skip_seq]|constructor].
  - split;[apply gateway_history_keep_formed;exact NEXT_WELL|]. split;[exact NEXT_OWNED|].
    intro value;rewrite NEXT_COUNTS,TEMP_COUNTS;reflexivity.
Qed.

Theorem gateway_history_actual_null_store_sequence {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    function global identifier pointer_type continuation environment parameters before after world following
    position ledger retired:
  gateway_history_well_formed position ledger retired->
  gateway_step backend ge
    (gateway_live(State function(Sassign(Evar global pointer_type)(Etempvar identifier pointer_type))
      (Kseq following continuation)environment(PTree.set identifier Vnullptr parameters)before)world)
    (gateway_source E0)
    (gateway_live(State function Sskip(Kseq following continuation)environment
      (PTree.set identifier Vnullptr parameters)after)world)->
  exists next archived,
    gateway_history_execution backend ge gateway_history_global_store_select position
      (gateway_live(Returnstate Vnullptr
        (Kcall(Some identifier)function environment parameters
          (Kseq(Sassign(Evar global pointer_type)(Etempvar identifier pointer_type))
            (Kseq following continuation)))before)world)
      {|gateway_history_active:=gateway_reference_valid ledger;gateway_history_abandoned:=retired|}
      (repeat(gateway_source E0)4)
      (gateway_live(State function following continuation environment
        (PTree.set identifier Vnullptr parameters)after)world)
      {|gateway_history_active:=gateway_reference_valid next;gateway_history_abandoned:=archived|} /\
    gateway_history_well_formed(S(S(S(S position))))next archived /\
    gateway_reference_take(gateway_reference_global global)(gateway_reference_entries next)=None /\
    (forall value,gateway_history_total_count next archived value=gateway_history_total_count ledger retired value).
Proof.
  intros FORMED SOURCE.
  pose proof(gateway_history_keep_formed _ _ _(gateway_history_keep_formed _ _ _ FORMED))as BEFORE_STORE.
  destruct(gateway_history_actual_null_global_store backend ge function global identifier pointer_type
    (Kseq following continuation)environment(PTree.set identifier Vnullptr parameters)
    before after world(S(S position))ledger retired(PTree.gss _ _ _)BEFORE_STORE SOURCE)
    as[next[archived[STORE[NEXT_WELL[VACANT COUNTS]]]]].
  exists next,archived;split.
  - econstructor.
    + apply gateway_internal;[exact I|apply step_returnstate].
    + change(gateway_history_execution backend ge gateway_history_global_store_select(S position)
        (gateway_live(State function Sskip
          (Kseq(Sassign(Evar global pointer_type)(Etempvar identifier pointer_type))(Kseq following continuation))
          environment(PTree.set identifier Vnullptr parameters)before)world)
        (gateway_history_apply position
          (if Val.eq Vnullptr Vnullptr then gateway_history_current gateway_reference_keep
           else gateway_history_current(gateway_reference_move
             (gateway_reference_result(S(gateway_reference_depth continuation)))
             (gateway_reference_temporary(gateway_reference_depth continuation)identifier)))
          {|gateway_history_active:=gateway_reference_valid ledger;gateway_history_abandoned:=retired|})
        (repeat(gateway_source E0)3)
        (gateway_live(State function following continuation environment(PTree.set identifier Vnullptr parameters)after)world)
        {|gateway_history_active:=gateway_reference_valid next;gateway_history_abandoned:=archived|}).
      destruct(Val.eq Vnullptr Vnullptr);[|contradiction].
      change(gateway_history_execution backend ge gateway_history_global_store_select(S position)
        (gateway_live(State function Sskip
          (Kseq(Sassign(Evar global pointer_type)(Etempvar identifier pointer_type))(Kseq following continuation))
          environment(PTree.set identifier Vnullptr parameters)before)world)
        {|gateway_history_active:=gateway_reference_valid ledger;gateway_history_abandoned:=retired|}
        (repeat(gateway_source E0)3)
        (gateway_live(State function following continuation environment(PTree.set identifier Vnullptr parameters)after)world)
        {|gateway_history_active:=gateway_reference_valid next;gateway_history_abandoned:=archived|}).
      econstructor.
      * apply gateway_internal;[exact I|apply step_skip_seq].
      * change(gateway_history_execution backend ge gateway_history_global_store_select(S(S position))
          (gateway_live(State function(Sassign(Evar global pointer_type)(Etempvar identifier pointer_type))
            (Kseq following continuation)environment(PTree.set identifier Vnullptr parameters)before)world)
          {|gateway_history_active:=gateway_reference_valid ledger;gateway_history_abandoned:=retired|}
          [gateway_source E0;gateway_source E0]
          (gateway_live(State function following continuation environment(PTree.set identifier Vnullptr parameters)after)world)
          {|gateway_history_active:=gateway_reference_valid next;gateway_history_abandoned:=archived|}).
        eapply gateway_history_execution_append with(prefix:=[gateway_source E0])
          (middle:=gateway_live(State function Sskip(Kseq following continuation)environment
            (PTree.set identifier Vnullptr parameters)after)world)
          (intermediate:={|gateway_history_active:=gateway_reference_valid next;gateway_history_abandoned:=archived|}).
        -- exact STORE.
        -- econstructor;[apply gateway_internal;[exact I|apply step_skip_seq]|constructor].
  - split;[apply gateway_history_keep_formed;exact NEXT_WELL|]. split;[exact VACANT|exact COUNTS].
Qed.
