(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The class reference moves through the actual temporary and global store. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayModuleSource
  GatewayModuleClass GatewayModuleRegions GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting
  GatewayReferenceExecution.
Import ListNotations.

Definition gateway_module_reference_store_select {World Event}:gateway_reference_selector World Event:=
  fun first event last status=>
  match event,first with
  |gateway_source _,gateway_live(Returnstate _ (Kcall(Some identifier)_ _ _ rest)_)_=>
    gateway_reference_move(gateway_reference_result(S(gateway_reference_depth rest)))
      (gateway_reference_temporary(gateway_reference_depth rest)identifier)
  |gateway_source _,gateway_live(State _ (Sassign(Evar global _)(Etempvar identifier _))continuation _ _ _)_=>
    gateway_reference_move(gateway_reference_temporary(gateway_reference_depth continuation)identifier)
      (gateway_reference_global global)
  |gateway_source _,gateway_live(State _ Sskip _ _ _ _)_=>gateway_reference_keep
  |gateway_ambient,_|gateway_blocked,_|gateway_lost,_=>gateway_reference_keep
  |_,_=>gateway_reference_unclassified
  end.

Theorem gateway_actual_module_reference_store {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python heap before world temporaries continuation class symbol ledger ticket:
  gateway_objects_ready python heap before->gateway_native_private python symbol->
  gateway_module_descriptor_regions ge before->Genv.find_symbol ge _host_outcome_class=Some symbol->
  Mem.valid_access before Mptr symbol 0 Writable->(exists object offset,class=Vptr object offset)->
  gateway_reference_ledger_well_formed ledger->gateway_reference_counts_fit ledger python->
  gateway_reference_owns ledger(gateway_reference_result(S(gateway_reference_depth continuation)))ticket class->
  gateway_reference_take(gateway_reference_temporary(gateway_reference_depth continuation)_t'11)
    (gateway_reference_entries ledger)=None->
  gateway_reference_take(gateway_reference_global _host_outcome_class)(gateway_reference_entries ledger)=None->
  exists after final,
    gateway_reference_execution backend ge gateway_module_reference_store_select
      (gateway_live(Returnstate class(module_outcome_cont temporaries continuation)before)world)
      (gateway_reference_valid ledger)(repeat(gateway_source E0)4)
      (gateway_live(State f_host_initialize module_outcome_rest continuation empty_env
        (PTree.set _t'11 class temporaries)after)world)(gateway_reference_valid final) /\
    gateway_reference_ledger_well_formed final /\gateway_reference_counts_fit final python /\
    gateway_reference_owns final(gateway_reference_global _host_outcome_class)ticket class /\
    gateway_reference_place_value ge(State f_host_initialize module_outcome_rest continuation empty_env
      (PTree.set _t'11 class temporaries)after)(gateway_reference_global _host_outcome_class)class /\
    Mem.load Mptr after symbol 0=Some class /\gateway_objects_ready python heap after /\
    gateway_module_descriptor_regions ge after /\
    (forall pointer,gateway_reference_count final pointer=gateway_reference_count ledger pointer).
Proof.
  intros READY PRIVATE REGIONS SYMBOL ACCESS POINTER FORMED FIT OWNED TEMP_FREE GLOBAL_FREE.
  destruct(gateway_actual_module_class_store ge python heap before temporaries continuation class symbol
    READY PRIVATE REGIONS SYMBOL ACCESS POINTER)as[after[PATH[STORE[LOAD[AFTER_READY AFTER_REGIONS]]]]].
  destruct(gateway_reference_move_selected ledger(gateway_reference_result(S(gateway_reference_depth continuation)))
    (gateway_reference_temporary(gateway_reference_depth continuation)_t'11)ticket class FORMED OWNED)
    as[temporary_ledger[TEMP_MOVE[TEMP_FORMED[TEMP_OWNED[TEMP_RETAINED TEMP_COUNTS]]]]].
  - intros entry MEMBER OWNER;exfalso.
    apply(proj1(gateway_reference_take_none _ _)TEMP_FREE entry MEMBER);exact OWNER.
  - assert(STILL_GLOBAL_FREE:gateway_reference_take(gateway_reference_global _host_outcome_class)
      (gateway_reference_entries temporary_ledger)=None).
    { eapply(gateway_reference_move_keeps_vacant ledger
        (gateway_reference_result(S(gateway_reference_depth continuation)))
        (gateway_reference_temporary(gateway_reference_depth continuation)_t'11)
        (gateway_reference_global _host_outcome_class)temporary_ledger);
        [exact GLOBAL_FREE|discriminate|exact TEMP_MOVE]. }
    destruct(gateway_reference_move_selected temporary_ledger
      (gateway_reference_temporary(gateway_reference_depth continuation)_t'11)
      (gateway_reference_global _host_outcome_class)ticket class TEMP_FORMED TEMP_OWNED)
      as[final[GLOBAL_MOVE[FINAL_FORMED[FINAL_OWNED[FINAL_RETAINED FINAL_COUNTS]]]]].
    + intros entry MEMBER OWNER;exfalso.
      apply(proj1(gateway_reference_take_none _ _)STILL_GLOBAL_FREE entry MEMBER);exact OWNER.
    + exists after,final;split.
      * econstructor.
        -- apply gateway_internal;[exact I|apply step_returnstate].
        -- change(gateway_reference_execution backend ge gateway_module_reference_store_select
             (gateway_live(State f_host_initialize Sskip
               (Kseq module_outcome_store(Kseq module_outcome_rest continuation))empty_env
               (PTree.set _t'11 class temporaries)before)world)
             (gateway_reference_apply(gateway_reference_move
               (gateway_reference_result(S(gateway_reference_depth continuation)))
               (gateway_reference_temporary(gateway_reference_depth continuation)_t'11))
               (gateway_reference_valid ledger))
             (repeat(gateway_source E0)3)
             (gateway_live(State f_host_initialize module_outcome_rest continuation empty_env
               (PTree.set _t'11 class temporaries)after)world)(gateway_reference_valid final)).
           rewrite TEMP_MOVE;econstructor.
           ++ apply gateway_internal;[exact I|apply step_skip_seq].
           ++ change(gateway_reference_execution backend ge gateway_module_reference_store_select
                (gateway_live(State f_host_initialize module_outcome_store(Kseq module_outcome_rest continuation)
                  empty_env(PTree.set _t'11 class temporaries)before)world)
                (gateway_reference_valid temporary_ledger)(repeat(gateway_source E0)2)
                (gateway_live(State f_host_initialize module_outcome_rest continuation empty_env
                  (PTree.set _t'11 class temporaries)after)world)(gateway_reference_valid final)).
              econstructor.
              ** destruct(actual_module_outcome_store_edge ge(PTree.set _t'11 class temporaries)
                   (Kseq module_outcome_rest continuation)before after class symbol SYMBOL(PTree.gss _ _ _)
                   POINTER STORE)as[INTERNAL[STEP UNIQUE]].
                 eapply gateway_internal;[exact INTERNAL|exact STEP].
              ** change(gateway_reference_execution backend ge gateway_module_reference_store_select
                   (gateway_live(State f_host_initialize Sskip(Kseq module_outcome_rest continuation)empty_env
                     (PTree.set _t'11 class temporaries)after)world)
                   (gateway_reference_apply(gateway_reference_move
                     (gateway_reference_temporary(gateway_reference_depth continuation)_t'11)
                     (gateway_reference_global _host_outcome_class))(gateway_reference_valid temporary_ledger))
                   [gateway_source E0]
                   (gateway_live(State f_host_initialize module_outcome_rest continuation empty_env
                     (PTree.set _t'11 class temporaries)after)world)(gateway_reference_valid final)).
                 rewrite GLOBAL_MOVE;econstructor.
                 --- apply gateway_internal;[exact I|apply step_skip_seq].
                 --- constructor.
      * split;[exact FINAL_FORMED|]. split.
        -- intro pointer;rewrite FINAL_COUNTS,TEMP_COUNTS;apply FIT.
        -- split;[exact FINAL_OWNED|]. split.
           ++ eapply gateway_reference_global_binding;eassumption.
           ++ split;[exact LOAD|]. split;[exact AFTER_READY|]. split;[exact AFTER_REGIONS|].
              intro pointer;rewrite FINAL_COUNTS,TEMP_COUNTS;reflexivity.
Qed.
