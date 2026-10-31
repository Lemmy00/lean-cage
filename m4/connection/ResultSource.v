(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-structures.result: Actual entry, stores, copying and freeing of the generated result constructor. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Globalenvs Errors Ctypes Ctypesdefs Cop Clight.
Require Import Slice Machine ClightSteps StoreSteps WriteAll LocalAccess ScalarMemory ResultLayout.
Import ListNotations.
Open Scope Z_scope.

Definition result_env local := PTree.set ___compound (local,result_type) empty_env.
Definition result_args output ofs kind stage detail entry :=
  [Vptr output (Ptrofs.repr ofs);Vint kind;Vint stage;Vint detail;Vint entry].
Definition result_temps output ofs kind stage detail entry :=
  PTree.set _entry (Vint entry) (PTree.set _detail (Vint detail)
    (PTree.set _stage (Vint stage) (PTree.set _kind (Vint kind)
      (PTree.set __res (Vptr output (Ptrofs.repr ofs)) (create_undef_temps (fn_temps f_result_of)))))).
Definition result_initial output ofs kind stage detail entry k m :=
  Callstate (Internal f_result_of) (result_args output ofs kind stage detail entry) k m.

Theorem result_source_entry : forall m allocated local output ofs kind stage detail entry k,
  Mem.alloc m 0 144 = (allocated,local) ->
  store_edge result_ge (result_initial output ofs kind stage detail entry k m)
    (State f_result_of (fn_body f_result_of) k (result_env local)
      (result_temps output ofs kind stage detail entry) allocated).
Proof.
  intros. apply function_entry_source_edge. constructor.
  - repeat (apply list_norepet_cons; [simpl; intuition discriminate|]); apply list_norepet_nil.
  - repeat (apply list_norepet_cons; [simpl; intuition discriminate|]); apply list_norepet_nil.
  - unfold list_disjoint, var_names; cbn.
    intros x y X Y. destruct X as [X|[X|[X|[X|[X|X]]]]]; destruct Y as [Y|[Y|Y]];
      try contradiction; subst; discriminate.
  - econstructor; [exact H|constructor].
  - reflexivity.
Qed.

Ltac result_location := first
  [eapply local_location_value; unfold result_env; WriteAll.lookup
  | eapply pointer_location_value; result_expression
  | eapply struct_location_value; [result_expression|reflexivity|reflexivity|reflexivity]]
with result_expression := first
  [apply old_expression_value; WriteAll.expression
  | eapply location_read_value; [result_location|first
      [apply deref_loc_copy; reflexivity | apply deref_loc_reference; reflexivity]]
  | eapply binary_expression_value; [result_expression|result_expression|reflexivity]
  | eapply cast_expression_value; [result_expression|reflexivity]].

Lemma result_source_free : forall m after local k le,
  Mem.free m local 0 144 = Some after ->
  store_edge result_ge (State f_result_of (Sreturn None) k (result_env local) le m)
    (Returnstate Vundef (call_cont k) after).
Proof.
  intros. apply local_void_return_edge. unfold result_env, blocks_of_env.
  cbn [PTree.elements PTree.xelements PTree.set PTree.set' PTree.empty empty_env].
  change (match Mem.free m local 0 144 with Some after => Some after | None => None end = Some after).
  rewrite H; reflexivity.
Qed.

Definition result_globals m rb ub run uid :=
  Mem.load Mint64 m rb 0 = Some (Vlong run) /\ Mem.load Mint32 m ub 0 = Some (Vint uid).
Lemma result_globals_after_store : forall m after local rb ub run uid chunk ofs value,
  result_globals m rb ub run uid -> rb <> local -> ub <> local ->
  Mem.store chunk m local ofs value = Some after -> result_globals after rb ub run uid.
Proof.
  intros m after local rb ub run uid chunk ofs value [RUN UID] R U STORE.
  split; erewrite Mem.load_store_other; eauto.
Qed.

Ltac result_route := eapply store_next; [assumption|apply unchanged_store_edge; WriteAll.structural|].
Ltac result_scalar :=
  lazymatch goal with
  | STORES : scalar_stores ?local ?m (?cell :: ?rest) ?last,
    GOOD : ?P ?m, GLOBAL : result_globals ?m ?rb ?ub ?run ?uid,
    STABLE : forall chunk ofs value before after,
      ?P before -> Mem.store chunk before ?local ofs value = Some after -> ?P after |- _ =>
    inversion STORES; subst; clear STORES;
    lazymatch goal with STORE : Mem.store _ m local _ _ = Some ?nextmem |- _ =>
      let PRESERVED := fresh "PRESERVED" in
      pose proof (STABLE _ _ _ _ _ GOOD STORE) as PRESERVED;
      let GLOBAL' := fresh "GLOBALS" in
      assert (GLOBAL' : result_globals nextmem rb ub run uid)
        by (eapply result_globals_after_store; [exact GLOBAL|eassumption|eassumption|exact STORE]);
      eapply store_next; [exact GOOD| |];
      [eapply assignment_source_edge with (after := nextmem);
        [result_location|result_expression|reflexivity|eapply assign_loc_value; [reflexivity|exact STORE]]|]
    end
  end.
Ltac result_global symbol :=
  eapply store_next; [assumption|eapply certified_set_edge|];
  [eapply location_read_value;
    [eapply global_location_value; [unfold result_env; cbn; reflexivity|exact symbol]|
     eapply deref_loc_value; [reflexivity|cbn; match goal with G : result_globals _ _ _ _ _ |- _ =>
       first [exact (proj1 G)|exact (proj2 G)] end]]|].

Lemma result_construction_source_path : forall (P : mem -> Prop)
    m allocated local built copied freed output ofs kind stage detail entry uid run rb ub k,
  Genv.find_symbol result_ge _run_id = Some rb -> Genv.find_symbol result_ge _run_uid = Some ub ->
  rb <> local -> ub <> local ->
  Mem.alloc m 0 144 = (allocated,local) ->
  scalar_stores local allocated (result_cells kind stage detail entry uid run) built ->
  result_globals allocated rb ub run uid ->
  assign_loc result_ge result_type built output (Ptrofs.repr ofs) Full (Vptr local Ptrofs.zero) copied ->
  Mem.free copied local 0 144 = Some freed ->
  P m -> P allocated -> P copied -> P freed ->
  (forall chunk offset value before after,
     P before -> Mem.store chunk before local offset value = Some after -> P after) ->
  store_path result_ge P (result_initial output ofs kind stage detail entry k m) 161
    (Returnstate Vundef (call_cont k) freed).
Proof.
  intros P m allocated local built copied freed output ofs kind stage detail entry uid run rb ub k
    RS US RN UN ALLOC STORES GLOBAL COPY FREE PM PA PC PF STABLE.
  eapply store_next; [exact PM|apply result_source_entry; exact ALLOC|].
  unfold f_result_of; cbn [fn_body]. fold f_result_of. unfold result_temps.
  cbn [result_cells app map seq] in STORES.
  repeat result_route.
  result_scalar.
  repeat result_route. result_scalar.
  repeat result_route. result_scalar.
  repeat result_route. result_scalar.
  repeat result_route. result_scalar.
  repeat result_route. result_scalar.
  repeat result_route. result_global US.
  repeat result_route. result_scalar.
  repeat result_route. result_global RS.
  repeat result_route. result_scalar.
  do 42 (repeat result_route; result_scalar).
  repeat result_route.
  match goal with S : scalar_stores _ _ [] _ |- _ => inversion S; subst; clear S end.
  eapply store_next; [assumption| |].
  - eapply assignment_source_edge; [result_location|result_expression|reflexivity|exact COPY].
  - repeat result_route. eapply store_next; [exact PC|apply result_source_free; exact FREE|].
    apply store_done; exact PF.
Qed.
