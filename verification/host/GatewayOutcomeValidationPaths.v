(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual validation loop selects each getter and required type. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayOutcomeConstruction GatewayOutcomeEntry
  GatewayOutcomeValidationSource GatewaySourcePaths GatewaySourceBoundCalls GatewaySourceSegmentAutomation
  GatewayFramedRuntime GatewayObjectAddresses GatewayValueReturns.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_validation_iteration_cont :=
  Kloop1 gateway_outcome_validation_loop_body gateway_outcome_validation_loop_update
    (Kseq gateway_outcome_after_field_validation Kstop).
Definition gateway_validation_fields_tail :=
  match gateway_outcome_validation_loop_body with
  | Ssequence _ (Ssequence _ rest) => rest | _ => Sskip end.
Definition gateway_validation_lookup_cont environment parameters :=
  Kcall (Some _t'3) f_host_outcome_from environment parameters
    (Kseq (Sset _value (Etempvar _t'3 (tptr (Tstruct __object noattr))))
      (Kseq gateway_validation_fields_tail gateway_validation_iteration_cont)).
Definition gateway_validation_name_offset (index : nat) :=
  Ptrofs.add Ptrofs.zero (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_int (Int.repr (Z.of_nat index)))).

Lemma gateway_validation_positive_gt (ge : Clight.genv) memory word :
  0 < Int.signed word ->
  sem_binary_operation ge Ogt (Vint word) tint (Vint Int.zero) tint memory = Some (Vint Int.one).
Proof.
  intro POSITIVE; change (Some (Val.of_bool (Int.lt Int.zero word)) = Some (Vint Int.one)).
  assert (LESS : Int.lt Int.zero word = true).
  { unfold Int.lt; change ((if zlt 0 (Int.signed word) then true else false) = true).
    destruct zlt; [reflexivity |lia]. }
  rewrite LESS; reflexivity.
Qed.

Lemma gateway_validation_name_read (ge : Clight.genv) environment parameters memory table index name :
  parameters ! _index = Some (Vint (Int.repr (Z.of_nat index))) ->
  environment ! _host_outcome_fields = None -> Genv.find_symbol ge _host_outcome_fields = Some table ->
  Mem.loadv Mptr memory (Vptr table (gateway_validation_name_offset index)) = Some (Vptr name Ptrofs.zero) ->
  expression_value ge environment parameters memory
    (Ederef (Ebinop Oadd (Evar _host_outcome_fields (tarray (tptr tschar) 14))
      (Etempvar _index tuint) (tptr (tptr tschar))) (tptr tschar)) (Vptr name Ptrofs.zero).
Proof.
  intros INDEX LOCAL TABLE LOAD; eapply location_read_value.
  - apply pointer_location_value.
    eapply binary_expression_value with (v := Vptr table Ptrofs.zero) (w := Vint (Int.repr (Z.of_nat index))).
    + apply old_expression_value, value_function; assumption || reflexivity.
    + apply old_expression_value, value_temp; exact INDEX.
    + reflexivity.
  - eapply deref_loc_value; [reflexivity |exact LOAD].
Qed.

Ltac gateway_validation_source_call closed loads reduce :=
  lazymatch goal with
  | |- gateway_source_path _ _ _ _ _ _ (State ?function ?body ?continuation ?environment ?parameters ?memory) _ =>
    let statement := eval hnf in body in lazymatch statement with
    | Sloop ?first ?second =>
      eapply gateway_source_same with
        (target := State function first (Kloop1 first second continuation) environment parameters memory);
        [exact closed |cbn; tauto |intros; apply unchanged_store_edge, edge_loop |
         gateway_validation_source_call closed loads reduce]
    | Ssequence ?first ?rest =>
      eapply gateway_source_same with (target := State function first (Kseq rest continuation) environment parameters memory);
        [exact closed |cbn; tauto |intros; apply unchanged_store_edge, edge_seq |
         gateway_validation_source_call closed loads reduce]
    | Sskip => let rest := eval hnf in continuation in lazymatch rest with
      | Kseq ?following ?tail =>
        eapply gateway_source_same with (target := State function following tail environment parameters memory);
          [exact closed |cbn; tauto |intros; apply unchanged_store_edge, edge_skip_seq |
           gateway_validation_source_call closed loads reduce]
      | Kloop1 ?first ?second ?tail =>
        eapply gateway_source_same with (target := State function second (Kloop2 first second tail) environment parameters memory);
          [exact closed |cbn; tauto |intros; apply unchanged_store_edge, edge_skip_loop1 |
           gateway_validation_source_call closed loads reduce]
      | Kloop2 ?first ?second ?tail =>
        eapply gateway_source_same with (target := State function (Sloop first second) tail environment parameters memory);
          [exact closed |cbn; tauto |intros; apply unchanged_store_edge, edge_skip_loop2 |
           gateway_validation_source_call closed loads reduce]
      end
    | Sbreak => let rest := eval hnf in continuation in lazymatch rest with
      | Kseq ?following ?tail =>
        eapply gateway_source_same with (target := State function Sbreak tail environment parameters memory);
          [exact closed |cbn; tauto |intros; apply unchanged_store_edge, edge_break_seq |
           gateway_validation_source_call closed loads reduce]
      | Kloop1 ?first ?second ?tail =>
        eapply gateway_source_same with (target := State function Sskip tail environment parameters memory);
          [exact closed |cbn; tauto |intros; apply unchanged_store_edge, edge_break_loop1 |
           gateway_validation_source_call closed loads reduce]
      end
    | Sset ?identifier ?expression =>
      let value := open_constr:(_ : val) in
      eapply gateway_source_same with (target := State function Sskip continuation environment (PTree.set identifier value parameters) memory);
        [exact closed |cbn; tauto |intros; apply certified_set_edge; gateway_segment_expression loads reduce |
         gateway_validation_source_call closed loads reduce]
    | Sifthenelse ?expression ?yes ?no =>
      let flag := open_constr:(_ : bool) in
      eapply gateway_source_same with (target := State function (if flag then yes else no) continuation environment parameters memory);
        [exact closed |cbn; tauto |intros; eapply certified_if_edge;
          [gateway_segment_expression loads reduce |reduce ()] |gateway_validation_source_call closed loads reduce]
    | (if ?flag then ?yes else ?no) =>
      let selected := eval vm_compute in flag in lazymatch selected with
      | true => change body with yes; gateway_validation_source_call closed loads reduce
      | false => change body with no; gateway_validation_source_call closed loads reduce end
    | Scall _ _ _ => idtac
    end
  | |- gateway_source_path _ _ _ _ _ _ (Returnstate ?value ?saved ?memory) _ =>
    let actual := eval hnf in saved in lazymatch actual with
    | Kcall ?destination ?function ?environment ?parameters ?continuation =>
      eapply gateway_source_same with
        (target := State function Sskip continuation environment (set_opttemp destination value parameters) memory);
        [exact closed |cbn; tauto |intros; apply unchanged_store_edge, edge_returnstate |
         gateway_validation_source_call closed loads reduce]
    end
  end.

Theorem gateway_validation_iteration_getter {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) environment parameters before word index data data_offset table name symbol definition :
  gateway_ambient_closed backend property ->
  parameters ! _valid = Some (Vint word) -> 0 < Int.signed word -> (index < 14)%nat ->
  parameters ! _index = Some (Vint (Int.repr (Z.of_nat index))) ->
  parameters ! _data = Some (Vptr data data_offset) ->
  environment ! _host_outcome_fields = None -> environment ! _PyDict_GetItemString = None ->
  Genv.find_symbol ge _host_outcome_fields = Some table ->
  (forall memory world, property memory world ->
    Mem.loadv Mptr memory (Vptr table (gateway_validation_name_offset index)) = Some (Vptr name Ptrofs.zero)) ->
  Genv.find_symbol ge _PyDict_GetItemString = Some symbol -> Genv.find_funct_ptr ge symbol = Some definition ->
  type_of_fundef definition = Tfunction [tptr (Tstruct __object noattr); tptr tschar] (tptr (Tstruct __object noattr)) cc_default ->
  exists selected,
    gateway_source_path backend ge definition [Vptr data data_offset; Vptr name Ptrofs.zero]
      (gateway_validation_lookup_cont environment selected) property
      (State f_host_outcome_from gateway_outcome_validation_loop_body gateway_validation_iteration_cont environment parameters before) property /\
    selected ! _index = parameters ! _index /\ selected ! _data = parameters ! _data /\
    selected ! _t'35 = Some (Vptr name Ptrofs.zero).
Proof.
  intros CLOSED VALID POSITIVE BOUND INDEX DATA TABLE_LOCAL LOCAL TABLE LOAD SYMBOL FUNCTION TYPE.
  assert (COMPARE : forall memory, sem_binary_operation ge Olt (Vint (Int.repr (Z.of_nat index))) tuint
    (Vint (Int.repr 14)) tint memory = Some (Vint Int.one)).
  { intro memory; assert (RANGE : 0 <= Z.of_nat index <= Int.max_unsigned) by (unfold Int.max_unsigned, Int.modulus, Int.wordsize; cbn; lia).
    change (Some (Val.of_bool (Int.ltu (Int.repr (Z.of_nat index)) (Int.repr 14))) = Some (Vint Int.one)).
    unfold Int.ltu; rewrite !Int.unsigned_repr by (unfold Int.max_unsigned, Int.modulus, Int.wordsize; cbn; lia).
    destruct zlt; [reflexivity |lia]. }
  eexists; split.
  - gateway_validation_source_call CLOSED
      ltac:(fun _ => eapply gateway_validation_name_read;
        [repeat rewrite PTree.gso by discriminate; exact INDEX |exact TABLE_LOCAL |exact TABLE |eapply LOAD; eassumption])
      ltac:(fun _ => first [eapply gateway_validation_positive_gt; exact POSITIVE |apply COMPARE |reflexivity]).
    eapply gateway_source_same with (target := Callstate definition [Vptr data data_offset; Vptr name Ptrofs.zero]
      (gateway_validation_lookup_cont environment _) before).
    + exact CLOSED.
    + cbn; tauto.
    + intros; eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero).
      * reflexivity.
      * apply old_expression_value, value_function; [exact LOCAL |exact SYMBOL |reflexivity].
      * apply cons_argument_values with (v := Vptr data data_offset).
        -- gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
        -- reflexivity.
        -- apply cons_argument_values with (v := Vptr name Ptrofs.zero).
           ++ gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
           ++ reflexivity.
           ++ apply no_argument_values.
      * change (Genv.find_funct_ptr ge symbol = Some definition); exact FUNCTION.
      * exact TYPE.
    + apply gateway_source_reached; auto.
  - repeat split; repeat rewrite PTree.gso by discriminate; first [reflexivity |apply PTree.gss].
Qed.

Definition gateway_validation_type_name (index : nat) : ident :=
  if (Nat.eqb index 4 || Nat.eqb index 10)%bool then _PyDict_Type else
  if Nat.eqb index 5 then _PyLong_Type else
  if (Nat.eqb index 8 || Nat.eqb index 9)%bool then _PyBytes_Type else _PyUnicode_Type.
Definition gateway_validation_optional (index : nat) : int :=
  if (Nat.eqb index 4 || Nat.eqb index 7 || Nat.eqb index 11 || Nat.eqb index 13)%bool then Int.one else Int.zero.

Theorem gateway_validation_lookup_type {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) environment parameters before index value dictionary integer bytes unicode symbol :
  gateway_ambient_closed backend property -> (index < 14)%nat -> gateway_object_pointer_value value ->
  parameters ! _index = Some (Vint (Int.repr (Z.of_nat index))) ->
  (forall identifier, In identifier [_host_has_type; _PyDict_Type; _PyLong_Type; _PyBytes_Type; _PyUnicode_Type] ->
    environment ! identifier = None) ->
  Genv.find_symbol ge _host_has_type = Some symbol -> Genv.find_funct_ptr ge symbol = Some (Internal f_host_has_type) ->
  Genv.find_symbol ge _PyDict_Type = Some dictionary -> Genv.find_symbol ge _PyLong_Type = Some integer ->
  Genv.find_symbol ge _PyBytes_Type = Some bytes -> Genv.find_symbol ge _PyUnicode_Type = Some unicode ->
  let selected_type := if (Nat.eqb index 4 || Nat.eqb index 10)%bool then dictionary else
    if Nat.eqb index 5 then integer else if (Nat.eqb index 8 || Nat.eqb index 9)%bool then bytes else unicode in
  exists selected,
    gateway_source_path backend ge (Internal f_host_has_type)
      [value; Vptr selected_type Ptrofs.zero; Vint (gateway_validation_optional index)]
      (gateway_outcome_field_type_cont environment selected) property
      (Returnstate value (gateway_validation_lookup_cont environment parameters) before) property /\
    selected ! _index = parameters ! _index /\ selected ! _data = parameters ! _data /\ selected ! _value = Some value.
Proof.
  intros CLOSED BOUND POINTER INDEX LOCAL SYMBOL FUNCTION DICTIONARY INTEGER BYTES UNICODE.
  assert (CAST : forall memory, sem_cast value (tptr (Tstruct __object noattr))
    (tptr (Tstruct __object noattr)) memory = Some value).
  { intro memory; destruct POINTER as [NULL |[object [offset SAME]]]; subst value; reflexivity. }
  cbn zeta.
  let discharge := ltac:(
    cbn [Nat.eqb gateway_validation_optional]; eexists; split;
    [gateway_validation_source_call CLOSED
      ltac:(fun _ => eapply gateway_global_address_expression;
        [apply LOCAL; cbn; tauto |first [exact DICTIONARY |exact INTEGER |exact BYTES |exact UNICODE]])
      ltac:(fun _ => reflexivity);
     eapply gateway_source_same with (target := Callstate (Internal f_host_has_type) _
       (gateway_outcome_field_type_cont environment _) before);
     [exact CLOSED |cbn; tauto |
      intros; eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero);
      [reflexivity |apply old_expression_value, value_function;
        [apply LOCAL; cbn; tauto |exact SYMBOL |reflexivity] |
       apply cons_argument_values with (v := value);
       [gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity) |
        apply CAST |
        eapply cons_argument_values;
        [gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity) |reflexivity |
         eapply cons_argument_values;
         [gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity) |reflexivity |apply no_argument_values]]] |
       change (Genv.find_funct_ptr ge symbol = Some (Internal f_host_has_type)); exact FUNCTION |reflexivity] |
      apply gateway_source_reached; auto] |
     repeat split; unfold set_opttemp; repeat rewrite PTree.gso by discriminate; first [reflexivity |apply PTree.gss]]) in
  do 14 (destruct index as [|index]; [discharge |]); lia.
Qed.
