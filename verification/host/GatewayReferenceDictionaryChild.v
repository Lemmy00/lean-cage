(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Real key/duplicate guards precede the dictionary's second recursive value call. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayValueEntry GatewayValueExpressions GatewayContainerLoopSource
  GatewayContainerArraySource GatewayContainerDictionarySource GatewayObjectAddresses GatewaySourceDynamic GatewaySourcePaths
  GatewayFramedRuntime GatewayUnaryExpressions GatewayFailurePaths GatewayValueGuards GatewayValueReturns
  GatewaySourceBoundCalls GatewaySourceSegmentAutomation GatewaySourceCuts.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_dictionary_key_source_path {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) slots parameters key key_offset memory symbol definition unicode :
  gateway_ambient_closed backend property ->
  (forall memory world, property memory world -> Mem.weak_valid_pointer memory key (Ptrofs.unsigned key_offset) = true) ->
  (forall memory world, property memory world -> Mem.loadv Mint64 memory (Vptr (gateway_value_tag_slot slots) Ptrofs.zero) =
    Some (Vlong (Int64.repr 8))) ->
  Genv.find_symbol ge _PyObject_IsInstance = Some symbol -> Genv.find_funct_ptr ge symbol = Some definition ->
  Genv.find_symbol ge _PyUnicode_Type = Some unicode ->
  type_of_fundef definition = Tfunction [tptr (Tstruct __object noattr); tptr (Tstruct __object noattr)] tint cc_default ->
  exists called_parameters,
    gateway_source_path backend ge definition [Vptr key key_offset; Vptr unicode Ptrofs.zero]
      (gateway_dictionary_key_cont slots called_parameters) property
      (Returnstate (Vptr key key_offset) (gateway_container_first_cont slots parameters) memory) property /\
    called_parameters ! _first = Some (Vptr key key_offset) /\
    called_parameters ! _container = parameters ! _container /\
    called_parameters ! _stream = parameters ! _stream /\
    called_parameters ! _depth = parameters ! _depth /\
    called_parameters ! _index__1 = parameters ! _index__1.
Proof.
  intros CLOSED POINTER TAG SYMBOL FUNCTION UNICODE TYPE; eexists; split.
  - gateway_bound_source_call CLOSED
      ltac:(fun _ => first [apply gateway_value_tag_expression; eapply TAG; eassumption |
        eapply gateway_unary_expression_value with (value := Vptr key key_offset) (result := Vint Int.zero);
          [gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity) |
           match goal with GOOD : property ?current ?world |- _ =>
             change (option_map (fun flag => Val.of_bool (negb flag))
               (if Mem.weak_valid_pointer current key (Ptrofs.unsigned key_offset) then Some true else None) = Some (Vint Int.zero));
             rewrite (POINTER current world GOOD); reflexivity end]]) ltac:(fun _ => reflexivity).
    eapply gateway_source_same with (target := Callstate definition [Vptr key key_offset; Vptr unicode Ptrofs.zero]
      (gateway_dictionary_key_cont slots _) memory).
    + exact CLOSED.
    + cbn; tauto.
    + intros; eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero).
      * reflexivity.
      * apply old_expression_value; eapply value_function; [reflexivity |exact SYMBOL |reflexivity].
      * apply cons_argument_values with (v := Vptr key key_offset).
        -- gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
        -- reflexivity.
        -- apply cons_argument_values with (v := Vptr unicode Ptrofs.zero).
           ++ eapply cast_expression_value; [eapply gateway_global_address_expression; [reflexivity |exact UNICODE] |reflexivity].
           ++ reflexivity.
           ++ apply no_argument_values.
      * change (Genv.find_funct_ptr ge symbol = Some definition); exact FUNCTION.
      * exact TYPE.
    + apply gateway_source_reached; auto.
  - unfold set_opttemp; repeat split; repeat rewrite PTree.gso by discriminate;
      first [apply PTree.gss |reflexivity].
Qed.

Theorem gateway_dictionary_second_source_path {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) slots parameters stream depth status memory symbol :
  gateway_ambient_closed backend property -> parameters ! _stream = Some stream ->
  parameters ! _depth = Some (Vint depth) -> gateway_object_pointer_value stream ->
  parameters ! _string_key = Some (Vint status) -> 0 < Int.signed status ->
  Genv.find_symbol ge _host_value = Some symbol -> Genv.find_funct_ptr ge symbol = Some (Internal f_host_value) ->
  exists called_parameters,
    gateway_source_path backend ge (Internal f_host_value) [stream; Vint (Int.sub depth Int.one)]
      (gateway_dictionary_second_cont slots called_parameters) property
      (Returnstate (Vint Int.zero) (gateway_dictionary_contains_cont slots parameters) memory) property /\
    called_parameters ! _duplicate = Some (Vint Int.zero) /\
    called_parameters ! _container = parameters ! _container /\ called_parameters ! _first = parameters ! _first /\
    called_parameters ! _stream = parameters ! _stream /\ called_parameters ! _depth = parameters ! _depth /\
    called_parameters ! _index__1 = parameters ! _index__1.
Proof.
  intros CLOSED STREAM DEPTH POINTER STRING_KEY POSITIVE SYMBOL FUNCTION.
  assert (POS : Int.lt (Int.repr 0) status = true).
  { change (Int.lt Int.zero status = true); unfold Int.lt; rewrite Int.signed_zero; destruct zlt; [reflexivity |lia]. }
  eexists; split.
  - gateway_bound_source_call CLOSED ltac:(fun _ => fail)
      ltac:(fun _ => cbn -[Int.lt]; rewrite ?POS; reflexivity).
    eapply gateway_source_same with (target := Callstate (Internal f_host_value) [stream; Vint (Int.sub depth Int.one)]
      (gateway_dictionary_second_cont slots _) memory).
    + exact CLOSED.
    + cbn; tauto.
    + intros; eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero).
      * reflexivity.
      * apply old_expression_value; eapply value_function; [reflexivity |exact SYMBOL |reflexivity].
      * apply cons_argument_values with (v := stream).
        -- gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
        -- destruct POINTER as [NULL |[object [offset SAME]]]; subst stream; reflexivity.
        -- apply cons_argument_values with (v := Vint (Int.sub depth Int.one)).
           ++ gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
           ++ reflexivity.
           ++ apply no_argument_values.
      * change (Genv.find_funct_ptr ge symbol = Some (Internal f_host_value)); exact FUNCTION.
      * reflexivity.
    + apply gateway_source_reached; auto.
  - unfold set_opttemp; repeat split; repeat rewrite PTree.gso by discriminate;
      first [apply PTree.gss |reflexivity].
Qed.

Theorem gateway_dictionary_nonpositive_key_denied {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    slots parameters status memory :
  Int.signed status <= 0 ->
  gateway_failure_when backend ge (fun _ _ => True)
    (Returnstate (Vint status) (gateway_dictionary_key_cont slots parameters) memory).
Proof.
  intro NONPOSITIVE.
  assert (POS : Int.lt (Int.repr 0) status = false).
  { change (Int.lt Int.zero status = false); unfold Int.lt; rewrite Int.signed_zero; destruct zlt; [lia |reflexivity]. }
  assert (CLOSED : gateway_ambient_closed backend (fun _ _ => True))
    by (unfold gateway_ambient_closed; intros; exact I).
  gateway_bound_source_failure CLOSED
    ltac:(fun _ => apply old_expression_value; eapply value_unary; [constructor |reflexivity])
    ltac:(fun _ => cbn -[Int.lt]; rewrite ?POS; reflexivity) gateway_value_pointer_return.
Qed.

Theorem gateway_dictionary_contains_source_path {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    (property : mem -> World -> Prop) slots parameters parent parent_offset key key_offset status memory symbol definition :
  gateway_ambient_closed backend property -> parameters ! _container = Some (Vptr parent parent_offset) ->
  parameters ! _first = Some (Vptr key key_offset) -> 0 < Int.signed status ->
  Genv.find_symbol ge _PyDict_Contains = Some symbol -> Genv.find_funct_ptr ge symbol = Some definition ->
  type_of_fundef definition = Tfunction [tptr (Tstruct __object noattr); tptr (Tstruct __object noattr)] tint cc_default ->
  exists called_parameters,
    gateway_source_path backend ge definition [Vptr parent parent_offset; Vptr key key_offset]
      (gateway_dictionary_contains_cont slots called_parameters) property
      (Returnstate (Vint status) (gateway_dictionary_key_cont slots parameters) memory) property /\
    called_parameters ! _string_key = Some (Vint status) /\
    called_parameters ! _container = parameters ! _container /\ called_parameters ! _first = parameters ! _first /\
    called_parameters ! _stream = parameters ! _stream /\ called_parameters ! _depth = parameters ! _depth /\
    called_parameters ! _index__1 = parameters ! _index__1.
Proof.
  intros CLOSED PARENT KEY POSITIVE SYMBOL FUNCTION TYPE.
  assert (POS : Int.lt Int.zero status = true).
  { unfold Int.lt; rewrite Int.signed_zero; destruct zlt; [reflexivity |lia]. }
  change (Int.lt (Int.repr 0) status = true) in POS.
  eexists; split.
  - gateway_bound_source_call CLOSED ltac:(fun _ => fail)
      ltac:(fun _ => cbn -[Int.lt]; rewrite ?POS; reflexivity).
    eapply gateway_source_same with (target := Callstate definition [Vptr parent parent_offset; Vptr key key_offset]
      (gateway_dictionary_contains_cont slots _) memory).
    + exact CLOSED.
    + cbn; tauto.
    + intros; eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero).
      * reflexivity.
      * apply old_expression_value; eapply value_function; [reflexivity |exact SYMBOL |reflexivity].
      * apply cons_argument_values with (v := Vptr parent parent_offset).
        -- gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
        -- reflexivity.
        -- apply cons_argument_values with (v := Vptr key key_offset).
           ++ gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity).
           ++ reflexivity.
           ++ apply no_argument_values.
      * change (Genv.find_funct_ptr ge symbol = Some definition); exact FUNCTION.
      * exact TYPE.
    + apply gateway_source_reached; auto.
  - unfold set_opttemp; repeat split; repeat rewrite PTree.gso by discriminate;
      first [apply PTree.gss |reflexivity].
Qed.

Theorem gateway_dictionary_key_success_positive {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    slots parameters status before world events value after next :
  gateway_steps backend ge
    (gateway_live (Returnstate (Vint status) (gateway_dictionary_key_cont slots parameters) before) world) events
    (gateway_live (Returnstate value Kstop after) next) -> value <> Vnullptr -> 0 < Int.signed status.
Proof.
  intros RUN NONNULL; destruct (zle (Int.signed status) 0) as [NONPOSITIVE |POSITIVE]; [|lia].
  exfalso; apply NONNULL.
  exact (gateway_dictionary_nonpositive_key_denied backend ge slots parameters status before NONPOSITIVE
    before world events value after next I RUN).
Qed.

Theorem gateway_dictionary_duplicate_denied {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    slots parameters key_status duplicate memory :
  parameters ! _string_key = Some (Vint key_status) -> 0 < Int.signed key_status -> duplicate <> Int.zero ->
  gateway_failure_when backend ge (fun _ _ => True)
    (Returnstate (Vint duplicate) (gateway_dictionary_contains_cont slots parameters) memory).
Proof.
  intros STRING_KEY POSITIVE NONZERO.
  assert (POS : Int.lt (Int.repr 0) key_status = true).
  { change (Int.lt Int.zero key_status = true); unfold Int.lt; rewrite Int.signed_zero; destruct zlt; [reflexivity |lia]. }
  assert (ZERO : Int.eq duplicate Int.zero = false) by (apply Int.eq_false; exact NONZERO).
  pose proof ZERO as ZERO_REPR.
  change (Int.eq duplicate (Int.repr 0) = false) in ZERO_REPR.
  assert (CLOSED : gateway_ambient_closed backend (fun _ _ => True))
    by (unfold gateway_ambient_closed; intros; exact I).
  gateway_bound_source_failure CLOSED ltac:(fun _ => fail)
    ltac:(fun _ => cbn -[Int.lt Int.eq]; rewrite ?POS, ?ZERO, ?ZERO_REPR; reflexivity) gateway_value_pointer_return.
Qed.

Theorem gateway_dictionary_contains_success_zero {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    slots parameters key_status duplicate before world events value after next :
  parameters ! _string_key = Some (Vint key_status) -> 0 < Int.signed key_status ->
  gateway_steps backend ge
    (gateway_live (Returnstate (Vint duplicate) (gateway_dictionary_contains_cont slots parameters) before) world) events
    (gateway_live (Returnstate value Kstop after) next) -> value <> Vnullptr -> duplicate = Int.zero.
Proof.
  intros STRING_KEY POSITIVE RUN NONNULL; destruct (Int.eq_dec duplicate Int.zero) as [ZERO |NONZERO]; [exact ZERO |].
  exfalso; apply NONNULL.
  exact (gateway_dictionary_duplicate_denied backend ge slots parameters key_status duplicate before STRING_KEY POSITIVE NONZERO
    before world events value after next I RUN).
Qed.

Theorem gateway_dictionary_null_second_denied {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    slots parameters memory :
  gateway_failure_when backend ge (fun _ _ => True)
    (Returnstate Vnullptr (gateway_dictionary_second_cont slots parameters) memory).
Proof.
  assert (CLOSED : gateway_ambient_closed backend (fun _ _ => True))
    by (unfold gateway_ambient_closed; intros; exact I).
  gateway_bound_source_failure CLOSED
    ltac:(fun _ => eapply gateway_unary_expression_value with (value := Vnullptr) (result := Vint Int.one);
      [gateway_segment_expression ltac:(fun _ => fail) ltac:(fun _ => reflexivity) | reflexivity])
    ltac:(fun _ => reflexivity) gateway_value_pointer_return.
Qed.
