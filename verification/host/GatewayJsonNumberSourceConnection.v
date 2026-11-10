(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A real nonnull helper call reaches the constructor for exactly its validated received bytes. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayValue GatewayObjects GatewayBindings
  GatewayJsonNumberSourceLexical GatewayJsonNumberSourceCalls GatewayJsonNumberCallEntry GatewayJsonNumberSourcePhases
  GatewayJsonNumberLexical GatewayJsonNumberLexicalSlices GatewayNumberConstruction GatewayIntegerPrefix
  GatewaySourceSegments GatewaySourcePaths GatewaySourceCuts GatewayFramedRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition json_number_selected_api integer count :=
  if Z.eqb integer count then gateway_api_long_signed else gateway_api_unicode_utf8.
Definition json_number_selected_arguments object count mode_symbol integer :=
  if Z.eqb integer count then [Vlong (Int64.repr 0)]
  else [Vptr object Ptrofs.zero; Vlong (Int64.repr count); Vptr mode_symbol Ptrofs.zero].
Definition json_number_selected_cont integer count parameters :=
  if Z.eqb integer count then gateway_number_zero_cont parameters else gateway_number_decode_cont parameters.

Theorem gateway_actual_json_number_constructor {World Event} (backend : gateway_backend World Event)
    (property : mem -> World -> Prop) object bytes before world events value after next :
  gateway_ambient_closed backend property -> property before world -> Z.of_nat (length bytes) <= 65536 ->
  (forall offset byte, nth_error bytes offset = Some byte -> forall memory world, property memory world ->
    Mem.loadv Mint8signed memory (Vptr object (Ptrofs.repr (Z.of_nat offset))) = Some (Vint (Int.repr (Byte.signed byte)))) ->
  gateway_steps backend (Clight.globalenv prog)
    (gateway_live (Callstate (Internal f_host_json_number)
      [Vptr object Ptrofs.zero; Vlong (Int64.repr (Z.of_nat (length bytes)))] Kstop before) world) events
    (gateway_live (Returnstate value Kstop after) next) -> value <> Vnullptr ->
  exists parts parameters definition mode_symbol prefix suffix called owner,
    json_number_lexical bytes = Some parts /\ gateway_json_number bytes /\
    let integer := gateway_integer_start bytes + Z.of_nat (length (json_parts_integer parts)) in
    0 <= integer <= Z.of_nat (length bytes) /\
    Genv.find_symbol (Clight.globalenv prog) ___stringlit_8 = Some mode_symbol /\
    gateway_object_api_definition (json_number_selected_api integer (Z.of_nat (length bytes))) = Some definition /\
    events = prefix ++ suffix /\
    Forall (fun event => event = gateway_source E0 \/ event = gateway_ambient) prefix /\
    gateway_steps backend (Clight.globalenv prog)
      (gateway_live (Callstate (Internal f_host_json_number)
        [Vptr object Ptrofs.zero; Vlong (Int64.repr (Z.of_nat (length bytes)))] Kstop before) world) prefix
      (gateway_live (Callstate definition (json_number_selected_arguments object (Z.of_nat (length bytes)) mode_symbol integer)
        (json_number_selected_cont integer (Z.of_nat (length bytes)) parameters) called) owner) /\
    property called owner /\
    parameters ! _bytes = Some (Vptr object Ptrofs.zero) /\
    parameters ! _size = Some (Vlong (Int64.repr (Z.of_nat (length bytes)))) /\
    parameters ! _index = Some (Vlong (Int64.repr (Z.of_nat (length bytes)))) /\
    parameters ! _integer_end = Some (Vlong (Int64.repr integer)) /\
    parameters ! _digits = Some (Vlong (Int64.repr (gateway_integer_start bytes))) /\
    parameters ! _negative = Some (Vint (if gateway_integer_negative bytes then Int.one else Int.zero)) /\
    json_parts_sign parts = json_number_sign bytes /\
    gateway_steps backend (Clight.globalenv prog)
      (gateway_live (Callstate definition (json_number_selected_arguments object (Z.of_nat (length bytes)) mode_symbol integer)
        (json_number_selected_cont integer (Z.of_nat (length bytes)) parameters) called) owner) suffix
      (gateway_live (Returnstate value Kstop after) next).
Proof.
  intros CLOSED INPUT BOUND LOADS RUN NONNULL.
  destruct (gateway_actual_json_number_call_entry backend (Clight.globalenv prog) property object
    (Int64.repr (Z.of_nat (length bytes))) before world events value after next CLOSED INPUT RUN)
    as (entry & rest & entered & entry_world & initial & EVENTS0 & QUIET0 & ENTRY & READY0 & BYTES0 & SIZE0 & BODY).
  destruct (gateway_actual_json_number_lexical_source backend (Clight.globalenv prog) property initial object bytes entered
    CLOSED BOUND BYTES0 SIZE0 LOADS) as [DENIED |(parts & parameters & LEXICAL & RESULT)].
  { exfalso; apply NONNULL; exact (DENIED entered entry_world rest value after next READY0 BODY). }
  destruct RESULT as [INTEGER_BOUND [SEGMENT [BYTES [SIZE [POSITION [INTEGER_END [DIGITS [NEGATIVE SIGN]]]]]]]].
  set (integer := gateway_integer_start bytes + Z.of_nat (length (json_parts_integer parts))) in *.
  set (count := Z.of_nat (length bytes)) in *.
  destruct gateway_actual_json_number_api_bindings as
    [(long_definition & LONG_API & [long_symbol [LONG_SYMBOL LONG_FUNCTION]] & LONG_TYPE)
      [(decode_definition & DECODE_API & [decode_symbol [DECODE_SYMBOL DECODE_FUNCTION]] & DECODE_TYPE) [mode_symbol MODE]]].
  assert (VALID : gateway_json_number bytes) by (exact (proj2 (json_number_lexical_sound bytes parts LEXICAL))).
  destruct (Z.eqb integer count) eqn:KIND.
  - unfold json_lexical_constructor in SEGMENT; rewrite KIND in SEGMENT.
    pose proof (gateway_json_number_long_call backend (Clight.globalenv prog) property parameters entered long_symbol long_definition
      CLOSED LONG_SYMBOL LONG_FUNCTION LONG_TYPE) as TAIL.
    pose proof (gateway_segment_then_call backend (Clight.globalenv prog) _ _ _ _ _ _ _ _ SEGMENT TAIL) as PATH.
    destruct (gateway_source_path_cut backend (Clight.globalenv prog) _ _ _ _ _ _ PATH entered entry_world rest value after next READY0 BODY)
      as (lexing & suffix & called & owner & EVENTS1 & QUIET1 & PREFIX & READY & SUFFIX).
    exists parts, parameters, long_definition, mode_symbol, (entry ++ lexing), suffix, called, owner.
    split; [exact LEXICAL |]. split; [exact VALID |]. fold integer; fold count.
    unfold json_number_selected_api, json_number_selected_arguments, json_number_selected_cont; rewrite KIND.
    split; [exact INTEGER_BOUND |]. split; [exact MODE |]. split; [exact LONG_API |]. split.
    + rewrite EVENTS0, EVENTS1, app_assoc; reflexivity.
    + split; [apply Forall_app; split; assumption |]. split.
      * eapply gateway_steps_append; [exact ENTRY |exact PREFIX].
      * split; [exact READY |]. split; [exact BYTES |]. split; [exact SIZE |]. split; [exact POSITION |].
        split; [exact INTEGER_END |]. split; [exact DIGITS |]. split; [exact NEGATIVE |]. split; [exact SIGN |exact SUFFIX].
  - unfold json_lexical_constructor in SEGMENT; rewrite KIND in SEGMENT.
    pose proof (gateway_json_number_decode_call backend (Clight.globalenv prog) property parameters object count entered decode_symbol decode_definition
      mode_symbol CLOSED BYTES SIZE DECODE_SYMBOL DECODE_FUNCTION DECODE_TYPE MODE) as TAIL.
    pose proof (gateway_segment_then_call backend (Clight.globalenv prog) _ _ _ _ _ _ _ _ SEGMENT TAIL) as PATH.
    destruct (gateway_source_path_cut backend (Clight.globalenv prog) _ _ _ _ _ _ PATH entered entry_world rest value after next READY0 BODY)
      as (lexing & suffix & called & owner & EVENTS1 & QUIET1 & PREFIX & READY & SUFFIX).
    exists parts, parameters, decode_definition, mode_symbol, (entry ++ lexing), suffix, called, owner.
    split; [exact LEXICAL |]. split; [exact VALID |]. fold integer; fold count.
    unfold json_number_selected_api, json_number_selected_arguments, json_number_selected_cont; rewrite KIND.
    split; [exact INTEGER_BOUND |]. split; [exact MODE |]. split; [exact DECODE_API |]. split.
    + rewrite EVENTS0, EVENTS1, app_assoc; reflexivity.
    + split; [apply Forall_app; split; assumption |]. split.
      * eapply gateway_steps_append; [exact ENTRY |exact PREFIX].
      * split; [exact READY |]. split; [exact BYTES |]. split; [exact SIZE |]. split; [exact POSITION |].
        split; [exact INTEGER_END |]. split; [exact DIGITS |]. split; [exact NEGATIVE |]. split; [exact SIGN |exact SUFFIX].
Qed.
