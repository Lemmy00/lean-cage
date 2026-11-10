(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The successful setup guards precede the real integer loop,
   and the first chunk width is computed from the actual bounded input length. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayNumberWidth GatewayNumberIntegerStructure GatewayNumberIntegerCalls
  GatewayNumberConstruction GatewaySourcePaths GatewaySourceSegments GatewaySourceSegmentAutomation GatewayUnaryExpressions GatewayFramedRuntime.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_number_integer_start {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)parameters current current_offset base base_offset size digits memory:
  gateway_ambient_closed backend property->0<=digits<size->size<=65536->
  (forall memory world,property memory world->Mem.weak_valid_pointer memory current(Ptrofs.unsigned current_offset)=true)->
  (forall memory world,property memory world->Mem.weak_valid_pointer memory base(Ptrofs.unsigned base_offset)=true)->
  parameters!_value__1=Some(Vptr current current_offset)->parameters!_size=Some(Vlong(Int64.repr size))->
  parameters!_digits=Some(Vlong(Int64.repr digits))->
  exists called_parameters,
    gateway_source_segment backend ge property
      (Returnstate(Vptr base base_offset)(gateway_number_base_cont parameters)memory)
      (State f_host_json_number number_integer_loop number_integer_loop_cont empty_env called_parameters memory)property /\
    called_parameters!_index=Some(Vlong(Int64.repr digits)) /\
    called_parameters!_width=Some(Vlong(Int64.repr(gateway_number_first_width(size-digits)))) /\
    called_parameters!_base=Some(Vptr base base_offset) /\
    (forall identifier,identifier<>_base->identifier<>_t'16->identifier<>_t'17->identifier<>_index->identifier<>_width->
      called_parameters!identifier=parameters!identifier).
Proof.
  intros CLOSED DIGITS SIZE CURRENT_VALID BASE_VALID CURRENT LIMIT START.
  pose proof(Z.mod_pos_bound(size-digits)9 ltac:(lia))as MODULO.
  destruct(Z.eq_dec((size-digits)mod 9)0)as[ZERO|NONZERO]eqn:DECIDE;eexists;split.
  all:try solve[
    gateway_segment_dynamic CLOSED
      ltac:(fun _=>first[number_nonnull_expression property current current_offset CURRENT_VALID|
        number_nonnull_expression property base base_offset BASE_VALID|
        eapply gateway_unary_expression_value with(value:=Vlong(Int64.repr((size-digits)mod 9)))
          (result:=Vint(if Z.eq_dec((size-digits)mod 9)0 then Int.one else Int.zero));
          [gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|
           apply gateway_number_zero_width;lia]])
      ltac:(fun _=>first[apply gateway_number_subtract|apply gateway_number_remainder;lia|rewrite DECIDE;reflexivity|reflexivity])].
  all:repeat split;unfold set_opttemp,gateway_number_first_width;rewrite?DECIDE;
    try solve[repeat rewrite PTree.gso by discriminate;apply PTree.gss].
  all:intros identifier A B C D E;repeat rewrite PTree.gso by congruence;reflexivity.
Qed.
