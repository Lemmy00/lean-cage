(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Recursive child receipts come from the same actual wider loop run. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayValueEntry GatewayValueGuards GatewayValueReturns
  GatewayContainerLoopSource GatewaySourceDynamic GatewaySourcePaths GatewaySourceCuts GatewayFailurePaths
  GatewayFramedRuntime GatewayUnaryExpressions.
Import ListNotations.

Theorem gateway_actual_container_child_failure {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    slots parameters before world events value after next:
  gateway_steps backend ge(gateway_live(Returnstate Vnullptr(gateway_container_first_cont slots parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value=Vnullptr.
Proof.
  intro RUN.
  assert(CLOSED:gateway_ambient_closed backend(fun _ _=>True))by(unfold gateway_ambient_closed;intros;exact I).
  assert(PATH:gateway_failure_when backend ge(fun _ _=>True)
    (Returnstate Vnullptr(gateway_container_first_cont slots parameters)before)).
  { gateway_source_dynamic_failure CLOSED
      ltac:(fun _=>lazymatch goal with
        |-expression_value _ _ _ _ (Eunop _ _ _) _=>
          eapply gateway_unary_expression_value with(value:=Vnullptr)(result:=Vint Int.one);
            [gateway_source_dynamic_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|reflexivity]
        end)ltac:(fun _=>reflexivity)gateway_value_pointer_return. }
  exact(PATH before world events value after next I RUN).
Qed.

Theorem gateway_actual_container_child_cut {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    (property:mem->World->Prop)slots parameters stream depth index size before world events value after next symbol:
  gateway_ambient_closed backend property ->gateway_object_pointer_value stream ->
  parameters!_stream=Some stream ->parameters!_depth=Some(Vint depth) ->parameters!_index__1=Some(Vlong index) ->
  Int64.ltu index size=true ->
  (forall memory world,property memory world ->Mem.loadv Mint64 memory(Vptr(gateway_value_size_slot slots)Ptrofs.zero)=Some(Vlong size)) ->
  Genv.find_symbol ge _host_value=Some symbol ->Genv.find_funct_ptr ge symbol=Some(Internal f_host_value) ->
  property before world ->gateway_steps backend ge
    (gateway_live(State f_host_value gateway_container_loop gateway_container_loop_cont(gateway_value_environment slots)parameters before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value<>Vnullptr ->
  exists called_parameters prefix child_events suffix child_before child_world child child_after child_next,
    events=prefix++child_events++suffix /\Forall(fun event=>event=gateway_source E0 \/event=gateway_ambient)prefix /\
    called_parameters!_stream=Some stream /\called_parameters!_depth=Some(Vint depth) /\
    called_parameters!_container=parameters!_container /\called_parameters!_index__1=Some(Vlong index) /\
    property child_before child_world /\
    gateway_steps backend ge
      (gateway_live(Callstate(Internal f_host_value)[stream;Vint(Int.sub depth Int.one)]Kstop child_before)child_world)child_events
      (gateway_live(Returnstate child Kstop child_after)child_next) /\child<>Vnullptr /\
    gateway_steps backend ge
      (gateway_live(Returnstate child(gateway_container_first_cont slots called_parameters)child_after)child_next)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros CLOSED POINTER STREAM DEPTH INDEX LT LOADED SYMBOL FUNCTION INPUT RUN NONNULL.
  destruct(gateway_container_next_child_path backend ge property slots parameters stream depth index size before symbol
    CLOSED POINTER STREAM DEPTH INDEX LT LOADED SYMBOL FUNCTION)
    as(called_parameters &PATH &CALLED_STREAM &CALLED_DEPTH &CALLED_CONTAINER &CALLED_INDEX).
  destruct(gateway_source_path_cut backend ge _ _ _ _ _ _ PATH before world events value after next INPUT RUN)
    as(prefix &rest &child_before &child_world &EVENTS &QUIET &PREFIX &READY &FROM_CHILD).
  destruct(gateway_return_cut backend ge(Internal f_host_value)[stream;Vint(Int.sub depth Int.one)]
    (gateway_container_first_cont slots called_parameters)child_before child_world rest(Returnstate value Kstop after)next
    ltac:(cbn;exact I)ltac:(cbn;lia)FROM_CHILD)
    as(child_events &suffix &child &child_after &child_next &REST_EVENTS &CHILD_RUN &REST).
  assert(CHILD_NONNULL:child<>Vnullptr).
  { intro NULL;subst child;apply NONNULL;eapply gateway_actual_container_child_failure;exact REST. }
  exists called_parameters,prefix,child_events,suffix,child_before,child_world,child,child_after,child_next.
  split;[rewrite EVENTS,REST_EVENTS;reflexivity|]. split;[exact QUIET|]. split;[exact CALLED_STREAM|].
  split;[exact CALLED_DEPTH|]. split;[exact CALLED_CONTAINER|]. split;[exact CALLED_INDEX|]. split;[exact READY|].
  split;[exact CHILD_RUN|]. split;assumption.
Qed.
