(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The caller's actual captured graph supplies constructor validation inputs. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayValue GatewayObjectThreads
  GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceThreads GatewayReferenceGraphCapture GatewayReferenceContainerScope
  GatewayOutcomeValidationContext GatewayLocalRuntime GatewayNativeRegions.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_validation_context_from_capture {World}
    (python : World -> python_world) (objects : World -> gateway_object_heap) decimal_float ledger held reserved
    captured original ticket wire protected source memory world :
  gateway_objects_ready (python world) (objects world) memory ->
  gateway_reference_scope python objects decimal_float ledger held world ->
  In (gateway_reference_graph_capture ticket original wire captured) held ->
  (forall pointer, (count_occ Val.eq reserved pointer + gateway_reference_count ledger pointer <= python_native_strong (python world) pointer)%nat) ->
  gateway_native_region_owned (fun current object => gateway_native_private (python current) object) protected memory world ->
  Mem.unchanged_on protected source memory ->
  gateway_outcome_validation_context python objects decimal_float ledger held reserved captured original protected source empty_env memory world.
Proof.
  intros READY SCOPE MEMBER BUDGET REGIONS FRAME.
  destruct (gateway_reference_capture_member _ _ _ _ _ _ _ SCOPE MEMBER)
    as [[owner OWNED] [PRIVATE [DESTROY VIEW]]].
  cbn [gateway_reference_graph_capture gateway_held_object gateway_held_view gateway_held_description_holds] in OWNED, PRIVATE, DESTROY, VIEW.
  destruct VIEW as [VALUE [CAPTURED_DESTROY SNAPSHOT]].
  assert (CREDIT : (0 < python_native_strong (python world) original)%nat).
  { pose proof (gateway_reference_owned_count_positive _ _ _ _ OWNED).
    pose proof (proj1 SCOPE original); lia. }
  constructor; [exact READY |apply gateway_native_environment_empty |exact SCOPE |exact BUDGET |exact CREDIT |
    exact PRIVATE |exact DESTROY |exact SNAPSHOT |exact REGIONS |exact FRAME | |].
  all: intros identifier object ty LOOK; rewrite PTree.gempty in LOOK; discriminate.
Qed.
