(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: One actual source fork supplies the fresh worker's physical objects. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine LibraryMachine ProcessEffects.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffArguments NativeHandoffInput.
From EntryProcess Require Import ProcessMachine.
From EntryNamespace Require Import NamespaceMachine NamespaceStructure NamespacePaths NamespaceMemory
  NamespaceRegion NamespaceTraceRegion NamespaceChildResult NamespaceForkPrefix NamespaceFork NamespaceForkWorld
  NamespaceObjects NamespaceKernel NamespaceWorldTrace NamespaceGuestFlags NamespaceChildImage NamespaceGuestImage
  NamespaceHandles.
Import ListNotations.
Open Scope Z_scope.

Lemma namespace_launch_environment:namespace_ge=handoff_ge.
Proof. reflexivity. Qed.
Local Opaque namespace_ge handoff_ge.

Theorem same_fork_worker_image_objects scope common before_world fork_world first second failure reply le before
    snapshot parent child events target path arguments environment after_world
    input_binding output_binding errors_binding:
  scope_history scope=[] ->
  ChildPrefixResult scope(namespace_fd_events common)
    (Callstate namespace_fork_definition[]
      (child_fork_cont(storage_pair(scope_storage scope))le(scope_continuation scope))before) ->
  namespace_fd_events common=child_signal_log scope first second failure reply ->
  namespace_kernel_steps before_world common fork_world ->
  fork_matches fork_world snapshot ->NativeForkCopy(scope_cell scope)before parent child ->
  namespace_steps namespace_ge(scope_cell scope)
    (live(Returnstate(Vint Int.zero)
      (child_fork_cont(storage_pair(scope_storage scope))le(scope_continuation scope))child))events target ->
  In(namespace_guest_event(entry_image path arguments environment))events ->
  namespace_kernel_steps(namespace_fork_child fork_world snapshot)events after_world ->
  namespace_table before_world(scope_input scope)=Some input_binding ->
  namespace_table before_world(scope_output scope)=Some output_binding ->
  namespace_table before_world(scope_errors scope)=Some errors_binding ->
  exists channel inherited prefix rest guest_le memory,
    fork_world=child_fork_world before_world inherited /\
    events=prefix++rest /\namespace_fd_events prefix=[] /\
    namespace_steps namespace_ge(scope_cell scope)
      (live(Callstate(Internal f_guest)
        [Vint(scope_input scope);Vint(scope_output scope);Vint(scope_errors scope);Vint failure]
        (child_guest_cont(storage_pair(scope_storage scope))guest_le(scope_continuation scope))memory))rest target /\
    handoff_borrowed_input(scope_cell scope)memory(scope_borrowed scope) /\
    namespace_table after_world=
      exec_table(handoff_stdio_table inherited(scope_input scope)(scope_output scope)(scope_errors scope)failure) /\
    Forall(fun fd=>4<=Int.signed fd)[scope_input scope;scope_output scope;scope_errors scope;failure] /\
    namespace_table after_world(scope_input scope)=
      Some{|descriptor_object:=descriptor_object input_binding;descriptor_cloexec:=false|} /\
    namespace_table after_world(scope_output scope)=
      Some{|descriptor_object:=descriptor_object output_binding;descriptor_cloexec:=false|} /\
    namespace_table after_world(scope_errors scope)=
      Some{|descriptor_object:=descriptor_object errors_binding;descriptor_cloexec:=false|} /\
    namespace_table after_world failure=
      Some{|descriptor_object:=release_endpoint channel child_endpoint;descriptor_cloexec:=false|} /\
    (forall descriptor binding,namespace_table after_world descriptor=Some binding ->
      descriptor_object binding<>release_endpoint channel parent_endpoint).
Proof.
  intros HISTORY FRONTIER LOG COMMON MATCH COPY RUN IMAGE KERNEL INPUT OUTPUT ERRORS.
  destruct(source_common_fork_world _ _ _ _ _ _ _ _ _ _ HISTORY FRONTIER LOG COMMON)
    as[channel[inherited[WORLD[DEFAULT[MASK[FIRST[SECOND[MINIMUM[PEER[FAILURE[CLOEXEC[AMBIENT OLD]]]]]]]]]]]].
  rewrite LOG in FRONTIER.
  destruct(actual_child_branch_image_reaches_guest scope first second failure reply le before
    fork_world snapshot parent child events target path arguments environment
    HISTORY FRONTIER MATCH COPY RUN IMAGE)
    as[prefix[rest[guest_le[memory[EVENTS[EMPTY[NOIMAGES[PRE[BORROWED[NONNEGATIVE[GUEST LATER]]]]]]]]]]].
  rewrite EVENTS in KERNEL;destruct(namespace_kernel_steps_split _ _ _ _ KERNEL)as[guest_world[BEFORE_GUEST GUEST_KERNEL]].
  pose proof(child_guest_prefix_preserves_fork_world _ _ _ EMPTY BEFORE_GUEST)as SAME_GUEST;subst guest_world.
  assert(TABLE:namespace_table(namespace_fork_child fork_world snapshot)=inherited).
  { rewrite WORLD;reflexivity. }
  destruct(OLD _ _ INPUT)as[INHERITED_INPUT INPUT_EXCLUDES].
  destruct(OLD _ _ OUTPUT)as[INHERITED_OUTPUT OUTPUT_EXCLUDES].
  destruct(OLD _ _ ERRORS)as[INHERITED_ERRORS ERRORS_EXCLUDES].
  rewrite namespace_launch_environment in GUEST.
  assert(BORROWED_TABLE:parent_channel_cloexec(namespace_table(namespace_fork_child fork_world snapshot))channel)
    by(rewrite TABLE;exact CLOEXEC).
  assert(EXCLUDED_INPUT:excludes_parent_at(namespace_table(namespace_fork_child fork_world snapshot))channel(scope_input scope)).
  { intros binding PRESENT;rewrite TABLE,INHERITED_INPUT in PRESENT;inversion PRESENT;subst;exact INPUT_EXCLUDES. }
  assert(EXCLUDED_OUTPUT:excludes_parent_at(namespace_table(namespace_fork_child fork_world snapshot))channel(scope_output scope)).
  { intros binding PRESENT;rewrite TABLE,INHERITED_OUTPUT in PRESENT;inversion PRESENT;subst;exact OUTPUT_EXCLUDES. }
  assert(EXCLUDED_ERRORS:excludes_parent_at(namespace_table(namespace_fork_child fork_world snapshot))channel(scope_errors scope)).
  { intros binding PRESENT;rewrite TABLE,INHERITED_ERRORS in PRESENT;inversion PRESENT;subst;exact ERRORS_EXCLUDES. }
  assert(EXCLUDED_FAILURE:excludes_parent_at(namespace_table(namespace_fork_child fork_world snapshot))channel failure).
  { intros binding PRESENT;rewrite TABLE,FAILURE in PRESENT;inversion PRESENT;subst;discriminate. }
  destruct(actual_namespace_image_has_private_table _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    BORROWED GUEST LATER GUEST_KERNEL BORROWED_TABLE EXCLUDED_INPUT EXCLUDED_OUTPUT EXCLUDED_ERRORS EXCLUDED_FAILURE)
    as[FINAL PRIVATE].
  rewrite TABLE in FINAL.
  pose proof(actual_namespace_image_checked_handles _ _ _ _ _ _ _ _ _ _ _ _ _
    BORROWED GUEST LATER)as CHECKED.
  pose proof CHECKED as BOUNDS;rewrite Forall_forall in BOUNDS.
  pose proof(BOUNDS(scope_input scope)ltac:(cbn;auto))as INPUT_BOUND.
  pose proof(BOUNDS(scope_output scope)ltac:(cbn;auto))as OUTPUT_BOUND.
  pose proof(BOUNDS(scope_errors scope)ltac:(cbn;auto))as ERRORS_BOUND.
  pose proof(BOUNDS failure ltac:(cbn;auto))as FAILURE_BOUND.
  exists channel,inherited,prefix,rest,guest_le,memory.
  split;[exact WORLD|]. split;[exact EVENTS|]. split;[exact EMPTY|].
  split;[rewrite namespace_launch_environment;exact GUEST|]. split;[exact BORROWED|].
  split;[exact FINAL|]. split;[exact CHECKED|].
  split.
  - rewrite FINAL;eapply handoff_owned_slot_survives;[exact INHERITED_INPUT|cbn;auto|].
    intro SAME;rewrite SAME,Int.signed_one in INPUT_BOUND by (vm_compute;reflexivity);lia.
  - split.
    + rewrite FINAL;eapply handoff_owned_slot_survives;[exact INHERITED_OUTPUT|cbn;auto|].
      intro SAME;rewrite SAME,Int.signed_one in OUTPUT_BOUND by (vm_compute;reflexivity);lia.
    + split.
      * rewrite FINAL;eapply handoff_owned_slot_survives;[exact INHERITED_ERRORS|cbn;auto|].
        intro SAME;rewrite SAME,Int.signed_one in ERRORS_BOUND by (vm_compute;reflexivity);lia.
      * split.
        -- rewrite FINAL;eapply handoff_owned_slot_survives with(binding:=endpoint_binding channel child_endpoint);
             [exact FAILURE|cbn;auto|].
           intro SAME;rewrite SAME,Int.signed_one in FAILURE_BOUND by (vm_compute;reflexivity);lia.
        -- exact PRIVATE.
Qed.
