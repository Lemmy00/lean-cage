(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Raw prepared-root storage inputs retain actual caller values and allocation separation. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine.
From EntryNative Require Import EntrySource.
From EntryProcess Require Import ProcessGlobalCalls.
From EntryReporting Require Import ResultLayout.
From EntryNamespace Require Import NamespaceObjects NamespaceStructure NamespacePaths NamespaceMemory NamespaceChildResult
  NamespaceCaller NamespaceForkWorld NamespaceParentEntry NamespaceKernel NamespaceWorldTrace NamespaceForkPrefix NamespaceTraceRegion.
Import ListNotations.

(* These are preparation's raw values and allocated cells. No admission,
   control, release, successful guard, source-write authorization, or image
   property is a field. M5.3 supplies them from its actual prepared-root path. *)
Record ParentPreparedInput(scope:ChildScope)(peer:int)(parent_memory:mem):Type:={
  prepared_parent_env:env;
  prepared_parent_temps:temp_env;
  prepared_parent_fd:int;
  prepared_report_fd:int;
  prepared_cgroup_fd:int;
  prepared_sequence:int64;
  prepared_status_cell:block;
  prepared_result_temporary:block;
  prepared_admission_cell:block;
  prepared_parent_continuation:scope_continuation scope=
    namespace_creation_cont prepared_parent_env prepared_parent_temps Kstop;
  prepared_parent_global:caller_env_global prepared_parent_env;
  prepared_parent_registers:
    prepared_parent_temps!_input=Some(Vint(scope_input scope)) /\
    prepared_parent_temps!_output=Some(Vint(scope_output scope)) /\
    prepared_parent_temps!_errors=Some(Vint(scope_errors scope)) /\
    prepared_parent_temps!_parentfd=Some(Vint prepared_parent_fd) /\
    prepared_parent_temps!_report=Some(Vint prepared_report_fd) /\
    prepared_parent_temps!_sequence=Some(Vlong prepared_sequence);
  prepared_parent_cells:
    prepared_parent_env!_child=Some(storage_pid(scope_storage scope),tint) /\
    prepared_parent_env!_pipefd=Some(storage_peer(scope_storage scope),tarray tint 2) /\
    prepared_parent_env!_status=Some(prepared_status_cell,tint) /\
    prepared_parent_env!_admission_cgroup=None /\prepared_parent_env!_preflight=None /\
    prepared_parent_env!__res__6=Some(prepared_result_temporary,result_type) /\
    prepared_parent_env!_admission=Some(prepared_admission_cell,result_type);
  prepared_parent_cgroup_load:Mem.load Mint32 parent_memory(namespace_symbol _admission_cgroup)0=
    Some(Vint prepared_cgroup_fd);
  prepared_cgroup_tls:namespace_symbol _admission_cgroup<>tls_block(scope_cell scope);
  prepared_cgroup_sources:
    prepared_cgroup_fd<>scope_input scope /\prepared_cgroup_fd<>scope_output scope /\
    prepared_cgroup_fd<>scope_errors scope /\prepared_cgroup_fd<>prepared_parent_fd;
  prepared_status_separation:
    prepared_status_cell<>storage_pid(scope_storage scope) /\prepared_status_cell<>storage_peer(scope_storage scope) /\
    prepared_status_cell<>namespace_symbol _admission_cgroup /\prepared_status_cell<>namespace_symbol _preflight;
  prepared_status_tls:prepared_status_cell<>tls_block(scope_cell scope);
  prepared_cgroup_local_separation:
    namespace_symbol _admission_cgroup<>storage_pid(scope_storage scope) /\
    namespace_symbol _admission_cgroup<>storage_pair(scope_storage scope)
}.

Arguments prepared_parent_env {scope peer parent_memory} _.
Arguments prepared_parent_temps {scope peer parent_memory} _.
Arguments prepared_parent_fd {scope peer parent_memory} _.
Arguments prepared_report_fd {scope peer parent_memory} _.
Arguments prepared_cgroup_fd {scope peer parent_memory} _.
Arguments prepared_sequence {scope peer parent_memory} _.
Arguments prepared_status_cell {scope peer parent_memory} _.
Arguments prepared_result_temporary {scope peer parent_memory} _.
Arguments prepared_admission_cell {scope peer parent_memory} _.
Arguments prepared_parent_continuation {scope peer parent_memory} _.
Arguments prepared_parent_global {scope peer parent_memory} _.
Arguments prepared_parent_registers {scope peer parent_memory} _.
Arguments prepared_parent_cells {scope peer parent_memory} _.
Arguments prepared_parent_cgroup_load {scope peer parent_memory} _.
Arguments prepared_cgroup_tls {scope peer parent_memory} _.
Arguments prepared_cgroup_sources {scope peer parent_memory} _.
Arguments prepared_status_separation {scope peer parent_memory} _.
Arguments prepared_status_tls {scope peer parent_memory} _.
Arguments prepared_cgroup_local_separation {scope peer parent_memory} _.

Theorem prepared_old_descriptor_differs_peer before common fork_world scope first second failure reply le memory
    channel old binding:
  scope_history scope=[] ->
  NamespaceForkPrefix.ChildPrefixResult scope(NamespaceTraceRegion.namespace_fd_events common)
    (Callstate NamespaceMachine.namespace_fork_definition[]
      (child_fork_cont(storage_pair(scope_storage scope))le(scope_continuation scope))memory) ->
  NamespaceTraceRegion.namespace_fd_events common=child_signal_log scope first second failure reply ->
  NamespaceWorldTrace.namespace_kernel_steps before common fork_world ->
  namespace_table fork_world first=Some(endpoint_binding channel parent_endpoint) ->
  namespace_table before old=Some binding ->old<>first.
Proof.
  intros HISTORY FRONTIER LOG KERNEL PEER OLD.
  destruct(source_common_fork_world _ _ _ _ _ _ _ _ _ _ HISTORY FRONTIER LOG KERNEL)
    as[actual[inherited[WORLD[DEFAULT[MASK[D0[D1[MINIMUM[FIRST[FAILURE[CLOEXEC[AMBIENT PRESERVED]]]]]]]]]]]].
  assert(TABLE:namespace_table fork_world=inherited).
  { rewrite WORLD;unfold child_fork_world,NamespaceKernel.namespace_default_action;rewrite Int.eq_true;reflexivity. }
  rewrite TABLE,FIRST in PEER;unfold endpoint_binding in PEER;inversion PEER;subst actual.
  destruct(PRESERVED _ _ OLD)as[PRESENT OBJECT].
  intro SAME;subst old;rewrite FIRST in PRESENT;inversion PRESENT;subst binding;apply OBJECT;reflexivity.
Qed.
