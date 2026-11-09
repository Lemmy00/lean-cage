(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.values: The same actual fork/image supplies the ordinary worker's exact inputs. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
From LeanImport Require Import Lean.
Require Import ArgumentsImport Machine.
From EntryNative Require Import EntrySource NativeValues NativeHandoffMachine NativeHandoffStructure NativeHandoffArguments
  NativeHandoffAllocation NativeHandoffInput NativeHandoffInitial NativeHandoffExec NativeHandoffGuest
  NativeHandoffValues NativeHandoffWire NativeHandoffConnection.
From EntryProcess Require Import ProcessMachine.
From EntryNamespace Require Import NamespaceMachine NamespaceStructure NamespacePaths NamespaceMemory NamespaceTraceRegion
  NamespaceChildResult NamespaceForkPrefix NamespaceFork NamespaceKernel NamespaceChildImage NamespaceGuestFlags
  NamespaceGuest NamespaceLaunch.
Import ListNotations.
Local Close Scope lean_scope.
Local Open Scope Z_scope.
Local Opaque namespace_ge handoff_ge.

Theorem same_fork_worker_argument_values scope first second failure reply le before world snapshot parent child
    events target path arguments environment valid_utf8 copied(runtime:WorkerArgvContract valid_utf8 copied):
  scope_history scope=[] ->
  ChildPrefixResult scope(child_signal_log scope first second failure reply)
    (Callstate namespace_fork_definition[]
      (child_fork_cont(storage_pair(scope_storage scope))le(scope_continuation scope))before) ->
  fork_matches world snapshot ->NativeForkCopy(scope_cell scope)before parent child ->
  namespace_steps namespace_ge(scope_cell scope)
    (live(Returnstate(Vint Int.zero)
      (child_fork_cont(storage_pair(scope_storage scope))le(scope_continuation scope))child))events target ->
  In(namespace_guest_event(entry_image path arguments environment))events ->
  valid_utf8(handoff_borrowed_root_bytes(scope_borrowed scope)) ->
  Forall valid_utf8(handoff_borrowed_argument_bytes(scope_borrowed scope)) ->
  exists prefix rest guest_le guest_memory actual b after caller suffix,
    events=prefix++rest /\namespace_fd_events prefix=[] /\
    rest=map namespace_guest_event actual /\
    namespace_steps namespace_ge(scope_cell scope)
      (live(Callstate(Internal f_guest)
        [Vint(scope_input scope);Vint(scope_output scope);Vint(scope_errors scope);Vint failure]
        (child_guest_cont(storage_pair(scope_storage scope))guest_le(scope_continuation scope))guest_memory))rest target /\
    handoff_checked_lean(forall args,copied after(handoff_arguments b)args ->
      LeanCage_Entry_ArgumentMeaning_nativeValues
        (Nat_of_nat(Z.to_nat(Int.unsigned(handoff_borrowed_uid(scope_borrowed scope)))))
        (Nat_of_nat(Z.to_nat(Int.signed(scope_input scope))))
        (Nat_of_nat(Z.to_nat(Int.signed(scope_output scope))))
        (Nat_of_nat(Z.to_nat(Int.signed(scope_errors scope))))(Nat_of_nat(Z.to_nat(Int.signed failure)))
        (argument_bytes(handoff_worker_mode_bytes(handoff_borrowed_preflight(scope_borrowed scope))))
        (argument_bytes(handoff_borrowed_root_bytes(scope_borrowed scope)))(argument_bytes handoff_normal_bytes)
        (argument_byte_lists(handoff_borrowed_argument_bytes(scope_borrowed scope)))args) /\
    path=Vptr(handoff_symbol EntrySource.___stringlit_111)Ptrofs.zero /\
    arguments=Vptr(handoff_arguments b)Ptrofs.zero /\
    environment=Vptr(handoff_environment b)Ptrofs.zero /\target=dead after /\
    exists native_prefix native_rest,
      actual=native_prefix++native_rest /\
      entry_handoff_steps handoff_ge(scope_cell scope)
        (live(Callstate entry_exec_definition[path;arguments;environment]
          (handoff_exec_cont(handoff_locals_env b)caller(Kseq(guest_tail 24(fn_body f_guest))suffix))after))
        native_rest target.
Proof.
  intros HISTORY FRONTIER MATCH COPY RUN IMAGE ROOTUTF8 ARGVUTF8.
  destruct(actual_child_branch_image_reaches_guest scope first second failure reply le before
    world snapshot parent child events target path arguments environment HISTORY FRONTIER MATCH COPY RUN IMAGE)
    as[prefix[rest[guest_le[guest_memory[EVENTS[EMPTY[NOIMAGES[PRE[BORROWED[NONNEGATIVE[GUEST LATER]]]]]]]]]]].
  rewrite namespace_launch_environment in GUEST.
  destruct(actual_namespace_guest_projects _ _ _ _ _ _ _ _ _ _ BORROWED GUEST)
    as[actual[REST REAL]].
  assert(ACTUAL_IMAGE:In(entry_image path arguments environment)actual).
  { rewrite REST in LATER;apply in_map_iff in LATER as[event[SAME MEMBER]];inversion SAME;subst;exact MEMBER. }
  destruct(handoff_guest_worker_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ runtime
    BORROWED REAL ACTUAL_IMAGE ROOTUTF8 ARGVUTF8)
    as[native_prefix[endpoint[native_rest[b[after[caller[suffix FACTS]]]]]]].
  destruct FACTS as[ACTUAL[NOIMAGES' F0]]. destruct F0 as[PREFIX[STATE F1]].
  destruct F1 as[SNAPSHOT[TAIL F2]]. destruct F2 as[LATER'[FAILURE F3]].
  destruct F3 as[VALUES[PATH[ARGS[ENV TARGET]]]].
  exists prefix,rest,guest_le,guest_memory,actual,b,after,caller,suffix.
  split;[exact EVENTS|]. split;[exact EMPTY|]. split;[exact REST|].
  split;[rewrite namespace_launch_environment;exact GUEST|]. split;[exact VALUES|].
  split;[exact PATH|]. split;[exact ARGS|]. split;[exact ENV|]. split;[exact TARGET|].
  exists native_prefix,native_rest;split;[exact ACTUAL|].
  rewrite STATE,<-PATH,<-ARGS,<-ENV in TAIL;exact TAIL.
Qed.
