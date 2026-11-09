(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Every actual guest image has the five successful descriptor operations in its own history. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine StoreSteps.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffStructure NativeHandoffArguments
  NativeHandoffAllocation NativeHandoffInput NativeHandoffMemory NativeHandoffLoop NativeHandoffExec NativeHandoffGuest
  NativeHandoffImage NativeHandoffTracePaths NativeHandoffTraceChecks NativeHandoffTraceGuest.
Import ListNotations.
Open Scope Z_scope.
Local Opaque handoff_ge handoff_symbol.

Theorem handoff_guest_image_flags cell input before input_fd output_fd errors_fd failure k
    events target path arguments environment :
  handoff_borrowed_input cell before input ->
  entry_handoff_steps handoff_ge cell
    (live(Callstate(Internal EntrySource.f_guest)[Vint input_fd;Vint output_fd;Vint errors_fd;Vint failure]k before))events target ->
  In(entry_image path arguments environment)events ->
  exists prefix b after caller suffix waits,
    events=prefix++(repeat entry_primitive_wait waits++[entry_image path arguments environment]) /\
    handoff_flags_projection prefix=handoff_expected_flags input_fd output_fd errors_fd failure /\
    entry_handoff_steps handoff_ge cell
      (live(Callstate(Internal EntrySource.f_guest)[Vint input_fd;Vint output_fd;Vint errors_fd;Vint failure]k before))prefix
      (live(Callstate entry_exec_definition
        [Vptr(handoff_symbol EntrySource.___stringlit_111)Ptrofs.zero;
         Vptr(handoff_arguments b)Ptrofs.zero;Vptr(handoff_environment b)Ptrofs.zero]
        (handoff_exec_cont(handoff_locals_env b)caller(Kseq(guest_tail 24(fn_body EntrySource.f_guest))suffix))after)) /\
    path=Vptr(handoff_symbol EntrySource.___stringlit_111)Ptrofs.zero /\
    arguments=Vptr(handoff_arguments b)Ptrofs.zero /\environment=Vptr(handoff_environment b)Ptrofs.zero /\target=dead after.
Proof.
  intros INPUT RUN IMAGE.
  assert(SAFE:handoff_trace_failure_safe cell).
  { intros m fd stage error call history last ERRNO CALL EXEC p a e.
    exact(handoff_failure_call_has_no_image cell m fd stage error call history last ERRNO CALL EXEC p a e). }
  destruct(handoff_guest_image_has_checked_snapshot _ _ _ _ _ _ _ _ _ _ _ _ _ INPUT RUN IMAGE)
    as[oldprefix[endpoint[oldrest[OLDEVENTS[OLDNONE[OLDPREFIX[SNAPSHOT[OLDREST OLDIMAGE]]]]]]]].
  destruct SNAPSHOT as[oldb[oldafter[oldcaller[uidbytes[fdtexts[oldk[SAME[FAILURE FIELDS]]]]]]]].
  destruct FIELDS as[LIVE[MODE[UID[UIDTEXT[UIDLEN[UIDVALUE[HISTORY[HISTORYLEN[CHECKED TABLES]]]]]]]]].
  pose proof(handoff_trace_guest_normal cell input before input_fd output_fd errors_fd failure k
    SAFE INPUT MODE UID CHECKED events target path arguments environment RUN IMAGE)as CUT.
  destruct CUT as[prefix[last[rest[EVENTS[FLAGS[PREFIX[READY[REST LATER]]]]]]]].
  destruct READY as[b[after[caller[suffix[END CALLERFAILURE]]]]];subst last.
  destruct(handoff_exec_image_is_current _ _ _ _ _ _ _ _ _ _ _ _ _ _ CALLERFAILURE REST LATER)
    as[PATH[ARGUMENTS[ENVIRONMENT[waits[RESTEVENTS TARGET]]]]].
  exists prefix,b,after,caller,suffix,waits;split;[rewrite EVENTS,RESTEVENTS,PATH,ARGUMENTS,ENVIRONMENT;reflexivity|].
  split;[exact FLAGS|]. split;[exact PREFIX|]. split;[exact PATH|]. split;[exact ARGUMENTS|]. split;assumption.
Qed.
