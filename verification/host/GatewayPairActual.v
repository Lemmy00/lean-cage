(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: The full native helper derives normalized endpoints from its same actual pair birth. *)
From Stdlib Require Import ZArith List Lia String.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine CallContexts.
From HostGateway Require Import GatewaySource GatewayMachine GatewaySpawnABI GatewaySpawnResources GatewaySpawnRuntime
  GatewayPairContext GatewayPairSource GatewayPairInputs GatewayPairStart
  GatewayThreadRuntime GatewayFramedRuntime GatewaySetupPaths GatewayOperations GatewayFrames GatewayStreamInterface GatewayContexts
  GatewayPairHistory GatewayPairBuffers GatewayCallerBuffers.
Import ListNotations.
Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Theorem actual_private_pair_with_origin_history {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
    native_private stable_readonly discipline thread_errno resources ipc
    (runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno)
    (descriptors:gateway_spawn_descriptor_runtime backend io native_private stable_readonly discipline resources ipc)
    object offset(history:mem->World->Prop)
    (buffers:gateway_pair_buffer_laws backend native_private stable_readonly discipline object offset history)
    before world events after next:
  gateway_pair_input native_private discipline resources object offset before world->
  history before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_private_pair)[Vptr object offset]Kstop before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next)->
  exists prefix suffix called call_world born born_world observed
    (receipt:gateway_socketpair_receipt ipc(resources call_world)(resources born_world)),
    events=prefix++gateway_primitive observed::suffix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(Internal f_host_private_pair)[Vptr object offset]Kstop before)world)prefix
      (gateway_live(Callstate(gateway_spawn_signature gateway_socketpair_api)(pair_socket_arguments object offset)
        (pair_socket_cont(Vptr object offset))called)call_world) /\
    gateway_spawn_operation backend gateway_socketpair_api(pair_socket_arguments object offset)
      called call_world(Vint Int.zero)born born_world observed /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate(Vint Int.zero)(pair_socket_cont(Vptr object offset))born)born_world)suffix
      (gateway_live(Returnstate(Vint Int.zero)Kstop after)next) /\
    gateway_pair_input native_private discipline resources object offset called call_world /\
    gateway_resource_reference(resources world)(resources call_world) /\
    gateway_resource_reference(resources world)(resources next) /\
    exists left right,4<=left /\4<=right /\
      gateway_pair_full_context native_private discipline resources ipc
        (gateway_pair_receipt_identity ipc(resources call_world)(resources born_world)receipt)
        object offset left right history after next.
Proof.
  intros INITIAL INITIAL_HISTORY RUN.
  set(input:=fun memory current=>(gateway_pair_input native_private discipline resources object offset memory current /\
    gateway_resource_reference(resources world)(resources current))/\history memory current).
  assert(INPUT_AMBIENT:gateway_runtime_discipline backend input).
  { intros first current changed later[RAW HISTORY]INTERFERENCE;split.
    - eapply gateway_pair_input_reference_ambient;eassumption.
    - eapply gateway_pair_buffer_ambient;[exact buffers|exact(proj1(proj1 RAW))|exact HISTORY|exact INTERFERENCE]. }
  assert(INPUT_INITIAL:input before world)by(split;[split;[exact INITIAL|apply gateway_resource_reference_refl]|exact INITIAL_HISTORY]).
  destruct(actual_pair_first_socket backend input INPUT_AMBIENT object offset before world events(Vint Int.zero)after next INPUT_INITIAL RUN)
    as[entry_events[rest[entry_memory[entry_world[EVENTS[QUIET[ENTRY[INPUT REST]]]]]]]].
  destruct(gateway_return_cut backend(Clight.globalenv prog)(gateway_spawn_signature gateway_socketpair_api)
    (pair_socket_arguments object offset)(pair_socket_cont(Vptr object offset))entry_memory entry_world rest
    (Returnstate(Vint Int.zero)Kstop after)next ltac:(exact I)ltac:(cbn;lia)REST)
    as[callee_events[caller_events[returned[returned_memory[returned_world[REST_EVENTS[CALLEE CALLER]]]]]]].
  destruct(gateway_external_operation_of_run backend(Clight.globalenv prog)
    (EF_external "socketpair"(mksignature[Xint;Xint;Xint;Xptr]Xint cc_default))
    [tint;tint;tint;tptr tint]tint cc_default(pair_socket_arguments object offset)
    entry_memory entry_world callee_events returned returned_memory returned_world CALLEE)
    as[pending[post_events[called[call_world[born[born_world[observed
      [CALLEE_EVENTS[PENDING[PENDING_RUN[OPERATION POST_RUN]]]]]]]]]]].
  assert(AT_INPUT:input called call_world).
  { exact(gateway_pending_run_ready backend(Clight.globalenv prog)input INPUT_AMBIENT
      (Callstate(gateway_spawn_signature gateway_socketpair_api)(pair_socket_arguments object offset)Kstop entry_memory)
      entry_memory entry_world pending called call_world INPUT PENDING PENDING_RUN). }
  assert(API:gateway_spawn_operation backend gateway_socketpair_api(pair_socket_arguments object offset)
    called call_world returned born born_world observed).
  { exists(gateway_spawn_signature gateway_socketpair_api);split;[apply actual_gateway_spawn_signatures|exact OPERATION]. }
  pose proof(proj1(proj1 AT_INPUT))as AT_RAW.
  destruct(gateway_socketpair_operation _ _ _ _ _ _ _ descriptors called call_world object offset returned born born_world observed
    (proj1 AT_RAW)(proj2(proj2(proj2 AT_RAW)))(proj1(proj2 AT_RAW))(proj1(proj2(proj2 AT_RAW)))API)
    as[SIDE[VALID[ACCESS[PERMISSIONS[FRAME[EXCLUSIVE[IO[FAILED|[receipt[RETURNED[LEFT RIGHT]]]]]]]]]]].
  - destruct FAILED as[RETURNED REST_FAILED];subst returned.
    pose proof(actual_pair_socket_failed backend(Clight.globalenv prog)object offset returned_memory returned_world caller_events
      (Vint Int.zero)after next CALLER)as BAD;discriminate BAD.
  - subst returned.
    set(identity:=gateway_pair_receipt_identity ipc(resources call_world)(resources born_world)receipt).
    set(first:=gateway_pair_left _ _ _ receipt).
    set(second:=gateway_pair_right _ _ _ receipt).
    set(context:=gateway_pair_full_context native_private discipline resources ipc identity object offset first second history).
    assert(AT_BIRTH:context born born_world).
    { split.
      - eapply gateway_pair_created_context;[exact AT_RAW|exact SIDE|exact VALID|exact ACCESS|exact PERMISSIONS|
          exact EXCLUSIVE|exact LEFT|exact RIGHT].
      - eapply gateway_pair_buffer_socket;[exact buffers|exact(proj2 AT_INPUT)|exact ACCESS|exact PERMISSIONS|exact FRAME]. }
    assert(CONTEXT_AMBIENT:gateway_ambient_closed backend context).
    { apply gateway_pair_full_context_ambient with(io:=io)(stable_readonly:=stable_readonly)(thread_errno:=thread_errno);assumption. }
    assert(AT_RETURN:context returned_memory returned_world).
    { destruct(gateway_runtime_path_return_exact backend(Clight.globalenv prog)context
        (Returnstate(Vint Int.zero)Kstop born)(Vint Int.zero)context born born_world post_events
        (Vint Int.zero)returned_memory returned_world AT_BIRTH
        ltac:(constructor;[exact CONTEXT_AMBIENT|auto])POST_RUN)as[RETURNED READY];exact READY. }
    assert(FINAL:exists left right,4<=left /\4<=right /\
      gateway_pair_full_context native_private discipline resources ipc identity object offset left right history after next).
    { destruct(actual_gateway_spawn_binding gateway_fcntl_api)as[duplicate_symbol[DS DF]].
      destruct(actual_gateway_spawn_binding gateway_close_api)as[close_symbol[CS CF]].
      eapply gateway_setup_return_exact with
        (result:=fun memory current=>exists left right,4<=left /\4<=right /\
          gateway_pair_full_context native_private discipline resources ipc identity object offset left right history memory current)
        (property:=context)(source:=Returnstate(Vint Int.zero)(pair_socket_cont(Vptr object offset))returned_memory).
      - exact AT_RETURN.
      - eapply actual_pair_started_script with(io:=io)(stable_readonly:=stable_readonly)(thread_errno:=thread_errno)
          (duplicate_symbol:=duplicate_symbol)(close_symbol:=close_symbol);try eassumption.
        intros left right memory current LBOUND RBOUND READY;exists left,right;split;[exact LBOUND|].
        split;[exact RBOUND|exact READY].
      - exact CALLER. }
    exists(entry_events++pending),(post_events++caller_events),called,call_world,born,born_world,observed,receipt.
    split.
    + rewrite EVENTS,REST_EVENTS,CALLEE_EVENTS;repeat rewrite<-app_assoc;cbn[app];reflexivity.
    + split.
      * eapply gateway_steps_append;[exact ENTRY|].
        exact(gateway_plug_steps backend(Clight.globalenv prog)_ _ _ (pair_socket_cont(Vptr object offset))I PENDING_RUN).
      * split;[exact API|]. split.
        -- eapply gateway_steps_append;[|exact CALLER].
           exact(gateway_plug_steps backend(Clight.globalenv prog)_ _ _ (pair_socket_cont(Vptr object offset))I POST_RUN).
        -- split;[exact AT_RAW|]. split;[exact(proj2(proj1 AT_INPUT))|]. split;[|exact FINAL].
           destruct FINAL as[left[right[LBOUND[RBOUND CONTEXT]]]].
           eapply gateway_resource_reference_transitive;[exact(proj2(proj1 AT_INPUT))|].
           exact(gateway_pair_original_reference ipc identity left right(resources next)(proj2(proj2(proj2(proj1 CONTEXT))))).
Qed.

Theorem actual_private_pair_with_history {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
    native_private stable_readonly discipline thread_errno resources ipc
    (runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno)
    (descriptors:gateway_spawn_descriptor_runtime backend io native_private stable_readonly discipline resources ipc)
    object offset(history:mem->World->Prop)
    (buffers:gateway_pair_buffer_laws backend native_private stable_readonly discipline object offset history)
    before world events after next:
  gateway_pair_input native_private discipline resources object offset before world->
  history before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_private_pair)[Vptr object offset]Kstop before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next)->
  exists prefix suffix called call_world born born_world observed
    (receipt:gateway_socketpair_receipt ipc(resources call_world)(resources born_world)),
    events=prefix++gateway_primitive observed::suffix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(Internal f_host_private_pair)[Vptr object offset]Kstop before)world)prefix
      (gateway_live(Callstate(gateway_spawn_signature gateway_socketpair_api)(pair_socket_arguments object offset)
        (pair_socket_cont(Vptr object offset))called)call_world) /\
    gateway_spawn_operation backend gateway_socketpair_api(pair_socket_arguments object offset)
      called call_world(Vint Int.zero)born born_world observed /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate(Vint Int.zero)(pair_socket_cont(Vptr object offset))born)born_world)suffix
      (gateway_live(Returnstate(Vint Int.zero)Kstop after)next) /\
    gateway_pair_input native_private discipline resources object offset called call_world /\
    gateway_resource_reference(resources world)(resources next) /\
    exists left right,4<=left /\4<=right /\
      gateway_pair_full_context native_private discipline resources ipc
        (gateway_pair_receipt_identity ipc(resources call_world)(resources born_world)receipt)
        object offset left right history after next.
Proof.
  intros INITIAL HISTORY RUN.
  destruct(actual_private_pair_with_origin_history backend io native_private stable_readonly discipline thread_errno resources ipc
    runtime descriptors object offset history buffers before world events after next INITIAL HISTORY RUN)
    as(prefix&suffix&called&call_world&born&born_world&observed&receipt&EVENTS&PREFIX&OPERATION&SUFFIX&RAW&ORIGIN&REFERENCE&FINAL).
  exists prefix,suffix,called,call_world,born,born_world,observed,receipt.
  split;[exact EVENTS|]. split;[exact PREFIX|]. split;[exact OPERATION|]. split;[exact SUFFIX|].
  split;[exact RAW|]. split;[exact REFERENCE|exact FINAL].
Qed.

(* This compatibility view retains the existing role/lease result. The complete
   caller uses the derived buffer specialization below. *)
Theorem actual_private_pair {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
    native_private stable_readonly discipline thread_errno resources ipc
    (runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno)
    (descriptors:gateway_spawn_descriptor_runtime backend io native_private stable_readonly discipline resources ipc)
    object offset before world events after next:
  gateway_pair_input native_private discipline resources object offset before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_private_pair)[Vptr object offset]Kstop before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next)->
  exists prefix suffix called call_world born born_world observed
    (receipt:gateway_socketpair_receipt ipc(resources call_world)(resources born_world)),
    events=prefix++gateway_primitive observed::suffix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(Internal f_host_private_pair)[Vptr object offset]Kstop before)world)prefix
      (gateway_live(Callstate(gateway_spawn_signature gateway_socketpair_api)(pair_socket_arguments object offset)
        (pair_socket_cont(Vptr object offset))called)call_world) /\
    gateway_spawn_operation backend gateway_socketpair_api(pair_socket_arguments object offset)
      called call_world(Vint Int.zero)born born_world observed /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate(Vint Int.zero)(pair_socket_cont(Vptr object offset))born)born_world)suffix
      (gateway_live(Returnstate(Vint Int.zero)Kstop after)next) /\
    gateway_pair_input native_private discipline resources object offset called call_world /\
    gateway_resource_reference(resources world)(resources next) /\
    exists left right,4<=left /\4<=right /\
      gateway_pair_context native_private discipline resources ipc
        (gateway_pair_receipt_identity ipc(resources call_world)(resources born_world)receipt)
        object offset left right after next.
Proof.
  intros INITIAL RUN.
  destruct(actual_private_pair_with_history backend io native_private stable_readonly discipline thread_errno resources ipc
    runtime descriptors object offset(fun _ _=>True)
    (gateway_pair_trivial_buffer_laws backend native_private stable_readonly discipline object offset)
    before world events after next INITIAL I RUN)
    as[prefix[suffix[called[call_world[born[born_world[observed[receipt
      [EVENTS[PREFIX[API[SUFFIX[RAW[REFERENCE[left[right[LBOUND[RBOUND[BASE HISTORY]]]]]]]]]]]]]]]]]]].
  exists prefix,suffix,called,call_world,born,born_world,observed,receipt.
  split;[exact EVENTS|]. split;[exact PREFIX|]. split;[exact API|]. split;[exact SUFFIX|].
  split;[exact RAW|]. split;[exact REFERENCE|]. exists left,right;split;[exact LBOUND|]. split;assumption.
Qed.

Theorem actual_private_pair_buffers {World Event}(backend:gateway_backend World Event)(io:Event->option gateway_native_io)
    native_private stable_readonly discipline thread_errno resources ipc
    (runtime:gateway_thread_runtime backend io native_private stable_readonly discipline thread_errno)
    (descriptors:gateway_spawn_descriptor_runtime backend io native_private stable_readonly discipline resources ipc)
    object offset readonly reference owner before world events after next:
  (forall position,~readonly object position)->
  gateway_pair_input native_private discipline resources object offset before world->
  gateway_caller_buffers native_private stable_readonly readonly object reference owner before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_private_pair)[Vptr object offset]Kstop before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next)->
  exists prefix suffix called call_world born born_world observed
    (receipt:gateway_socketpair_receipt ipc(resources call_world)(resources born_world)),
    events=prefix++gateway_primitive observed::suffix /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(Internal f_host_private_pair)[Vptr object offset]Kstop before)world)prefix
      (gateway_live(Callstate(gateway_spawn_signature gateway_socketpair_api)(pair_socket_arguments object offset)
        (pair_socket_cont(Vptr object offset))called)call_world) /\
    gateway_spawn_operation backend gateway_socketpair_api(pair_socket_arguments object offset)
      called call_world(Vint Int.zero)born born_world observed /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate(Vint Int.zero)(pair_socket_cont(Vptr object offset))born)born_world)suffix
      (gateway_live(Returnstate(Vint Int.zero)Kstop after)next) /\
    gateway_pair_input native_private discipline resources object offset called call_world /\
    gateway_resource_reference(resources world)(resources next) /\
    exists left right,4<=left /\4<=right /\
      gateway_pair_context native_private discipline resources ipc
        (gateway_pair_receipt_identity ipc(resources call_world)(resources born_world)receipt)
        object offset left right after next /\
      gateway_caller_buffers native_private stable_readonly readonly object reference owner after next.
Proof.
  intros DISJOINT INITIAL HISTORY RUN.
  exact(actual_private_pair_with_history backend io native_private stable_readonly discipline thread_errno resources ipc
    runtime descriptors object offset(gateway_caller_buffers native_private stable_readonly readonly object reference owner)
    (gateway_pair_caller_buffer_laws backend io native_private stable_readonly discipline thread_errno runtime
      readonly object offset reference owner DISJOINT)before world events after next INITIAL HISTORY RUN).
Qed.
