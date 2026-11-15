(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.ownership: Pair origins retain their exact copyout and
   position before the original selected spawn call. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import CallContexts.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewaySpawnABI
  GatewaySpawnResources GatewaySpawnRuntime GatewayPairContext GatewayPairSource GatewayPairKernelOrigin
  GatewayExchangePairContext GatewayExchangeContext GatewayCallerFamily GatewayCallerBuffers
  GatewayPairBuffers GatewayPairInputs GatewayPairHistory GatewayThreadRuntime GatewayStreamInterface.
Import ListNotations.

Definition gateway_copyout_pair_birth {World Event} (backend : gateway_backend World Event)
    (resources : World -> gateway_resource_state) ipc object before world events after next
    (identity : gateway_pair_identity ipc) : Prop :=
  exists prefix suffix called call_world born born_world observed
    (receipt : gateway_socketpair_receipt ipc (resources call_world) (resources born_world)),
    identity = gateway_pair_receipt_identity ipc (resources call_world) (resources born_world) receipt /\
    events = prefix ++ gateway_primitive observed :: suffix /\
    gateway_steps backend (Clight.globalenv prog)
      (gateway_live (Callstate (Internal f_host_private_pair) [Vptr object Ptrofs.zero] Kstop before) world) prefix
      (gateway_live (Callstate (gateway_spawn_signature gateway_socketpair_api)
        (pair_socket_arguments object Ptrofs.zero) (pair_socket_cont (Vptr object Ptrofs.zero)) called) call_world) /\
    gateway_spawn_operation backend gateway_socketpair_api (pair_socket_arguments object Ptrofs.zero)
      called call_world (Vint Int.zero) born born_world observed /\
    Mem.load Mint32 born object 0 = Some (Vint (Int.repr (gateway_pair_left _ _ _ receipt))) /\
    Mem.load Mint32 born object 4 = Some (Vint (Int.repr (gateway_pair_right _ _ _ receipt))) /\
    gateway_steps backend (Clight.globalenv prog)
      (gateway_live (Returnstate (Vint Int.zero) (pair_socket_cont (Vptr object Ptrofs.zero)) born) born_world)
      suffix (gateway_live (Returnstate (Vint Int.zero) Kstop after) next).

Lemma gateway_copyout_pair_forget {World Event} (backend : gateway_backend World Event)
    resources ipc object before world events after next identity :
  gateway_copyout_pair_birth backend resources ipc object before world events after next identity ->
  gateway_pair_birth_in_run backend resources ipc object before world events after next identity.
Proof.
  intros (prefix & suffix & called & call_world & born & born_world & observed & receipt &
    IDENTITY & EVENTS & PREFIX & OPERATION & LEFT & RIGHT & SUFFIX).
  exists prefix, suffix, called, call_world, born, born_world, observed, receipt.
  split; [exact IDENTITY |]. split; [exact EVENTS |]. split; [exact PREFIX |]. split; assumption.
Qed.

Theorem actual_exchange_pair_copyout {World Event} (backend : gateway_backend World Event)
    io native stable discipline thread_errno resources ipc
    (thread : gateway_thread_runtime backend io native stable discipline thread_errno)
    (descriptors : gateway_spawn_descriptor_runtime backend io native stable discipline resources ipc)
    readonly selected reference owner original object before world events after next :
  (forall position, ~ readonly object position) -> selected object -> Mem.range_perm reference object 0 8 Cur Freeable ->
  gateway_exchange_context native stable discipline resources readonly selected reference owner original before world ->
  gateway_steps backend (Clight.globalenv prog)
    (gateway_live (Callstate (Internal f_host_private_pair) [Vptr object Ptrofs.zero] Kstop before) world) events
    (gateway_live (Returnstate (Vint Int.zero) Kstop after) next) ->
  exists (identity : gateway_pair_identity ipc) left right,
    (4 <= left)%Z /\ (4 <= right)%Z /\
    gateway_copyout_pair_birth backend resources ipc object before world events after next identity /\
    gateway_resource_reference (resources world) (pair_origin ipc identity) /\
    gateway_pair_context native discipline resources ipc identity object Ptrofs.zero left right after next /\
    gateway_exchange_context native stable discipline resources readonly selected reference owner original after next.
Proof.
  intros DISJOINT SELECTED PERMISSIONS INITIAL RUN.
  pose proof (gateway_caller_family_pair_input native stable discipline resources readonly selected reference owner original
    before world object INITIAL SELECTED PERMISSIONS) as RAW.
  destruct (actual_private_pair_with_kernel_origin_history backend io native stable discipline thread_errno resources ipc
    thread descriptors object Ptrofs.zero (gateway_caller_family native stable readonly selected reference owner)
    (gateway_caller_family_pair_laws backend io native stable discipline thread_errno thread readonly selected object
      Ptrofs.zero reference owner DISJOINT) before world events after next RAW (proj2 (proj2 INITIAL)) RUN)
    as (prefix & suffix & called & call_world & born & born_world & observed & receipt & EVENTS & PREFIX & OPERATION &
      LEFT_LOAD & RIGHT_LOAD & SUFFIX & CALLED & ORIGIN & REFERENCE & left & right & LEFT & RIGHT & PAIR & FAMILY).
  exists (gateway_pair_receipt_identity ipc (resources call_world) (resources born_world) receipt), left, right.
  split; [exact LEFT |]. split; [exact RIGHT |]. split.
  - exists prefix, suffix, called, call_world, born, born_world, observed, receipt.
    split; [reflexivity |]. split; [exact EVENTS |]. split; [exact PREFIX |]. split; [exact OPERATION |].
    split; [exact LEFT_LOAD |]. split; assumption.
  - split; [exact ORIGIN |]. split; [exact PAIR |].
    destruct PAIR as [SIDE [PRIVATE [CELLS RESOURCES]]].
    split; [exact SIDE |]. split; [|exact FAMILY]. split; [exact (proj1 RESOURCES) |].
    eapply gateway_resource_reference_transitive; [exact (proj2 (proj1 (proj2 INITIAL))) |exact REFERENCE].
Qed.

Definition gateway_copyout_pair_slice {World Event} (backend : gateway_backend World Event)
    (resources : World -> gateway_resource_state) ipc object source world events target next
    (identity : gateway_pair_identity ipc) ordinal : Prop :=
  exists prefix suffix continuation called call_world born born_world observed
    (receipt : gateway_socketpair_receipt ipc (resources call_world) (resources born_world)),
    identity = gateway_pair_receipt_identity ipc (resources call_world) (resources born_world) receipt /\
    length prefix = ordinal /\ events = prefix ++ gateway_primitive observed :: suffix /\
    gateway_steps backend (Clight.globalenv prog) (gateway_live source world) prefix
      (gateway_live (Callstate (gateway_spawn_signature gateway_socketpair_api)
        (pair_socket_arguments object Ptrofs.zero) continuation called) call_world) /\
    gateway_spawn_operation backend gateway_socketpair_api (pair_socket_arguments object Ptrofs.zero)
      called call_world (Vint Int.zero) born born_world observed /\
    Mem.load Mint32 born object 0 = Some (Vint (Int.repr (gateway_pair_left _ _ _ receipt))) /\
    Mem.load Mint32 born object 4 = Some (Vint (Int.repr (gateway_pair_right _ _ _ receipt))) /\
    gateway_steps backend (Clight.globalenv prog)
      (gateway_live (Returnstate (Vint Int.zero) continuation born) born_world) suffix (gateway_live target next).

Theorem gateway_copyout_pair_slice_positioned {World Event} (backend : gateway_backend World Event) resources ipc
    object source world prefix helper_events suffix continuation before called_world after returned_world identity events target next :
  is_call_cont continuation -> events = prefix ++ helper_events ++ suffix ->
  gateway_steps backend (Clight.globalenv prog) (gateway_live source world) prefix
    (gateway_live (Callstate (Internal f_host_private_pair) [Vptr object Ptrofs.zero] continuation before) called_world) ->
  gateway_copyout_pair_birth backend resources ipc object before called_world helper_events after returned_world identity ->
  gateway_steps backend (Clight.globalenv prog)
    (gateway_live (Returnstate (Vint Int.zero) continuation after) returned_world) suffix (gateway_live target next) ->
  exists ordinal, (length prefix <= ordinal < length prefix + length helper_events)%nat /\
    gateway_copyout_pair_slice backend resources ipc object source world events target next identity ordinal.
Proof.
  intros CONTINUATION EVENTS PREFIX
    (local_prefix & local_suffix & called & call_world & born & born_world & observed & receipt & IDENTITY &
      LOCAL_EVENTS & LOCAL_PREFIX & OPERATION & LEFT & RIGHT & LOCAL_SUFFIX) SUFFIX.
  exists (length prefix + length local_prefix)%nat; split.
  - rewrite LOCAL_EVENTS, length_app; cbn; lia.
  - exists (prefix ++ local_prefix), (local_suffix ++ suffix),
      (plug_cont (pair_socket_cont (Vptr object Ptrofs.zero)) continuation), called, call_world, born, born_world,
      observed, receipt.
    split; [exact IDENTITY |]. split; [apply length_app |]. split.
    + rewrite EVENTS, LOCAL_EVENTS; repeat rewrite <- app_assoc; reflexivity.
    + split.
      * eapply gateway_steps_append; [exact PREFIX |].
        exact (gateway_plug_steps backend (Clight.globalenv prog) _ _ _ continuation CONTINUATION LOCAL_PREFIX).
      * split; [exact OPERATION |]. split; [exact LEFT |]. split; [exact RIGHT |].
        eapply gateway_steps_append; [|exact SUFFIX].
        exact (gateway_plug_steps backend (Clight.globalenv prog) _ _ _ continuation CONTINUATION LOCAL_SUFFIX).
Qed.

Definition gateway_copyout_pairs_slice_ordered {World Event} (backend : gateway_backend World Event) resources ipc
    data control source world events target next (data_identity control_identity : gateway_pair_identity ipc) : Prop :=
  exists data_ordinal control_ordinal, (data_ordinal < control_ordinal)%nat /\
    gateway_copyout_pair_slice backend resources ipc data source world events target next data_identity data_ordinal /\
    gateway_copyout_pair_slice backend resources ipc control source world events target next control_identity control_ordinal.

Lemma gateway_copyout_pair_slice_append {World Event} (backend : gateway_backend World Event) resources ipc
    object source world prefix middle current suffix target next identity ordinal :
  gateway_copyout_pair_slice backend resources ipc object source world prefix middle current identity ordinal ->
  gateway_steps backend (Clight.globalenv prog) (gateway_live middle current) suffix (gateway_live target next) ->
  gateway_copyout_pair_slice backend resources ipc object source world (prefix ++ suffix) target next identity ordinal.
Proof.
  intros (leading & rest & continuation & called & call_world & born & born_world & observed & receipt &
    IDENTITY & INDEX & EVENTS & PREFIX & OPERATION & LEFT & RIGHT & REST) SUFFIX.
  exists leading, (rest ++ suffix), continuation, called, call_world, born, born_world, observed, receipt.
  split; [exact IDENTITY |]. split; [exact INDEX |]. split.
  - rewrite EVENTS; repeat rewrite <- app_assoc; reflexivity.
  - split; [exact PREFIX |]. split; [exact OPERATION |]. split; [exact LEFT |]. split; [exact RIGHT |].
    eapply gateway_steps_append; eassumption.
Qed.

Lemma gateway_copyout_pairs_slice_ordered_append {World Event} (backend : gateway_backend World Event) resources ipc
    data control source world prefix middle current suffix target next data_identity control_identity :
  gateway_copyout_pairs_slice_ordered backend resources ipc data control source world prefix middle current
    data_identity control_identity ->
  gateway_steps backend (Clight.globalenv prog) (gateway_live middle current) suffix (gateway_live target next) ->
  gateway_copyout_pairs_slice_ordered backend resources ipc data control source world (prefix ++ suffix) target next
    data_identity control_identity.
Proof.
  intros (data_ordinal & control_ordinal & ORDER & DATA & CONTROL) SUFFIX.
  exists data_ordinal, control_ordinal; split; [exact ORDER |]. split;
    eapply gateway_copyout_pair_slice_append; eassumption.
Qed.

Lemma gateway_copyout_pair_slice_prepend {World Event} (backend : gateway_backend World Event) resources ipc
    object source world leading following current events target next identity ordinal :
  gateway_steps backend (Clight.globalenv prog) (gateway_live source world) leading (gateway_live following current) ->
  gateway_copyout_pair_slice backend resources ipc object following current events target next identity ordinal ->
  gateway_copyout_pair_slice backend resources ipc object source world (leading ++ events) target next identity
    (length leading + ordinal).
Proof.
  intros LEADING (prefix & suffix & continuation & called & call_world & born & born_world & observed & receipt &
    IDENTITY & INDEX & EVENTS & PREFIX & OPERATION & LEFT & RIGHT & REST).
  exists (leading ++ prefix), suffix, continuation, called, call_world, born, born_world, observed, receipt.
  split; [exact IDENTITY |]. split; [rewrite length_app, INDEX; reflexivity |]. split.
  - rewrite EVENTS, app_assoc; reflexivity.
  - split; [eapply gateway_steps_append; eassumption |].
    split; [exact OPERATION |]. split; [exact LEFT |]. split; assumption.
Qed.

Lemma gateway_copyout_pairs_slice_ordered_prepend {World Event} (backend : gateway_backend World Event) resources ipc
    data control source world leading following current events target next data_identity control_identity :
  gateway_steps backend (Clight.globalenv prog) (gateway_live source world) leading (gateway_live following current) ->
  gateway_copyout_pairs_slice_ordered backend resources ipc data control following current events target next
    data_identity control_identity ->
  gateway_copyout_pairs_slice_ordered backend resources ipc data control source world (leading ++ events) target next
    data_identity control_identity.
Proof.
  intros LEADING (data_ordinal & control_ordinal & ORDER & DATA & CONTROL).
  exists (length leading + data_ordinal)%nat, (length leading + control_ordinal)%nat; split; [lia |]. split;
    eapply gateway_copyout_pair_slice_prepend; eassumption.
Qed.
