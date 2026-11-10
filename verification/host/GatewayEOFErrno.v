(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.transport: Individual errno lookups retain the EOF caller's actual buffers. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Ctypes Clight.
From HostGateway Require Import GatewayMachine GatewayRuntime GatewayRuntimeABI GatewayThreadRuntime
  GatewayReadContext GatewayReadMemory GatewayStreamInterface GatewayReadonlyOperations GatewayBufferReference.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_errno_owned_context {World Event}(backend:gateway_backend World Event)io native stable discipline thread_errno
    (thread:gateway_thread_runtime backend io native stable discipline thread_errno)
    stream data stream_offset data_offset initial amount readonly reference owner mode
    before world result after next observed:
  gateway_owned_buffer_context native stable discipline stream data stream_offset data_offset initial amount readonly
    reference owner mode before world->
  gateway_runtime_operation backend gateway_errno_location_definition[]before world result after next observed->
  gateway_owned_buffer_context native stable discipline stream data stream_offset data_offset initial amount readonly
    reference owner mode after next /\io observed=None.
Proof.
  intros[CONTEXT[BUFFER NATIVE]]API.
  destruct(gateway_errno_location_operation _ _ _ _ _ _ thread mode before world result after next observed
    (proj1 CONTEXT)API)
    as[object[offset[VALUE[POINTER[LOAD[NOT_NATIVE[NOT_STABLE[SIDE[ACCESS[FRAME IO]]]]]]]]]].
  split;[|exact IO]. split.
  - eapply gateway_read_context_preserved;[exact CONTEXT|exact SIDE|exact ACCESS|exact FRAME].
  - split.
    + eapply gateway_buffer_reference_transitive;[exact BUFFER|]. split.
      * eapply gateway_read_context_readonly_frame;[exact CONTEXT|exact FRAME].
      * eapply gateway_context_buffer_permissions;[exact CONTEXT|exact FRAME].
    + eapply gateway_native_reference_transitive;[exact NATIVE|].
      eapply gateway_native_reference_operation;[exact ACCESS|exact FRAME].
Qed.
