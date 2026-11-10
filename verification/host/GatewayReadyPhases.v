(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Source phases of actual poll initialization and thread restoration. *)
From compcert Require Import Clight.
From HostGateway Require Import GatewayReadySource.

Definition ready_descriptor_sequence := match ready_after_clock_guard with Ssequence first _ => first | _ => Sskip end.
Definition ready_after_descriptor := match ready_after_clock_guard with Ssequence _ after => after | _ => Sskip end.
Definition ready_descriptor_load := match ready_descriptor_sequence with Ssequence load _ => load | _ => Sskip end.
Definition ready_descriptor_store := match ready_descriptor_sequence with Ssequence _ store => store | _ => Sskip end.
Definition ready_events_store := match ready_after_descriptor with Ssequence first _ => first | _ => Sskip end.
Definition ready_after_events := match ready_after_descriptor with Ssequence _ after => after | _ => Sskip end.
Definition ready_revents_store := match ready_after_events with Ssequence first _ => first | _ => Sskip end.
Definition ready_after_revents := match ready_after_events with Ssequence _ after => after | _ => Sskip end.
Definition ready_save_sequence := match ready_after_revents with Ssequence first _ => first | _ => Sskip end.
Definition ready_after_save := match ready_after_revents with Ssequence _ after => after | _ => Sskip end.
Definition ready_save_call := match ready_save_sequence with Ssequence call _ => call | _ => Sskip end.
Definition ready_save_bind := match ready_save_sequence with Ssequence _ bind => bind | _ => Sskip end.
Definition ready_poll_sequence := match ready_after_save with Ssequence first _ => first | _ => Sskip end.
Definition ready_after_poll := match ready_after_save with Ssequence _ after => after | _ => Sskip end.
Definition ready_poll_call := match ready_poll_sequence with Ssequence call _ => call | _ => Sskip end.
Definition ready_poll_bind := match ready_poll_sequence with Ssequence _ bind => bind | _ => Sskip end.
Definition ready_errno_sequence := match ready_after_poll with Ssequence first _ => first | _ => Sskip end.
Definition ready_after_errno := match ready_after_poll with Ssequence _ after => after | _ => Sskip end.
Definition ready_errno_call := match ready_errno_sequence with Ssequence call _ => call | _ => Sskip end.
Definition ready_errno_bind := match ready_errno_sequence with Ssequence _ bind => bind | _ => Sskip end.
Definition ready_restore_call := match ready_after_errno with Ssequence first _ => first | _ => Sskip end.
Definition ready_after_restore := match ready_after_errno with Ssequence _ after => after | _ => Sskip end.
Definition ready_signals_sequence := match ready_after_restore with Ssequence first _ => first | _ => Sskip end.
Definition ready_after_signals := match ready_after_restore with Ssequence _ after => after | _ => Sskip end.
Definition ready_signals_call := match ready_signals_sequence with Ssequence call _ => call | _ => Sskip end.
Definition ready_signals_test := match ready_signals_sequence with Ssequence _ test => test | _ => Sskip end.
