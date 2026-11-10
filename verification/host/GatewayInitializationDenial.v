(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Actual active/completed guards exclude every later helper call. *)
From Stdlib Require Import ZArith List Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayInitializationSource
  GatewayBindings GatewayRuntimeABI GatewayReturnBarrier GatewaySymbolicBarrier.
Open Scope Z_scope.

Definition initialization_denial_api identifier := Pos.eqb identifier _PyErr_SetString.
Definition initialization_active_guard := match initialization_active_check with
  Ssequence _ guard => guard | _ => Sskip end.
Definition initialization_complete_guard := match initialization_complete_check with
  Ssequence _ guard => guard | _ => Sskip end.

Theorem actual_initialization_denial_bindings :
  gateway_barrier_bindings (Clight.globalenv prog) empty_env initialization_denial_api
    (Internal f_host_initialize).
Proof.
  intros identifier ALLOWED; apply Pos.eqb_eq in ALLOWED; subst identifier.
  split; [reflexivity |].
  assert (BOUND : gateway_function_binding (Clight.globalenv prog) _PyErr_SetString gateway_set_error_definition).
  { apply gateway_actual_function_binding; vm_compute; reflexivity. }
  destruct BOUND as [symbol [SYMBOL FUNCTION]].
  exists symbol, gateway_set_error_definition; split; [exact SYMBOL |]. split; [exact FUNCTION |].
  split.
  - do 4 eexists; reflexivity.
  - discriminate.
Qed.

Theorem actual_initialization_guard_excludes_helper {World Event} (backend : gateway_backend World Event)
    (completed : bool) temporaries word before world events arguments continuation after next :
  temporaries ! (if completed then _t'4 else _t'6) = Some (Vint word) -> word <> Int.zero ->
  gateway_steps backend (Clight.globalenv prog)
    (gateway_live (State f_PyInit__host
      (if completed then initialization_complete_guard else initialization_active_guard)
      (Kseq (if completed then initialization_after_complete else initialization_after_active) Kstop)
      empty_env temporaries before) world) events
    (gateway_live (Callstate (Internal f_host_initialize) arguments continuation after) next) -> False.
Proof.
  intros WORD NONZERO RUN.
  eapply gateway_symbolic_barrier_excludes_call with
    (owner := f_PyInit__host) (protected := if completed then _t'4 else _t'6) (word := word)
    (body := if completed then initialization_complete_guard else initialization_active_guard)
    (continuation := Kseq
      (if completed then initialization_after_complete else initialization_after_active) Kstop);
    [exact actual_initialization_denial_bindings |apply Int.eq_false; exact NONZERO |
     exact WORD | |reflexivity |exact RUN].
  destruct completed; vm_compute; tauto.
Qed.
