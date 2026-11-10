(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: The real initializer derives bootstrap success from its own guard. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayPure GatewayReturns
  GatewayReturnTypes GatewayFailurePaths GatewayBootstrapGuarantee GatewayBootstrapRegions GatewayBootstrapBuffers
  GatewayBootstrapLoaderSetup GatewayBootstrapRuntime GatewayThreadRuntime.
Import ListNotations.
Open Scope Z_scope.

Definition initializer_after_interpreter := match fn_body f_host_initialize with
  Ssequence _ rest => rest | _ => Sskip end.
Definition initializer_bootstrap_sequence := match initializer_after_interpreter with
  Ssequence first _ => first | _ => Sskip end.
Definition initializer_after_bootstrap := match initializer_after_interpreter with
  Ssequence _ rest => rest | _ => Sskip end.
Definition initializer_bootstrap_call := match initializer_bootstrap_sequence with
  Ssequence call _ => call | _ => Sskip end.
Definition initializer_bootstrap_guard := match initializer_bootstrap_sequence with
  Ssequence _ guard => guard | _ => Sskip end.
Definition initializer_bootstrap_denied := match initializer_bootstrap_guard with
  Sifthenelse _ denied _ => denied | _ => Sskip end.
Definition initializer_bootstrap_cont temporaries :=
  Kcall (Some _t'3) f_host_initialize empty_env temporaries
    (Kseq initializer_bootstrap_guard (Kseq initializer_after_bootstrap Kstop)).

Theorem actual_initializer_bootstrap_shape :
  initializer_bootstrap_call = Scall (Some _t'3) (Evar _host_bootstrap (Tfunction [] tint cc_default)) [] /\
  initializer_bootstrap_guard = Sifthenelse (Etempvar _t'3 tint) initializer_bootstrap_denied Sskip.
Proof. split; reflexivity. Qed.

Theorem actual_initializer_bootstrap_call_edge (ge : Clight.genv) temporaries memory symbol :
  Globalenvs.Genv.find_symbol ge _host_bootstrap = Some symbol ->
  Globalenvs.Genv.find_funct_ptr ge symbol = Some (Internal f_host_bootstrap) ->
  store_edge ge
    (State f_host_initialize initializer_bootstrap_call
      (Kseq initializer_bootstrap_guard (Kseq initializer_after_bootstrap Kstop)) empty_env temporaries memory)
    (Callstate (Internal f_host_bootstrap) [] (initializer_bootstrap_cont temporaries) memory).
Proof.
  intros SYMBOL FUNCTION; eapply certified_call_edge with (vf := Vptr symbol Ptrofs.zero).
  - reflexivity.
  - apply old_expression_value; eapply value_function; [reflexivity |exact SYMBOL |reflexivity].
  - apply no_argument_values.
  - cbn; exact FUNCTION.
  - reflexivity.
Qed.

Theorem actual_bootstrap_integer_profile : gateway_int_return_function f_host_bootstrap.
Proof.
  unfold gateway_int_return_function; split; [reflexivity |].
  cbn; unfold gateway_int_return_expression; intuition.
Qed.

Theorem actual_initializer_failed_bootstrap {World Event} (backend : gateway_backend World Event)
    (ge : Clight.genv) temporaries memory :
  gateway_failure_result backend ge
    (Returnstate (Vint (Int.neg Int.one)) (initializer_bootstrap_cont temporaries) memory).
Proof.
  eapply gateway_failure_edge with (target := State f_host_initialize Sskip
    (Kseq initializer_bootstrap_guard (Kseq initializer_after_bootstrap Kstop)) empty_env
    (PTree.set _t'3 (Vint (Int.neg Int.one)) temporaries) memory);
    [cbn; tauto |intros; apply unchanged_store_edge, edge_returnstate |].
  eapply gateway_failure_edge with (target := State f_host_initialize initializer_bootstrap_guard
    (Kseq initializer_after_bootstrap Kstop) empty_env
    (PTree.set _t'3 (Vint (Int.neg Int.one)) temporaries) memory);
    [cbn; tauto |intros; apply unchanged_store_edge, edge_skip_seq |].
  eapply gateway_failure_edge with (target := State f_host_initialize initializer_bootstrap_denied
    (Kseq initializer_after_bootstrap Kstop) empty_env
    (PTree.set _t'3 (Vint (Int.neg Int.one)) temporaries) memory).
  - cbn; tauto.
  - intros; apply certified_if_edge with (v := Vint (Int.neg Int.one)) (b := true);
      [apply old_expression_value, value_temp, PTree.gss |reflexivity].
  - apply gateway_failure_selected; [repeat eexists; reflexivity | |reflexivity].
    vm_compute; intuition congruence.
Qed.

Theorem actual_initializer_undefined_bootstrap ge temporaries memory :
  gateway_blocked_path ge (Returnstate Vundef (initializer_bootstrap_cont temporaries) memory).
Proof.
  eapply gateway_blocked_next with (next := State f_host_initialize Sskip
    (Kseq initializer_bootstrap_guard (Kseq initializer_after_bootstrap Kstop)) empty_env
    (PTree.set _t'3 Vundef temporaries) memory);
    [cbn; tauto |intros; apply unchanged_store_edge, edge_returnstate |].
  eapply gateway_blocked_next with (next := State f_host_initialize initializer_bootstrap_guard
    (Kseq initializer_after_bootstrap Kstop) empty_env (PTree.set _t'3 Vundef temporaries) memory);
    [cbn; tauto |intros; apply unchanged_store_edge, edge_skip_seq |].
  apply gateway_blocked_at; [cbn; tauto |intros; discriminate |].
  intros available trace target STEP; inversion STEP; subst;
    try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
  all: match goal with EVALUATION : eval_expr _ _ _ _ (Etempvar _t'3 tint) ?value |- _ =>
    pose proof (evaluated_unique _ _ _ _ _ _
      (value_temp ge empty_env (PTree.set _t'3 Vundef temporaries) available _t'3 tint Vundef (PTree.gss _ _ _))
      _ EVALUATION) as SAME; subst value end.
  all: discriminate.
Qed.

Theorem actual_initializer_derives_bootstrap_zero {World Event} (backend : gateway_backend World Event)
    ge temporaries before world events returned value after next :
  gateway_int_return_value returned -> value <> Vnullptr ->
  gateway_steps backend ge
    (gateway_live (Returnstate returned (initializer_bootstrap_cont temporaries) before) world)
    events (gateway_live (Returnstate value Kstop after) next) -> returned = Vint Int.zero.
Proof.
  intros [UNDEFINED |[ZERO |FAILED]] NONNULL RUN; [subst returned |exact ZERO |subst returned].
  - exfalso; eapply gateway_blocked_cannot_return; [apply actual_initializer_undefined_bootstrap |exact RUN].
  - exfalso; apply NONNULL.
    exact (actual_initializer_failed_bootstrap backend ge temporaries before before world events value after next RUN).
Qed.

Theorem gateway_actual_initializer_bootstrap {World Event} (backend : gateway_backend World Event)
    io native stable discipline thread_errno module_filename canonicalizes
    (threads : gateway_thread_runtime backend io native stable discipline thread_errno)
    (runtime : gateway_bootstrap_runtime backend io native stable discipline module_filename canonicalizes)
    entry root engine results suffix executable results_literal temporaries before world events value after next :
  Globalenvs.Genv.find_symbol (Clight.globalenv prog) _PyInit__host = Some entry ->
  Globalenvs.Genv.find_symbol (Clight.globalenv prog) _host_root = Some root ->
  Globalenvs.Genv.find_symbol (Clight.globalenv prog) _host_engine = Some engine ->
  Globalenvs.Genv.find_symbol (Clight.globalenv prog) _host_default_results = Some results ->
  Globalenvs.Genv.find_symbol (Clight.globalenv prog) _suffix = Some suffix ->
  Globalenvs.Genv.find_symbol (Clight.globalenv prog) _executable = Some executable ->
  Globalenvs.Genv.find_symbol (Clight.globalenv prog) _results = Some results_literal ->
  gateway_bootstrap_buffers native stable discipline
    (bootstrap_loaded_capacities root engine results suffix executable results_literal)
    (bootstrap_loaded_literals suffix executable results_literal) before world -> value <> Vnullptr ->
  gateway_steps backend (Clight.globalenv prog)
    (gateway_live (Callstate (Internal f_host_bootstrap) [] (initializer_bootstrap_cont temporaries) before) world)
    events (gateway_live (Returnstate value Kstop after) next) ->
  exists prefix rest memory current,
    events = prefix ++ rest /\
    gateway_steps backend (Clight.globalenv prog)
      (gateway_live (Callstate (Internal f_host_bootstrap) [] Kstop before) world) prefix
      (gateway_live (Returnstate (Vint Int.zero) Kstop memory) current) /\
    gateway_steps backend (Clight.globalenv prog)
      (gateway_live (Returnstate (Vint Int.zero) (initializer_bootstrap_cont temporaries) memory) current) rest
      (gateway_live (Returnstate value Kstop after) next) /\
    gateway_bootstrap_named_paths native discipline module_filename canonicalizes entry root engine results memory current.
Proof.
  intros ENTRY ROOT ENGINE RESULTS SUFFIX EXECUTABLE RESULTS_LITERAL INPUT NONNULL RUN.
  destruct (gateway_return_cut backend (Clight.globalenv prog) (Internal f_host_bootstrap) []
    (initializer_bootstrap_cont temporaries) before world events (Returnstate value Kstop after) next I ltac:(cbn; lia) RUN)
    as (prefix & rest & returned & memory & current & EVENTS & BOOTSTRAP & REST).
  pose proof (gateway_actual_int_return backend (Clight.globalenv prog) f_host_bootstrap [] before world prefix returned memory current
    actual_bootstrap_integer_profile BOOTSTRAP) as TYPE.
  pose proof (actual_initializer_derives_bootstrap_zero backend (Clight.globalenv prog) temporaries memory current rest returned
    value after next TYPE NONNULL REST) as ZERO; subst returned.
  exists prefix, rest, memory, current.
  split; [exact EVENTS |]. split; [exact BOOTSTRAP |]. split; [exact REST |].
  eapply actual_bootstrap_call_return;
    [exact threads |exact runtime |exact ENTRY |exact ROOT |exact ENGINE |exact RESULTS |
     exact SUFFIX |exact EXECUTABLE |exact RESULTS_LITERAL |exact INPUT |exact BOOTSTRAP].
Qed.
