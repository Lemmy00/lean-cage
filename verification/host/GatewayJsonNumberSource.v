(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: JSON numeric lexical and conversion frontiers are selected from the actual native body. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayFailurePaths.
Import ListNotations.

Definition json_number_first body := match body with Ssequence first _ => first | _ => Sskip end.
Definition json_number_rest body := match body with Ssequence _ rest => rest | _ => Sskip end.
Definition json_number_then body := match body with Sifthenelse _ first _ => first | _ => Sskip end.
Definition json_number_else body := match body with Sifthenelse _ _ second => second | _ => Sskip end.
Definition json_number_index := json_number_first (fn_body f_host_json_number).
Definition json_number_after_index := json_number_rest (fn_body f_host_json_number).
Definition json_number_sign := json_number_first json_number_after_index.
Definition json_number_after_sign := json_number_rest json_number_after_index.
Definition json_number_sign_increment := json_number_first json_number_after_sign.
Definition json_number_after_increment := json_number_rest json_number_after_sign.
Definition json_number_digits := json_number_first json_number_after_increment.
Definition json_number_after_digits := json_number_rest json_number_after_increment.
Definition json_number_empty := json_number_first json_number_after_digits.
Definition json_number_after_empty := json_number_rest json_number_after_digits.
Definition json_number_integer := json_number_first json_number_after_empty.
Definition json_number_after_integer := json_number_rest json_number_after_empty.
Definition json_number_integer_load := json_number_first json_number_integer.
Definition json_number_integer_select := json_number_rest json_number_integer.
Definition json_number_nonzero := json_number_else json_number_integer_select.
Definition json_number_nonzero_guard := json_number_first json_number_nonzero.
Definition json_number_integer_loop := json_number_rest json_number_nonzero.
Definition json_number_integer_end := json_number_first json_number_after_integer.
Definition json_number_after_integer_end := json_number_rest json_number_after_integer.
Definition json_number_fraction := json_number_first json_number_after_integer_end.
Definition json_number_after_fraction := json_number_rest json_number_after_integer_end.
Definition json_number_fraction_branch := json_number_then (json_number_rest json_number_fraction).
Definition json_number_fraction_loop := json_number_first (json_number_rest json_number_fraction_branch).
Definition json_number_fraction_guard := json_number_rest (json_number_rest json_number_fraction_branch).
Definition json_number_exponent := json_number_first json_number_after_fraction.
Definition json_number_after_exponent := json_number_rest json_number_after_fraction.
Definition json_number_exponent_branch := json_number_then (json_number_rest json_number_exponent).
Definition json_number_exponent_after_marker := json_number_rest json_number_exponent_branch.
Definition json_number_exponent_after_sign := json_number_rest json_number_exponent_after_marker.
Definition json_number_exponent_after_position := json_number_rest json_number_exponent_after_sign.
Definition json_number_exponent_loop := json_number_first json_number_exponent_after_position.
Definition json_number_exponent_guard := json_number_rest json_number_exponent_after_position.
Definition json_number_complete := json_number_first json_number_after_exponent.
Definition json_number_after_complete := json_number_rest json_number_after_exponent.
Definition json_number_float_select := json_number_first json_number_after_complete.
Definition json_number_integer_construction := json_number_rest json_number_after_complete.
Definition json_number_float_construction := json_number_then json_number_float_select.
Definition json_number_decode_call := json_number_first (json_number_first json_number_float_construction).
Definition json_number_long_call := json_number_first (json_number_first json_number_integer_construction).
Definition json_number_invalid_body := match find_label _invalid (fn_body f_host_json_number) Kstop with
  Some (body, _) => body | _ => Sskip end.
Definition json_number_invalid_cont := match find_label _invalid (fn_body f_host_json_number) Kstop with
  Some (_, continuation) => continuation | _ => Kstop end.

Theorem actual_json_number_lexical_shape :
  json_number_index = Sset _index (Ecast (Econst_int Int.zero Ctypesdefs.tint) Ctypesdefs.tulong) /\
  json_number_digits = Sset _digits (Etempvar _index Ctypesdefs.tulong) /\
  json_number_integer_end = Sset _integer_end (Etempvar _index Ctypesdefs.tulong) /\
  json_number_fraction_loop = Sloop
    (match json_number_fraction_loop with Sloop body _ => body | _ => Sskip end) Sskip /\
  json_number_exponent_loop = Sloop
    (match json_number_exponent_loop with Sloop body _ => body | _ => Sskip end) Sskip /\
  json_number_complete = Sifthenelse
    (Ebinop Cop.One (Etempvar _index Ctypesdefs.tulong) (Etempvar _size Ctypesdefs.tulong) Ctypesdefs.tint)
    (Sgoto _invalid) Sskip.
Proof. repeat split; reflexivity. Qed.

Theorem actual_json_number_construction_shape :
  json_number_long_call = Scall (Some _t'15)
    (Evar _PyLong_FromLong (Tfunction [Ctypesdefs.tlong] (Ctypesdefs.tptr (Tstruct __object noattr)) cc_default))
    [Econst_int Int.zero Ctypesdefs.tint] /\
  json_number_decode_call = Scall (Some _t'13)
    (Evar _PyUnicode_DecodeUTF8 (Tfunction [Ctypesdefs.tptr Ctypesdefs.tschar; Ctypesdefs.tlong; Ctypesdefs.tptr Ctypesdefs.tschar]
      (Ctypesdefs.tptr (Tstruct __object noattr)) cc_default))
    [Etempvar _bytes (Ctypesdefs.tptr Ctypesdefs.tschar); Ecast (Etempvar _size Ctypesdefs.tulong) Ctypesdefs.tlong;
     Evar ___stringlit_8 (Ctypesdefs.tarray Ctypesdefs.tschar 7)].
Proof. split; reflexivity. Qed.

Theorem gateway_json_number_invalid_null parameters memory :
  gateway_null_source (State f_host_json_number json_number_invalid_body json_number_invalid_cont empty_env parameters memory).
Proof.
  left; split; [repeat eexists; reflexivity |]. split; [reflexivity |].
  right; split; [vm_compute; reflexivity |vm_compute; intuition congruence].
Qed.

Theorem gateway_json_number_invalid_lookup :
  find_label _invalid (fn_body f_host_json_number) Kstop = Some (json_number_invalid_body, json_number_invalid_cont).
Proof. reflexivity. Qed.

Theorem gateway_json_number_invalid_denied {World Event} (backend : gateway_backend World Event) ge
    continuation parameters memory :
  call_cont continuation = Kstop ->
  gateway_failure_result backend ge (State f_host_json_number (Sgoto _invalid) continuation empty_env parameters memory).
Proof.
  intro STOP.
  eapply gateway_failure_edge with (target := State f_host_json_number json_number_invalid_body json_number_invalid_cont empty_env parameters memory).
  - cbn; tauto.
  - intros available; split; [exact I |]. split.
    + apply step_goto; rewrite STOP; exact gateway_json_number_invalid_lookup.
    + intros trace target REAL; inversion REAL; subst;
        try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
      match goal with FOUND : find_label _ _ _ = Some _ |- _ =>
        rewrite STOP, gateway_json_number_invalid_lookup in FOUND; inversion FOUND; subst end.
      split; reflexivity.
  - intros before world events value after next RUN.
    assert (NULL : gateway_null_state (gateway_live
      (State f_host_json_number json_number_invalid_body json_number_invalid_cont empty_env parameters before) world))
      by (apply gateway_json_number_invalid_null).
    assert (PRESERVED : forall first observed last, gateway_steps backend ge first observed last ->
      gateway_null_state first -> gateway_null_state last).
    { intros first observed last FLOW; induction FLOW; intros GOOD; [exact GOOD |].
      apply IHFLOW; eapply gateway_null_step; eassumption. }
    pose proof (PRESERVED _ _ _ RUN NULL) as FINAL.
    cbn in FINAL; tauto.
Qed.
