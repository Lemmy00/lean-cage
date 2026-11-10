(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The loader filename is read from the actual Dl_info field. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Errors
  Ctypes Ctypesdefs Clight.
Require Import ClightSteps StoreSteps LocalAccess.
From HostGateway Require Import GatewaySource GatewayBootstrapSource GatewayBootstrapABI.
Open Scope Z_scope.

Definition gateway_bootstrap_information_layout (ge : Clight.genv) : Prop :=
  exists composite,
    (genv_cenv ge) ! __7533 = Some composite /\
    field_offset (genv_cenv ge) _dli_fname (co_members composite) = OK (0, Full).

Theorem actual_bootstrap_filename_member :
  gateway_bootstrap_information_layout (Clight.globalenv prog).
Proof.
  assert (SOURCE : option_map co_members ((prog_comp_env prog) ! __7533) =
    Some (Member_plain _dli_fname (tptr tschar) :: Member_plain _dli_fbase (tptr tvoid) ::
      Member_plain _dli_sname (tptr tschar) :: Member_plain _dli_saddr (tptr tvoid) :: nil)).
  { vm_compute; reflexivity. }
  change (exists composite, (prog_comp_env prog) ! __7533 = Some composite /\
    field_offset (prog_comp_env prog) _dli_fname (co_members composite) = OK (0, Full)).
  destruct ((prog_comp_env prog) ! __7533) as [composite |] eqn:COMPOSITE; [|discriminate].
  cbn in SOURCE; inversion SOURCE as [MEMBERS].
  exists composite; split; [reflexivity |rewrite MEMBERS; reflexivity].
Qed.

Lemma gateway_bootstrap_information_reference ge temporaries memory information resolved :
  expression_value ge (bootstrap_environment information resolved) temporaries memory
    (Evar _information gateway_loader_information_type) (Vptr information Ptrofs.zero).
Proof.
  eapply location_read_value; [apply local_location_value; reflexivity |].
  apply deref_loc_copy; reflexivity.
Qed.

Theorem gateway_bootstrap_filename_value ge temporaries memory information resolved filename :
  gateway_bootstrap_information_layout ge ->
  Mem.load Mptr memory information 0 = Some filename ->
  expression_value ge (bootstrap_environment information resolved) temporaries memory
    (Efield (Evar _information gateway_loader_information_type) _dli_fname (tptr tschar)) filename.
Proof.
  intros [composite [COMPOSITE FIELD]] LOAD.
  eapply location_read_value.
  - eapply struct_location_value with (id := __7533) (co := composite) (delta := 0).
    + apply gateway_bootstrap_information_reference.
    + reflexivity.
    + exact COMPOSITE.
    + exact FIELD.
  - eapply deref_loc_value; [reflexivity |exact LOAD].
Qed.
