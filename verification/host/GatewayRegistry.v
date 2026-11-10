(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Public registration names the maintained native source functions. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Ctypes Ctypesdefs Clight Clightdefs.
From HostGateway Require Import GatewaySource.
Import ListNotations.
Open Scope Z_scope.

Lemma gateway_actual_program_definitions : prog_defs prog=global_definitions.
Proof.
  unfold prog,mkprogram;destruct(build_composite_env' composites Logic.I);reflexivity.
Qed.

Fixpoint gateway_program_definition (wanted:ident)
    (definitions:list(ident*globdef(Ctypes.fundef Clight.function)type)) :
    option(globdef(Ctypes.fundef Clight.function)type) :=
  match definitions with
  |[]=>None
  |(name,definition)::rest=>
    if Pos.eqb wanted name then Some definition else gateway_program_definition wanted rest
  end.

Lemma gateway_program_definition_present wanted definitions definition :
  gateway_program_definition wanted definitions=Some definition ->
  In(wanted,definition)definitions.
Proof.
  induction definitions as[|[name current]rest IH];cbn;[discriminate|].
  destruct(Pos.eqb wanted name)eqn:SAME.
  - apply Pos.eqb_eq in SAME;subst;intro EQUAL;inversion EQUAL;auto.
  - intro FOUND;right;exact(IH FOUND).
Qed.

Definition registered_string (variable:globvar type) characters : Prop :=
  gvar_init variable=map(fun byte=>Init_int8(Int.repr byte))(characters++[0]).

(* Resolve the actual string initializer by its source identifier. String-literal
   numbering and unrelated SDK/global declarations are not interface assumptions. *)
Definition registered_method (table:globvar type) index function flags characters :Prop:=
  match skipn(5*index)(gvar_init table)with
  |Init_addrof name name_offset::Init_addrof actual function_offset::
      Init_int32 convention::Init_space padding::Init_addrof _ _::_=>
    name_offset=Ptrofs.zero /\actual=function /\function_offset=Ptrofs.zero /\
    convention=Int.repr flags /\padding=4 /\
    match gateway_program_definition name global_definitions with
    |Some(Gvar variable)=>registered_string variable characters
    |_=>False
    end
  |_=>False
  end.

Theorem actual_workspace_validate_registered :
  registered_method v_host_workspace_methods 0 _host_workspace_validate 3
    [118;97;108;105;100;97;116;101].
Proof. repeat split;reflexivity. Qed.

Theorem actual_workspace_check_registered :
  registered_method v_host_workspace_methods 1 _host_workspace_check 3 [99;104;101;99;107].
Proof. repeat split;reflexivity. Qed.

Theorem actual_workspace_run_registered :
  registered_method v_host_workspace_methods 2 _host_workspace_run 3 [114;117;110].
Proof. repeat split;reflexivity. Qed.

Theorem actual_workspace_report_registered :
  registered_method v_host_workspace_methods 3 _host_workspace_report 3 [114;101;112;111;114;116].
Proof. repeat split;reflexivity. Qed.

Theorem actual_cli_registered :
  registered_method v_host_module_methods 0 _host_cli 3 [99;108;105].
Proof. repeat split;reflexivity. Qed.

Theorem actual_public_tables_are_program_data :
  In(_host_workspace_methods,Gvar v_host_workspace_methods)(prog_defs prog) /\
  In(_host_module_methods,Gvar v_host_module_methods)(prog_defs prog) /\
  In(_host_workspace_run,Gfun(Internal f_host_workspace_run))(prog_defs prog) /\
  In(_host_workspace_check,Gfun(Internal f_host_workspace_check))(prog_defs prog).
Proof.
  rewrite gateway_actual_program_definitions.
  split;[eapply gateway_program_definition_present;reflexivity|].
  split;[eapply gateway_program_definition_present;reflexivity|].
  split;[eapply gateway_program_definition_present;reflexivity|].
  eapply gateway_program_definition_present;reflexivity.
Qed.
