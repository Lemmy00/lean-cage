(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The real format and keyword tables define the public call shapes. *)
From Stdlib Require Import ZArith List Lia String Ascii.
From compcert Require Import Coqlib Integers AST Values Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayRegistry GatewayKeywordCode.
Import ListNotations.
Open Scope Z_scope.

Fixpoint gateway_keyword_text(text:string):list Z:=match text with
  |EmptyString=>[]|String character rest=>Z.of_nat(nat_of_ascii character)::gateway_keyword_text rest end.

Definition gateway_constructor_plan:gateway_keyword_plan:={|
  gateway_keyword_names:=map gateway_keyword_text["bundle"%string;"results"%string];
  gateway_keyword_required:=0;gateway_keyword_only:=false;gateway_keyword_label:=gateway_keyword_text "Workspace"|}.
Definition gateway_execute_plan(run:bool):gateway_keyword_plan:={|
  gateway_keyword_names:=map gateway_keyword_text
    (["policy"%string;"workspace"%string;"stdin"%string;"output"%string;"cancellation"%string;"timeout"%string]++
      if run then["_test_fault"%string]else[]);
  gateway_keyword_required:=1;gateway_keyword_only:=true;
  gateway_keyword_label:=gateway_keyword_text(if run then"run"else"check")|}.
Definition gateway_single_plan(name label:string):gateway_keyword_plan:={|
  gateway_keyword_names:=[gateway_keyword_text name];gateway_keyword_required:=1;gateway_keyword_only:=false;
  gateway_keyword_label:=gateway_keyword_text label|}.
Definition gateway_validate_plan:=gateway_single_plan "policy" "validate".
Definition gateway_report_plan:=gateway_single_plan "request" "report".
Definition gateway_cancellation_plan:gateway_keyword_plan:={|
  gateway_keyword_names:=[];gateway_keyword_required:=0;gateway_keyword_only:=false;
  gateway_keyword_label:=gateway_keyword_text "Cancellation"|}.
Definition gateway_outcome_plan:gateway_keyword_plan:={|
  gateway_keyword_names:=map gateway_keyword_text
    ["request_id"%string;"bundle_id"%string;"command"%string;"status"%string;"report"%string;
     "exit_code"%string;"vm_cleanup"%string;"error"%string;"stdout"%string;"stderr"%string;
     "files"%string;"output"%string;"publication"%string;"publication_error"%string];
  gateway_keyword_required:=7;gateway_keyword_only:=false;gateway_keyword_label:=gateway_keyword_text "Outcome"|}.
Definition gateway_cli_plan:gateway_keyword_plan:={|
  gateway_keyword_names:=[gateway_keyword_text "argv"];gateway_keyword_required:=0;gateway_keyword_only:=false;
  gateway_keyword_label:=gateway_keyword_text "cli"|}.

Fixpoint gateway_registered_keyword_names(initial:list init_data)(names:list(list Z)):Prop:=
  match initial,names with
  |[Init_int64 value],[]=>value=Int64.zero
  |Init_addrof identifier offset::rest,name::others=>offset=Ptrofs.zero /\
    (match gateway_program_definition identifier global_definitions with
     |Some(Gvar variable)=>registered_string variable name|_=>False end) /\
    gateway_registered_keyword_names rest others
  |_,_=>False end.
Definition gateway_registered_keyword_format(variable:globvar type)(plan:gateway_keyword_plan):Prop:=
  registered_string variable(map Byte.unsigned(gateway_keyword_format plan)).

Theorem actual_constructor_keyword_names:
  gateway_registered_keyword_names(gvar_init v_names)(gateway_keyword_names gateway_constructor_plan).
Proof. repeat split;reflexivity. Qed.
Theorem actual_execute_keyword_names(run:bool):
  gateway_registered_keyword_names(gvar_init(if run then v_run_names else v_check_names))
    (gateway_keyword_names(gateway_execute_plan run)).
Proof. destruct run;repeat split;reflexivity. Qed.
Theorem actual_validate_keyword_names:
  gateway_registered_keyword_names(gvar_init v_names__1)(gateway_keyword_names gateway_validate_plan).
Proof. repeat split;reflexivity. Qed.
Theorem actual_report_keyword_names:
  gateway_registered_keyword_names(gvar_init v_names__2)(gateway_keyword_names gateway_report_plan).
Proof. repeat split;reflexivity. Qed.
Theorem actual_cancellation_keyword_names:
  gateway_registered_keyword_names(gvar_init v_names__3)(gateway_keyword_names gateway_cancellation_plan).
Proof. reflexivity. Qed.
Theorem actual_outcome_keyword_names:
  gateway_registered_keyword_names(gvar_init v_names__4)(gateway_keyword_names gateway_outcome_plan).
Proof. repeat split;reflexivity. Qed.
Theorem actual_cli_keyword_names:
  gateway_registered_keyword_names(gvar_init v_names__5)(gateway_keyword_names gateway_cli_plan).
Proof. repeat split;reflexivity. Qed.

Theorem actual_constructor_keyword_format:
  gateway_registered_keyword_format v___stringlit_34 gateway_constructor_plan.
Proof. reflexivity. Qed.
Theorem actual_execute_keyword_format(run:bool):
  gateway_registered_keyword_format(if run then v___stringlit_60 else v___stringlit_59)(gateway_execute_plan run).
Proof. destruct run;reflexivity. Qed.

Theorem actual_public_keyword_plans_valid:
  Forall gateway_keyword_plan_valid
    [gateway_constructor_plan;gateway_execute_plan true;gateway_execute_plan false;
     gateway_validate_plan;gateway_report_plan;gateway_cancellation_plan;gateway_outcome_plan;gateway_cli_plan].
Proof.
  unfold gateway_keyword_plan_valid;cbn;
    repeat constructor;cbn;intuition(try discriminate;try lia).
Qed.
