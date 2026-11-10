(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.acceptance: Reject a source profile whose actual calls are stuck on ABI arity. *)
From Stdlib Require Import List Bool.
From compcert Require Import AST Ctypes Cop Clight.
From HostGateway Require Import GatewaySource GatewayRegistry.
Import ListNotations.

Fixpoint gateway_fixed_call_shapes(body:statement):bool:=match body with
  |Scall _ expression arguments=>match classify_fun(typeof expression)with
    |fun_case_f types _ _=>Nat.eqb(length arguments)(length types)|_=>false end
  |Sbuiltin _ _ types arguments=>Nat.eqb(length arguments)(length types)
  |Ssequence first second|Sifthenelse _ first second|Sloop first second=>
    gateway_fixed_call_shapes first&&gateway_fixed_call_shapes second
  |Sswitch _ cases=>gateway_fixed_case_shapes cases
  |Slabel _ source=>gateway_fixed_call_shapes source
  |_=>true end
with gateway_fixed_case_shapes(cases:labeled_statements):bool:=match cases with
  |LSnil=>true|LScons _ body rest=>gateway_fixed_call_shapes body&&gateway_fixed_case_shapes rest end.

Definition gateway_definition_call_shapes(entry:ident*globdef(Ctypes.fundef Clight.function)type):bool:=
  match snd entry with Gfun(Internal function)=>gateway_fixed_call_shapes(fn_body function)|_=>true end.

Theorem actual_gateway_calls_have_fixed_arity:forallb gateway_definition_call_shapes global_definitions=true.
Proof. vm_compute;reflexivity. Qed.

Theorem actual_gateway_function_call_shapes identifier function:
  In(identifier,Gfun(Internal function))(prog_defs prog)->gateway_fixed_call_shapes(fn_body function)=true.
Proof.
  rewrite gateway_actual_program_definitions;intro MEMBER.
  pose proof actual_gateway_calls_have_fixed_arity as ALL;rewrite forallb_forall in ALL.
  exact(ALL _ MEMBER).
Qed.
