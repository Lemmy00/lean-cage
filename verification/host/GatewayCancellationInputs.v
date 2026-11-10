(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Cancellation uses the actual registered object and signal cell. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Errors
  Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayRegistry.
Import ListNotations.
Open Scope Z_scope.

Definition gateway_cancellation_layout(ge:Clight.genv):Prop:=
  exists composite,(genv_cenv ge)!__9088=Some composite /\
    co_members composite=[Member_plain _ob_base(Tstruct __object noattr);Member_plain _cancelled tint] /\
    field_offset(genv_cenv ge)_cancelled(co_members composite)=OK(16,Full) /\
    sizeof(genv_cenv ge)(Tstruct __9088 noattr)=24.

Lemma actual_cancellation_members:
  option_map(fun composite=>(co_members composite,co_sizeof composite))((prog_comp_env prog)!__9088)=
    Some([Member_plain _ob_base(Tstruct __object noattr);Member_plain _cancelled tint],24).
Proof. vm_compute;reflexivity. Qed.

Theorem actual_cancellation_layout:gateway_cancellation_layout(Clight.globalenv prog).
Proof.
  pose proof actual_cancellation_members as MEMBERS.
  destruct((prog_comp_env prog)!__9088)as[composite|]eqn:LOOK;[|discriminate].
  cbn in MEMBERS;injection MEMBERS as MEMBERS SIZE.
  exists composite;split;[exact LOOK|]. split;[exact MEMBERS|]. split.
  - rewrite MEMBERS;reflexivity.
  - change(match(prog_comp_env prog)!__9088 with Some known=>co_sizeof known|None=>0 end=24).
    rewrite LOOK;exact SIZE.
Qed.

Definition gateway_variable_binding(ge:Clight.genv)identifier variable:Prop:=
  exists symbol,Genv.find_symbol ge identifier=Some symbol /\Genv.find_var_info ge symbol=Some variable.

Lemma gateway_actual_variable_binding identifier variable:
  (prog_defmap prog)!identifier=Some(Gvar variable)->
  gateway_variable_binding(Clight.globalenv prog)identifier variable.
Proof.
  intro DEFINITION.
  destruct((proj1(Genv.find_def_symbol prog identifier(Gvar variable)))DEFINITION)
    as[symbol[SYMBOL VARIABLE]].
  exists symbol;split;[exact SYMBOL|apply Genv.find_var_info_iff;exact VARIABLE].
Qed.

Theorem actual_cli_signal_binding:
  gateway_variable_binding(Clight.globalenv prog)_host_cli_cancelled v_host_cli_cancelled /\
  gvar_init v_host_cli_cancelled=[Init_space 4] /\
  gvar_info v_host_cli_cancelled=tvolatile tint /\
  gvar_readonly v_host_cli_cancelled=false /\gvar_volatile v_host_cli_cancelled=true.
Proof.
  split;[apply gateway_actual_variable_binding;vm_compute;reflexivity|].
  repeat split;reflexivity.
Qed.

(* Volatile values are supplied by the exact volatile-load primitive. Clight
   assigns their global storage Nonempty permission, not ordinary readable bytes. *)
Local Opaque prog.
Theorem actual_cli_signal_storage memory:
  Genv.init_mem prog=Some memory->
  exists symbol,Genv.find_symbol(Clight.globalenv prog)_host_cli_cancelled=Some symbol /\
    Genv.find_var_info(Clight.globalenv prog)symbol=Some v_host_cli_cancelled /\
    Mem.valid_block memory symbol /\Mem.range_perm memory symbol 0 4 Cur Nonempty.
Proof.
  intro INITIAL.
  destruct(proj1 actual_cli_signal_binding)as[symbol[SYMBOL VARIABLE]].
  pose proof(Genv.init_mem_characterization(gv:=v_host_cli_cancelled)(m:=memory)prog symbol VARIABLE INITIAL)
    as[PERMISSIONS REST].
  change(Mem.range_perm memory symbol 0 4 Cur Nonempty)in PERMISSIONS.
  exists symbol;split;[exact SYMBOL|]. split;[exact VARIABLE|]. split.
  - eapply Mem.perm_valid_block with(ofs:=0);apply PERMISSIONS;lia.
  - exact PERMISSIONS.
Qed.

Definition gateway_type_slot(table:globvar type)index code function:Prop:=
  match skipn(3*index)(gvar_init table)with
  |Init_int32 slot::Init_space padding::Init_addrof actual offset::_=>
    slot=Int.repr code /\padding=4 /\actual=function /\offset=Ptrofs.zero
  |_=>False end.

Theorem actual_cancellation_constructor_slots:
  gateway_type_slot v_host_cancellation_slots 0 65 _PyType_GenericNew /\
  gateway_type_slot v_host_cancellation_slots 1 60 _host_cancellation_init /\
  gateway_type_slot v_host_cancellation_slots 2 52 _host_plain_free /\
  gateway_type_slot v_host_cancellation_slots 3 64 _host_cancellation_methods /\
  gateway_type_slot v_host_cancellation_slots 4 73 _host_cancellation_properties.
Proof. repeat split;reflexivity. Qed.

Theorem actual_cancellation_type_size:
  match gvar_init v_host_cancellation_spec with
  |Init_addrof _ _::Init_int32 size::Init_int32 itemsize::Init_int32 flags::Init_space _::Init_addrof slots offset::nil=>
    size=Int.repr 24 /\itemsize=Int.zero /\flags=Int.zero /\
      slots=_host_cancellation_slots /\offset=Ptrofs.zero
  |_=>False end.
Proof. repeat split;reflexivity. Qed.

Theorem actual_cancellation_methods_registered:
  registered_method v_host_cancellation_methods 0 _host_cancellation_cancel 4[99;97;110;99;101;108] /\
  registered_method v_host_cancellation_methods 1 _host_cancellation_is_set 4[105;115;95;115;101;116].
Proof. repeat split;reflexivity. Qed.
