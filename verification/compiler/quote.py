"""Generate an untrusted typed LTL candidate printer for the pinned OCaml AST."""
# SPDX-License-Identifier: Apache-2.0
# §AR-compiled-reporting.certificate: The kernel validates generated terms and allocation choices.
from pathlib import Path
import re


def constructors(source, name):
    match = re.search(r'\btype '+name+r'\s*=\s*(.*?)(?=\n(?:type |val |module )|\Z)',source,re.S)
    if not match:
        raise ValueError('missing compiler datatype '+name)
    result = []
    for part in match[1].split('|'):
        part = part.strip()
        if not part:
            continue
        value = re.fullmatch(r'(\w+)(?:\s+of\s+(.+))?',part,re.S)
        if not value:
            raise ValueError('unsupported constructor '+part)
        result.append((value[1], re.split(r'\s*\*\s*',value[2]) if value[2] else []))
    return result


def variant(module, name, choices):
    types = {'Int.int':'coqint','Int64.int':'coqint64','Ptrofs.int':'coqptrofs',
             'coq_Z':'coqZ','ident':'positive','condition':'condition',
             'typ':'asttype','addressing':'addressing','comparison':'comparison','float':'coqfloat','float32':'coqsingle'}
    rows = ['let '+name+' p = function']
    for ctor, args in choices:
        variables = ['x'+str(i) for i in range(len(args))]
        pattern = module+'.'+ctor+(' ('+', '.join(variables)+')' if variables else '')
        printers = []
        for typ, variable in zip(args,variables):
            if typ not in types:
                raise ValueError('unsupported compiler field '+typ)
            printers += [types[typ],variable]
        output = '('+module+'.'+ctor+(' '+' '.join('%a' for _ in variables) if variables else '')+')'
        rows.append(' | '+pattern+' -> fprintf p "'+output+'" '+ ' '.join(printers))
    return '\n'.join(rows)+'\n\n'


def printer(source: Path):
    op = (source/'extraction/Op.mli').read_text()
    registers = constructors((source/'extraction/Machregs.mli').read_text(),'mreg')
    result = '''(* Generated untrusted data printer. Kernel validation supplies correctness.
   AST descriptions come from the pinned CompCert source; its notices and
   INRIA Non-Commercial License Agreement apply to that upstream material. *)
open Format
open Camlcoq
open AST
open LTL
open Locations
open Machregs
open ExportBase
let comparison p = function
 | Integers.Ceq -> fprintf p "Integers.Ceq"
 | Integers.Cne -> fprintf p "Integers.Cne"
 | Integers.Clt -> fprintf p "Integers.Clt"
 | Integers.Cle -> fprintf p "Integers.Cle"
 | Integers.Cgt -> fprintf p "Integers.Cgt"
 | Integers.Cge -> fprintf p "Integers.Cge"
'''
    for name in ['condition','addressing','operation']:
        result += variant('Op',name,constructors(op,name))
    result += 'let mreg p = function\n'
    result += '\n'.join(' | Machregs.'+ctor+' -> fprintf p "Machregs.'+ctor+'"' for ctor,_ in registers)+'\n'
    result += '''
let slot p = function
 | Local -> fprintf p "Locations.Local"
 | Incoming -> fprintf p "Locations.Incoming"
 | Outgoing -> fprintf p "Locations.Outgoing"
let loc p = function
 | R r -> fprintf p "(Locations.R %a)" mreg r
 | S(s,o,t) -> fprintf p "(Locations.S %a %a %a)" slot s coqZ o asttype t
let ros p = function
 | Datatypes.Coq_inl r -> fprintf p "(inl %a)" mreg r
 | Datatypes.Coq_inr id -> fprintf p "(inr %a)" positive id
let rec builtin_arg atom p = function
 | BA v -> fprintf p "(BA %a)" atom v
 | BA_int v -> fprintf p "(BA_int %a)" coqint v
 | BA_long v -> fprintf p "(BA_long %a)" coqint64 v
 | BA_float v -> fprintf p "(BA_float %a)" coqfloat v
 | BA_single v -> fprintf p "(BA_single %a)" coqsingle v
 | BA_loadstack(c,o) -> fprintf p "(BA_loadstack %s %a)" (name_of_chunk c) coqptrofs o
 | BA_addrstack o -> fprintf p "(BA_addrstack %a)" coqptrofs o
 | BA_loadglobal(c,id,o) -> fprintf p "(BA_loadglobal %s %a %a)" (name_of_chunk c) positive id coqptrofs o
 | BA_addrglobal(id,o) -> fprintf p "(BA_addrglobal %a %a)" positive id coqptrofs o
 | BA_splitlong(a,b) -> fprintf p "(BA_splitlong %a %a)" (builtin_arg atom) a (builtin_arg atom) b
 | BA_addptr(a,b) -> fprintf p "(BA_addptr %a %a)" (builtin_arg atom) a (builtin_arg atom) b
let rec builtin_res atom p = function
 | BR v -> fprintf p "(BR %a)" atom v
 | BR_none -> fprintf p "BR_none"
 | BR_splitlong(a,b) -> fprintf p "(BR_splitlong %a %a)" (builtin_res atom) a (builtin_res atom) b
let instruction p = function
 | Lop(op,args,res) -> fprintf p "(LTL.Lop %a %a %a)" operation op (print_list mreg) args mreg res
 | Lload(c,a,args,d) -> fprintf p "(LTL.Lload %s %a %a %a)" (name_of_chunk c) addressing a (print_list mreg) args mreg d
 | Lgetstack(s,o,t,d) -> fprintf p "(LTL.Lgetstack %a %a %a %a)" slot s coqZ o asttype t mreg d
 | Lsetstack(r,s,o,t) -> fprintf p "(LTL.Lsetstack %a %a %a %a)" mreg r slot s coqZ o asttype t
 | Lstore(c,a,args,r) -> fprintf p "(LTL.Lstore %s %a %a %a)" (name_of_chunk c) addressing a (print_list mreg) args mreg r
 | Lcall(s,f) -> fprintf p "(LTL.Lcall %a %a)" signatur s ros f
 | Ltailcall(s,f) -> fprintf p "(LTL.Ltailcall %a %a)" signatur s ros f
 | Lbuiltin(ef,args,r) -> fprintf p "(LTL.Lbuiltin %a %a %a)" external_function ef (print_list (builtin_arg loc)) args (builtin_res mreg) r
 | Lbranch s -> fprintf p "(LTL.Lbranch %a)" positive s
 | Lcond(c,args,a,b) -> fprintf p "(LTL.Lcond %a %a %a %a)" condition c (print_list mreg) args positive a positive b
 | Ljumptable(r,t) -> fprintf p "(LTL.Ljumptable %a %a)" mreg r (print_list positive) t
 | Lreturn -> fprintf p "LTL.Lreturn"
let rec code p = function
 | [] -> fprintf p "(PTree.empty _)"
 | (label,block)::rest -> fprintf p "(PTree.set %a %a %a)"
     positive label (print_list instruction) block code rest
let func p f = fprintf p
 "{| LTL.fn_sig := %a; LTL.fn_stacksize := %a; LTL.fn_code := %a; LTL.fn_entrypoint := %a |}"
 signatur f.fn_sig coqZ f.fn_stacksize code (Maps.PTree.elements f.fn_code) positive f.fn_entrypoint
let candidate p (rtl,ltl) = fprintf p
 "{| candidate_entry := %a; candidate_stack := %a; candidate_nodes := %d%%nat; candidate_function := %a |}"
 positive rtl.RTL.fn_entrypoint coqZ rtl.RTL.fn_stacksize
 (List.length (Maps.PTree.elements rtl.RTL.fn_code)) func ltl
let write path candidates =
 let channel = open_out path in
 let p = formatter_of_out_channel channel in
 fprintf p "From Stdlib Require Import ZArith List String.\\nFrom compcert Require Import Integers Floats AST Maps Op Locations Machregs LTL.\\nRequire Import AllocationCandidates.\\nLocal Open Scope string_scope.\\nLocal Open Scope Z_scope.\\nDefinition candidates : list allocation_candidate := %a.\\n"
 (print_list candidate) candidates;
 pp_print_flush p (); close_out channel
'''
    return result
