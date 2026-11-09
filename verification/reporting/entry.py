#!/usr/bin/env python3
"""Replay accepted reporting proofs in the maintained entry caller's actual source environment."""
# §AR-entry.caller: Current reporting callbacks retain the original proof records and machine types.
import importlib.util
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
DIRECTORY = Path(__file__).resolve().parent
ORIGINAL = ROOT / 'm4/connection'
ROOTS = ('ResultOwnership', 'SenderProgram', 'SenderSuccessfulRuns')
# These interfaces are genuinely generic in the source environment. Reusing them
# also retains exactly the machine/event/address/TLS types used by NamespaceMachine.
SHARED = frozenset(('IO', 'Machine', 'ClightSteps', 'StoreSteps', 'Library', 'LibraryMachine',
    'ProcessEffects', 'LibraryControl', 'Deterministic', 'LocalAccess',
    'ScalarMemory', 'CallContexts', 'WriteMemory', 'WriteBytes', 'GlobalReads', 'CallAccess',
    'FreshMemory', 'FrameRecord', 'FrameBytes', 'DecoderControl', 'DecoderValidity', 'DecoderZeros'))
OVERRIDES = frozenset(('Fault',))
MATCHED_FUNCTIONS = ('error_number', 'write_all', 'put32', 'put64', 'get32', 'get64',
                     'send_frame', 'result_of', 'decode_frame')


def normalize_compat(text):
    return re.sub(r"\b(\w+)Draft\b", lambda match: match[1] if (ORIGINAL / (match[1] + ".v")).is_file() else match[0], text)


def imports(text):
    text = normalize_compat(text)
    return [name for body in re.findall(r'(?<!From )Require Import\s+(.*?)\.', text, re.S)
            for name in body.split()]


def proof_origin(module):
    return DIRECTORY / 'entry' / (module + '.v') if module in OVERRIDES else ORIGINAL / (module + '.v')


def modules():
    ordered, seen = [], set()
    def visit(name):
        if name in seen or name in SHARED:
            return
        path = proof_origin(name)
        if not path.is_file():
            return
        seen.add(name)
        for dependency in imports(path.read_text()):
            visit(dependency)
        ordered.append(name)
    for root in ROOTS:
        visit(root)
    return tuple(ordered)


def proof_text(module):
    selected = set(modules())
    text = normalize_compat(proof_origin(module).read_text())
    text = text.replace('Slice.prog', 'EntrySource.prog')
    def imports_replacement(match):
        names = match[1].split()
        shared = [name for name in names if name != 'Slice' and name not in selected]
        current = [name for name in names if name in selected]
        return ('Require Import ' + ' '.join(shared) + '.\n' if shared else '') + (
            'From EntryReporting Require Import ' + ' '.join(current) + '.\n' if current else '')
    text = re.sub(r'(?<!From )Require Import\s+(.*?)\.', imports_replacement, text, flags=re.S)
    text = text.replace('Import ListNotations.',
                        'From EntryNative Require Import EntrySource.\nImport ListNotations.', 1)
    if 'From EntryNative Require Import EntrySource.' not in text:
        text = 'From EntryNative Require Import EntrySource.\n' + text
    for name in selected:
        text = re.sub(r'(?<![\w.])' + re.escape(name) + r'\.(?=[A-Za-z_])', 'EntryReporting.' + name + '.', text)
    if module == 'ResultLayout':
        text += '''\nLemma current_result_composite : exists co,
  (genv_cenv result_ge)!_result=Some co /\\co_members co=
  [Member_plain _kind tuint;Member_plain _stage tuint;Member_plain _detail tuint;
   Member_plain _entry tuint;Member_plain _clean tuint;Member_plain _triggers tuint;
   Member_plain _uid tuint;Member_plain _run tulong;Member_plain _cpu tulong;
   Member_plain _peak tulong;Member_plain _out tulong;Member_plain _err tulong;
   Member_plain _elapsed tulong;Member_plain _oom tulong;Member_plain _pids tulong;
   Member_plain _export_state tuint;Member_plain _omitted tuint;Member_plain _export_error tuint;
   Member_plain _export_digest(tarray tuchar 32)].
Proof.
  assert(MEMBERS:result_members=
  [Member_plain _kind tuint;Member_plain _stage tuint;Member_plain _detail tuint;
   Member_plain _entry tuint;Member_plain _clean tuint;Member_plain _triggers tuint;
   Member_plain _uid tuint;Member_plain _run tulong;Member_plain _cpu tulong;
   Member_plain _peak tulong;Member_plain _out tulong;Member_plain _err tulong;
   Member_plain _elapsed tulong;Member_plain _oom tulong;Member_plain _pids tulong;
   Member_plain _export_state tuint;Member_plain _omitted tuint;Member_plain _export_error tuint;
   Member_plain _export_digest(tarray tuchar 32)])by reflexivity.
  unfold result_members in MEMBERS.
  destruct((genv_cenv result_ge)!_result)as[co|]eqn:LOOKUP.
  - exists co;split;[reflexivity|exact MEMBERS].
  - discriminate.
Qed.\n'''
    if module == 'ResultLayout':
        text += '''\nRequire Import LocalAccess LibraryMachine.
From compcert Require Import Globalenvs.
Lemma current_result_field_location e le m a field ty object offset delta:
  expression_value result_ge e le m a(Vptr object offset) ->typeof a=result_type ->
  field_offset result_ge field result_members=OK(delta,Full) ->
  location_value result_ge e le m(Efield a field ty)object(Ptrofs.add offset(Ptrofs.repr delta)).
Proof.
  intros VALUE TYPE OFFSET;destruct current_result_composite as[co[COMPOSITE MEMBERS]].
  assert(ACTUAL:co_members co=result_members).
  { unfold result_members;rewrite COMPOSITE;reflexivity. }
  eapply struct_location_value with(co:=co);[exact VALUE|exact TYPE|exact COMPOSITE|rewrite ACTUAL;exact OFFSET].
Qed.
Definition current_symbol id:=match Genv.find_symbol result_ge id with Some object=>object|None=>1%positive end.
'''
        for name in ('put32', 'put64', 'memcpy', 'fault', 'write_all'):
            definition = 'memcpy_definition' if name == 'memcpy' else '(Internal f_' + name + ')'
            text += f'''Lemma current_symbol_{name}:Genv.find_symbol result_ge _{name}=Some(current_symbol _{name}).
Proof. reflexivity. Qed.
Lemma current_function_{name}:Genv.find_funct result_ge(Vptr(current_symbol _{name})Ptrofs.zero)=Some {definition}.
Proof. reflexivity. Qed.\n'''
        text += 'Global Opaque current_symbol.\n'
    if module == 'SenderAccess':
        text = text.replace('eapply struct_location_value;[sender_expression|reflexivity|reflexivity|reflexivity]',
                            'eapply current_result_field_location;[sender_expression|reflexivity|reflexivity]')
        text = text.replace('eapply struct_location_value;[sender_expression|reflexivity|reflexivity|exact FIELD]',
                            'eapply current_result_field_location;[sender_expression|reflexivity|exact FIELD]')
        begin = text.index('Proof.', text.index('Theorem sender_encoding_symbols'))
        end = text.index('Qed.', begin) + 4
        text = text[:begin] + '''Proof.
  exists(current_symbol _put32),(current_symbol _put64),(current_symbol _memcpy).
  split;[exact current_symbol_put32|]. split;[exact current_function_put32|].
  split;[exact current_symbol_put64|]. split;[exact current_function_put64|].
  split;[exact current_symbol_memcpy|exact current_function_memcpy].
Qed.''' + text[end:]
    if module == 'SenderGuards':
        begin = text.index('Proof.', text.index('Theorem sender_report_symbols'))
        end = text.index('Qed.', begin) + 4
        text = text[:begin] + '''Proof.
  exists(current_symbol _fault),(current_symbol _write_all).
  split;[exact current_symbol_fault|]. split;[exact current_function_fault|].
  split;[exact current_symbol_write_all|exact current_function_write_all].
Qed.''' + text[end:]
    if module == 'ResultSource':
        text = text.replace('eapply struct_location_value; [result_expression|reflexivity|reflexivity|reflexivity]',
            'lazymatch goal with COMPOSITE : (genv_cenv ?ge)!?id=Some ?co, MEMBERS : co_members ?co=_ |- _ => eapply struct_location_value with(co:=co); [result_expression|reflexivity|exact COMPOSITE|rewrite MEMBERS;reflexivity] end')
        text = text.replace('  eapply store_next; [exact PM|apply result_source_entry; exact ALLOC|].',
            '  destruct current_result_composite as[co[COMPOSITE MEMBERS]].\n  eapply store_next; [exact PM|apply result_source_entry; exact ALLOC|].')
    if module == 'CallEvents':
        start = text.index('Proof.', text.index('Theorem fault_events_are_selectors'))
        stop = text.index('Qed.', start) + 4
        text = text[:start] + '''Proof.
  intros ge cell m mode name xs ys SYMBOLS INPUT.
  eapply source_path_event_contract with(count:=2%nat).
  - apply production_fault_path.
  - exact I.
  - exact I.
  - apply return_event_contract;exact I.
Qed.''' + text[stop:]
    if module == 'SenderSelectors':
        old = 'Definition report_matches mode_bytes tag := match compare_bytes mode_bytes (report_name tag) with Eq=>true|_=>false end.'
        if text.count(old) != 1:
            raise ValueError('production selector adapter no longer matches')
        text = text.replace(old, 'Definition report_matches (mode_bytes:list Byte.int) (tag:report_fault) := false.')
        begin = text.index('Theorem report_matches_exact')
        end = text.index('Theorem report_names_distinct', begin)
        text = text[:begin] + text[end:]
        begin = text.index('Proof.', text.index('Theorem report_selection_unique'))
        end = text.index('Qed.', begin) + 4
        text = text[:begin] + '''Proof.
  intros fd r mode_bytes a b A B;unfold report_selected,report_matches in A.
  rewrite Bool.andb_false_r in A;discriminate.
Qed.''' + text[end:]
    def shared_computations(match):
        body = match[1]
        for name, qualified in (('put32_values', 'Writers.put32_values'),
                                ('put64_values', 'Writers.put64_values'),
                                ('cell32', 'ResultLayout.cell32'), ('cell64', 'ResultLayout.cell64')):
            if re.search(r'\b' + name + r'\b', body) and qualified not in body.split():
                body += ' ' + qualified
        return 'cbn [' + body + ']'
    text = re.sub(r'cbn\s*\[([^\]]*)\]', shared_computations, text)
    return text


def validate_source(current):
    spec = importlib.util.spec_from_file_location('entry_identifier_adapter', DIRECTORY / 'source.py')
    adapter = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(adapter)
    reference_path = ROOT / '.tools/m4/bridge/source/Slice.v'
    predecessor = json.loads((ROOT / 'assurance/m4-frames-evidence.json').read_text())
    if hashlib.sha256(reference_path.read_bytes()).hexdigest() != predecessor['replayed_sources_sha256']['Slice.v']:
        raise ValueError('reporting reference AST differs from accepted preserved evidence')
    reference = reference_path.read_text()
    current = Path(current).read_text()
    mappings = {}
    for name in MATCHED_FUNCTIONS:
        pattern = rf'^Definition f_{name} :=.*?^\|\}}\.'
        old, new = re.search(pattern, reference, re.S | re.M), re.search(pattern, current, re.S | re.M)
        if old is None or new is None:
            raise ValueError('missing reporting function: ' + name)
        canonical = lambda value: adapter.LITERAL.sub('_STRING', adapter.TEMP.sub('_TEMP', value)).split()
        if canonical(old[0]) != canonical(new[0]):
            raise ValueError('reporting function changed beyond identifiers: ' + name)
        temporary = adapter.checked_bijection(zip(adapter.TEMP.findall(old[0]), adapter.TEMP.findall(new[0])), 'temporary')
        literals = adapter.checked_bijection(zip(adapter.LITERAL.findall(old[0]), adapter.LITERAL.findall(new[0])), 'string')
        old_globals, new_globals = adapter.literal_globals(reference), adapter.literal_globals(current)
        for left, right in literals.items():
            if old_globals[left] != new_globals[right]:
                raise ValueError('reporting literal bytes/type/flags changed: ' + left)
        mapping = {left:right for left,right in (temporary | literals).items() if left != right}
        if mapping:
            raise ValueError('reporting proof adaptation requires reviewed nonidentity mapping: ' + name)
        if old[0].split() != new[0].split():
            raise ValueError('reporting function differs after identity check: ' + name)
        mappings[name] = mapping
    return mappings
