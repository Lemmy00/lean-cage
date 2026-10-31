#!/usr/bin/env python3
"""Replay the isolated bridge experiment without changing reviewed expectations."""
# §AR-m4-bridge.import: Translation, source correspondence and foundations stay distinct.
import argparse
import gzip
import importlib.util
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

from profile import ROOT, DIRECTORY, WORK, digest, flags, lean_run, run, verify_tools

MANIFEST = ROOT / 'assurance/m4-bridge-claims.json'
EVIDENCE = ROOT / 'assurance/m4-bridge-evidence.json'
MODULES = ['BridgeNat', 'BridgeBytes', 'BridgeWords', 'BridgeSource']
ALLOWED_LEAN = {'Classical.choice', 'Quot.sound', 'propext'}
ALLOWED_ROCQ = {
    'ClassicalDedekindReals.sig_not_dec', 'ClassicalDedekindReals.sig_forall_dec',
    'FunctionalExtensionality.functional_extensionality_dep', 'Classical_Prop.classic',
    'Events.external_functions_sem', 'Events.inline_assembly_sem',
}
ALLOWED_UIP = {'eq', 'eq_inst1', 'True', 'HEq', 'HEq_inst1'}


def connection():
    spec = importlib.util.spec_from_file_location('bridge_connection', ROOT / 'm4/connection/check.py')
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def baseline_audits():
    spec = importlib.util.spec_from_file_location('bridge_m3_audit', ROOT / 'scripts/audit_m3.py')
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return [result.M1, result.M2, result]


def sources():
    paths = [p for p in DIRECTORY.iterdir() if p.is_file()]
    paths += [ROOT / 'docs/architecture/AR-m4-bridge.md', ROOT / 'docs/reviews/M4-bridge.md',
              ROOT / 'scripts/m3_axiom_query.lean',
              ROOT / 'm4/Codec.v', ROOT / 'm4/toolchain-lock.json', ROOT / 'assurance/m4-slice.v.gz',
              ROOT / 'assurance/m4-connection-claims.json', ROOT / 'assurance/m4-public-evidence.json']
    previous = connection().sources()
    for audit in baseline_audits():
        previous |= audit.required_sources()
        previous[str(audit.MANIFEST.relative_to(ROOT))] = digest(audit.MANIFEST)
    return dict(sorted((previous | {str(p.relative_to(ROOT)): digest(p) for p in paths}).items()))


def inventory():
    expected = {name + '.v' for name in MODULES} | {'NormalizedImport.v'}
    if {p.name for p in DIRECTORY.glob('*.v')} != expected:
        raise ValueError('missing or unlisted bridge Rocq source')
    if {p.name for p in DIRECTORY.glob('*.lean')} != {'Normalized.lean'}:
        raise ValueError('missing or unlisted bridge Lean source')
    names = []
    for module in MODULES:
        source = re.sub(r'\(\*.*?\*\)', '', (DIRECTORY / (module + '.v')).read_text(), flags=re.S)
        if re.search(r'\b(?:Admitted|admit|Axiom|Parameter|Abort|vm_cast_no_check|native_cast_no_check)\b', source):
            raise ValueError('unfinished or unchecked bridge proof')
        current = re.findall(r'^\s*(?:Theorem|Lemma|Example|Corollary|Fact|Remark|Proposition)\s+(\w+)', source, re.M)
        if not current:
            raise ValueError('empty bridge theorem inventory')
        names += [module + '.' + name for name in current]
    return names


def foundations(output):
    if output.strip() == 'Closed under the global context':
        return [], []
    lines = output.strip().splitlines()
    if not lines or lines[0] != 'Axioms:':
        raise ValueError('unrecognized bridge assumption report: ' + output)
    axioms, uip = set(), set()
    for line in lines[1:]:
        if not line.strip() or line[0].isspace():
            continue
        model = re.fullmatch(r'(\S+) relies on definitional UIP\.', line)
        declaration = re.fullmatch(r'([^\s:]+)(?:\s*:.*)?', line)
        if model:
            uip.add(model.group(1))
        elif declaration:
            axioms.add(declaration.group(1))
        else:
            raise ValueError('unrecognized bridge assumption line: ' + line)
    if not axioms and not uip:
        raise ValueError('empty bridge axiom report')
    axioms, uip = sorted(axioms), sorted(uip)
    if set(axioms) - ALLOWED_ROCQ or set(uip) - ALLOWED_UIP:
        raise ValueError('unreviewed bridge foundation: ' + output)
    return axioms, uip


def validate_claims(expected, actual):
    for key in ['rocq_declarations', 'lean_declarations', 'imported_endpoint', 'export_inventory']:
        if not actual[key] or actual[key] != expected[key]:
            raise ValueError('reviewed bridge statement/foundation/export inventory differs: ' + key)


def lean_inventory():
    # Reuse the established full-type/axiom query, now against the actual imported module.
    query = 'import Normalized\n' + (ROOT / 'scripts/m3_axiom_query.lean').read_text()
    query += '\n#audit_module Normalized\n'
    path = WORK / 'modules/BridgeAudit.lean'
    path.write_text(query)
    result = lean_run(['lean', str(path)])
    records = [json.loads(line.split('LEANCAGE_AUDIT ', 1)[1])
               for line in result.stdout.splitlines() if 'LEANCAGE_AUDIT ' in line]
    inventories = [record['declarations'] for record in records if 'declarations' in record]
    actual = sorted([record for record in records if 'name' in record], key=lambda x: x['name'])
    if len(inventories) != 1 or sorted(inventories[0]) != [r['name'] for r in actual] or not actual:
        raise ValueError('incomplete actual Lean bridge theorem inventory')
    for record in actual:
        if not record['is_theorem'] or set(record['axioms']) - ALLOWED_LEAN:
            raise ValueError('unreviewed Lean bridge theorem/foundation')
        if '...' in record['type'] or '⋯' in record['type']:
            raise ValueError('truncated Lean bridge statement')
    return actual


def export_inventory(path):
    names = {0: ''}
    declarations = []
    metadata = None
    for line in path.read_text().splitlines():
        row = json.loads(line)
        if 'meta' in row:
            metadata = row['meta']
        if 'in' in row:
            value = row.get('str') or row.get('num')
            names[row['in']] = (names[value['pre']] + '.' if value['pre'] else '') + str(value.get('str', value.get('i')))
        for kind in ['def', 'thm', 'opaque', 'axiom']:
            if kind in row:
                declarations.append({'name': names[row[kind]['name']], 'kind': kind})
        if 'inductive' in row:
            declarations += [{'name': names[item['name']], 'kind': kind}
                             for kind in ['types', 'ctors', 'recs'] for item in row['inductive'][kind]]
    if not metadata or metadata['lean']['version'] != '4.35.0':
        raise ValueError('unexpected Lean export version')
    if any(d['kind'] == 'axiom' for d in declarations):
        raise ValueError('the computational decoder closure must contain no exported axiom')
    if 'String' in names.values() or 'UInt32' in names.values():
        raise ValueError('incidental string/UInt32 dependency returned to normalized closure')
    if {'name': 'LeanCageM4.Normalized.decode', 'kind': 'def'} not in declarations:
        raise ValueError('missing actual exported decoder root')
    return {'metadata': metadata, 'declarations': declarations}


def compile_file(path):
    result = run(['rocq', 'c', '-q', *flags(), str(path)], cwd=WORK / 'proofs')
    return result.stdout


def tool_artifacts():
    paths = [WORK / 'opam-bin', WORK / 'lean4export/.lake/build/bin/lean4export',
             WORK / 'rocq-lean-import/src/Lean.vo',
             WORK / 'rocq-lean-import/src/ULiftCumulativeRegistration.vo',
             WORK / 'rocq-lean-import/src/lean_import.cmxs',
             WORK / 'opam/strict-9.3/bin/rocq', WORK / 'opam/strict-9.3/bin/rocqchk']
    paths += sorted((WORK / 'opam/strict-9.3/lib').rglob('*.cmxs'))
    paths += sorted((WORK / 'opam/strict-9.3/lib').rglob('*.so'))
    paths += sorted((WORK / 'sysroot/usr/lib/x86_64-linux-gnu').glob('libgmp.so*'))
    return {str(path.relative_to(WORK)): digest(path) for path in paths}


def collect():
    started = time.monotonic()
    verify_tools()
    names = inventory()
    before = sources()
    tools_before = tool_artifacts()
    for audit in baseline_audits():
        if audit.required_sources() != json.loads(audit.MANIFEST.read_text())['source_sha256']:
            raise ValueError('preceding Lean source/dependency identities differ')
    subprocess.run(['lake', 'build', 'LeanCageM3', 'leancage'], cwd=ROOT / 'm3',
                   check=True, capture_output=True, text=True, timeout=180)
    for directory in ['source', 'proofs', 'modules']:
        (WORK / directory).mkdir(exist_ok=True)
    gate = connection()
    old_manifest = json.loads((ROOT / 'assurance/m4-connection-claims.json').read_text())
    if len(old_manifest['rocq_declarations']) != 1113 or len(old_manifest['lean_declarations']) != 103:
        raise ValueError('bridge requires the reviewed public endpoint baseline')
    evidence = json.loads((ROOT / 'assurance/m4-evidence.json').read_text())
    archived = ROOT / 'assurance/m4-slice.v.gz'
    raw = gzip.decompress(archived.read_bytes())
    import hashlib
    if hashlib.sha256(raw).hexdigest() != evidence['uncompressed_sha256']['assurance/m4-slice.v.gz']:
        raise ValueError('archived Clight AST differs from reviewed source')
    (WORK / 'source/Slice.v').write_bytes(raw)
    replayed_sources = {'Slice.v': digest(WORK / 'source/Slice.v')}
    logs = {}
    for name in ['Slice', 'Codec', *gate.MODULES]:
        path = WORK / 'source' / (name + '.v')
        if name != 'Slice':
            original = ROOT / 'm4/Codec.v' if name == 'Codec' else gate.module_source(name)
            shutil.copyfile(original, path)
        replayed_sources[path.name] = digest(path)
        logs[path.name] = compile_file(path)
    print('Rebuilt exact archived AST, Codec and all 212 preceding proof modules.', flush=True)
    for module, original in [('Public', ROOT / 'm4/connection/Public.lean'), ('Normalized', DIRECTORY / 'Normalized.lean')]:
        path = WORK / 'modules' / (module + '.lean')
        shutil.copyfile(original, path)
        logs[module + '.lean'] = lean_run(['lean', '-R', str(WORK / 'modules'), '-o', str(path.with_suffix('.olean')), str(path)]).stdout
    lean = lean_inventory()
    export = lean_run([str(WORK / 'lean4export/.lake/build/bin/lean4export'), 'Normalized', '--', 'LeanCageM4.Normalized.decode']).stdout
    export_path = WORK / 'normalized-decoder.ndjson'
    export_path.write_text(export)
    exported = export_inventory(export_path)
    for module in ['NormalizedImport', *MODULES]:
        path = WORK / 'proofs' / (module + '.v')
        shutil.copyfile(DIRECTORY / path.name, path)
        logs[module + '.v'] = compile_file(path)
    # A negative trial exercises the compiled plugin, not just patch text.
    negative = WORK / 'proofs/GuardDisabled.v'
    negative.write_text('From LeanImport Require Import Lean.\nUnset Guard Checking.\n'
                        'Set Lean Error Mode "Fail".\nUnset Lean Skip Missing Quotient.\n'
                        'Lean Import "../normalized-decoder.ndjson".\n')
    try:
        compile_file(negative)
    except subprocess.CalledProcessError as error:
        if 'M4 strict bridge requires all kernel typing checks' not in error.stdout:
            raise ValueError('negative import failed for an unexpected reason: ' + error.stdout)
        logs['GuardDisabled.v'] = error.stdout
    else:
        raise ValueError('strict importer accepted disabled guardedness')
    query = ['From LeanImport Require Import Lean.', 'Require Import NormalizedImport ' + ' '.join(MODULES) + '.',
             'Set Printing All.', 'Set Printing Depth 1000000.', 'Set Printing Width 1000000.']
    targets = ['NormalizedImport.LeanCageM4_Normalized_decode', *names]
    for i, name in enumerate(targets):
        query += [f'Redirect "bridge-type-{i}" Check @{name}.',
                  f'Redirect "bridge-axioms-{i}" Print Assumptions {name}.']
    path = WORK / 'proofs/BridgeAudit.v'
    path.write_text('\n'.join(query) + '\n')
    logs[path.name] = compile_file(path)
    records = []
    for i, name in enumerate(targets):
        statement = (WORK / f'proofs/bridge-type-{i}.out').read_text().strip()
        assumptions = (WORK / f'proofs/bridge-axioms-{i}.out').read_text().strip()
        axioms, uip = foundations(assumptions)
        if '...' in statement:
            raise ValueError('truncated bridge theorem statement')
        records.append({'name': name, 'full_type': statement, 'transitive_assumptions': assumptions,
                        'assumption_names': axioms, 'definitional_uip': uip})
    kernel = run(['rocq', 'check', '-silent', *flags(checker=True), 'Slice', 'Codec', *gate.MODULES,
                  'NormalizedImport', *MODULES], cwd=WORK / 'proofs', timeout=300)
    tests = subprocess.run([sys.executable, '-m', 'unittest', 'discover', '-s', 'm4/bridge',
                            '-p', 'test_gate.py', '-v'], cwd=ROOT, text=True,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=True, timeout=30)
    logs['gate_tests'] = tests.stdout
    if sources() != before or tool_artifacts() != tools_before:
        raise ValueError('bridge sources or checker/tool artifacts changed during replay')
    artifacts = {str(path.relative_to(WORK)): digest(path)
                 for directory in ['source', 'proofs', 'modules'] for path in sorted((WORK / directory).glob('*'))
                 if path.suffix in {'.vo', '.olean'} and path.stem not in {'BridgeAudit', 'GuardDisabled'}}
    report = {'schema_version': 1, 'source_sha256': before, 'replayed_sources_sha256': replayed_sources,
              'rocq_declarations': records[1:], 'lean_declarations': lean, 'imported_endpoint': records[0],
              'export_inventory': exported, 'export_sha256': digest(export_path),
              'artifact_sha256': artifacts, 'tool_artifact_sha256': tools_before,
              'kernel_output': kernel.stdout, 'logs': logs,
              'elapsed_seconds': round(time.monotonic() - started, 3)}
    (WORK / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f"Bridge replay: {len(records)-1} Rocq and {len(lean)} Lean theorem records; strict import and kernel replay passed.", flush=True)
    return report


def check():
    expected = json.loads(MANIFEST.read_text())
    evidence = json.loads(EVIDENCE.read_text())
    report = collect()
    validate_claims(expected, report)
    for key in ['source_sha256', 'replayed_sources_sha256', 'artifact_sha256', 'tool_artifact_sha256', 'export_sha256']:
        if report[key] != evidence[key]:
            raise ValueError('reviewed bridge identity differs: ' + key)
    if evidence['claims_sha256'] != digest(MANIFEST) or evidence['full_bridge_complete'] is not False:
        raise ValueError('stale manifest or unsupported full bridge claim')
    connection().verify_hashes(evidence['archived_receipts_sha256'])
    exported = gzip.decompress((ROOT / 'assurance/m4-bridge-export.ndjson.gz').read_bytes())
    import hashlib
    if hashlib.sha256(exported).hexdigest() != report['export_sha256']:
        raise ValueError('archived exported term closure differs from the actual export')
    connection().validate_obligations(json.loads((ROOT / 'assurance/m4-obligations.json').read_text()))
    print('Primitive source/imported-reader correspondence checked; translation review, full-frame and Linux/executable composition remain OPEN.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--collect', action='store_true', help='write an ignored candidate report; never update reviewed expectations')
    args = parser.parse_args()
    try:
        collect() if args.collect else check()
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        print('Bridge replay failed: ' + str(error), file=sys.stderr)
        if isinstance(error, subprocess.CalledProcessError):
            print(error.stdout, file=sys.stderr)
        sys.exit(1)
